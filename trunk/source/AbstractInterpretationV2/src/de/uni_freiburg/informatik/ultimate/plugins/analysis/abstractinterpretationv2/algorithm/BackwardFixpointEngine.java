/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class BackwardFixpointEngine<STATE extends IAbstractState<STATE>, ACTION, VARDECL, LOC>
		implements IFixpointEngine<STATE, ACTION, VARDECL, LOC> {

	private final int mMaxUnwindings;
	private final int mMaxParallelStates;

	private final ITransitionProvider<ACTION, LOC> mTransitionProvider;
	private final IAbstractStateStorage<STATE, ACTION, LOC> mStateStorage;
	private final IAbstractDomain<STATE, ACTION> mDomain;
	private final IVariableProvider<STATE, ACTION> mVarProvider;
	private final ILoopDetector<ACTION> mLoopDetector;
	private final IDebugHelper<STATE, ACTION, VARDECL, LOC> mDebugHelper;
	private final IProgressAwareTimer mTimer;
	private final ILogger mLogger;

	private AbsIntResult<STATE, ACTION, LOC> mResult;
	private final SummaryMap<STATE, ACTION, LOC> mSummaryMap;

	public BackwardFixpointEngine(final FixpointEngineParameters<STATE, ACTION, VARDECL, LOC> params) {
		if (params == null || !params.isValid()) {
			throw new IllegalArgumentException("invalid params");
		}
		mTimer = params.getTimer();
		mLogger = params.getLogger();
		mTransitionProvider = params.getTransitionProvider();
		mStateStorage = params.getStorage();
		mDomain = params.getAbstractDomain();
		mVarProvider = params.getVariableProvider();
		mLoopDetector = params.getLoopDetector();
		mDebugHelper = params.getDebugHelper();
		mMaxUnwindings = params.getMaxUnwindings();
		mMaxParallelStates = params.getMaxParallelStates();
		mSummaryMap = new SummaryMap<>(mTransitionProvider, mLogger);
	}

	@Override
	public AbsIntResult<STATE, ACTION, LOC> run(final Collection<? extends LOC> start, final Script script) {
		mLogger.info("Starting fixpoint engine with domain " + mDomain.getClass().getSimpleName() + " (maxUnwinding="
				+ mMaxUnwindings + ", maxParallelStates=" + mMaxParallelStates + ")");
		mResult = new AbsIntResult<>(script, mDomain, mTransitionProvider, mVarProvider);
		mDomain.beforeFixpointComputation();
		calculateFixpoint(start);
		mResult.saveRootStorage(mStateStorage);
		mResult.saveSummaryStorage(mSummaryMap);
		mDomain.afterFixpointComputation(mResult);
		return mResult;
	}

	private void calculateFixpoint(final Collection<? extends LOC> sinks) {
		final Deque<BackwardsWorklistItem<STATE, ACTION, VARDECL, LOC>> worklist = new ArrayDeque<>();
		final IAbstractTransformer<STATE, ACTION> preOp = mDomain.getPreOperator();
		final IAbstractStateBinaryOperator<STATE> wideningOp = mDomain.getWideningOperator();

		// add all incoming edges of the sinks that are not unnecessary summaries to the worklist
		sinks.stream().flatMap(a -> mTransitionProvider.getPredecessorActions(a).stream())
				.filter(a -> !mTransitionProvider.isSummaryWithImplementation(a)).map(this::createInitialWorklistItem)
				.forEach(worklist::add);

		while (!worklist.isEmpty()) {
			checkTimeout();

			final BackwardsWorklistItem<STATE, ACTION, VARDECL, LOC> currentItem = worklist.removeFirst();
			mResult.getBenchmark().addIteration(currentItem.getAction());

			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageCurrentTransition(currentItem));
			}

			final DisjunctiveAbstractState<STATE> preState = calculateAbstractPre(currentItem, preOp);

			if (isUnnecessaryPreState(currentItem, preState)) {
				continue;
			}

			checkLoopState(currentItem);

			final DisjunctiveAbstractState<STATE> preStateAfterWidening =
					widenIfNecessary(currentItem, preState, wideningOp);
			if (preStateAfterWidening == null) {
				// we have reached a fixpoint
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(AbsIntPrefInitializer.INDENT
							+ " Skipping successors because post state is already contained");
				}
				continue;
			}
			logDebugPostChanged(preState, preStateAfterWidening, "Widening");
			final DisjunctiveAbstractState<STATE> preStateAfterSave = savePreState(currentItem, preStateAfterWidening);
			assert preStateAfterSave != null : "Saving a state is not allowed to return null";
			logDebugPostChanged(preStateAfterWidening, preStateAfterSave, "Merge");

			final List<BackwardsWorklistItem<STATE, ACTION, VARDECL, LOC>> newItems =
					createPredecessorItems(currentItem, preStateAfterSave);
			worklist.addAll(newItems);
		}
	}

	private DisjunctiveAbstractState<STATE> calculateAbstractPre(
			final BackwardsWorklistItem<STATE, ACTION, VARDECL, LOC> currentItem,
			final IAbstractTransformer<STATE, ACTION> preOp) {

		final DisjunctiveAbstractState<STATE> postState = currentItem.getState();
		final ACTION currentAction = currentItem.getAction();

		DisjunctiveAbstractState<STATE> preState = postState.apply(preOp, currentAction);

		// assert mTransitionProvider.isSummaryWithImplementation(currentAction) || mDebugHelper.isPostSound(postState,
		// preStateWithFreshVariables, blaState, currentAction) : getLogMessageUnsoundPost(postState,
		// preStateWithFreshVariables, blaState, currentAction);

		// check if we enter or leave a scope and act accordingly (saving summaries, creating new scope storages, etc.)
		preState = prepareScope(currentItem, preState);

		return preState;
	}

	/**
	 * Check whether a pending post state is bottom or already subsumed by the current fixpoint.
	 *
	 * @param currentItem
	 *            The worklist item for which we calculate a post state.
	 * @param pendingPreState
	 *            The post state as computed by the abstract post.
	 * @return true if the pendingPostState is either false or already subsumed by an existing state (i.e., a fixpoint),
	 *         and false otherwise.
	 */
	private boolean isUnnecessaryPreState(final BackwardsWorklistItem<STATE, ACTION, VARDECL, LOC> currentItem,
			final DisjunctiveAbstractState<STATE> pendingPreState) {
		if (pendingPreState.isBottom()) {
			// if the new abstract state is bottom, we do not enter loops and we do not add
			// new actions to the worklist
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessagePreIsBottom(pendingPreState));
			}
			return true;
		}

		final IAbstractStateStorage<STATE, ACTION, LOC> currentStateStorage = currentItem.getCurrentStorage();

		// check if the pending post state is already subsumed by a pre-existing state and if this is not a return
		if (checkSubset(currentStateStorage, currentItem.getAction(), pendingPreState)) {
			// it is subsumed, we can skip all successors safely
			return true;
		}

		return false;
	}

	private void checkLoopState(final BackwardsWorklistItem<STATE, ACTION, VARDECL, LOC> currentItem) {
		final ACTION currentAction = currentItem.getAction();
		// check if we are entering a loop
		if (mLoopDetector.isEnteringLoop(currentAction)) {
			final LOC currentLoopHead = mTransitionProvider.getSource(currentAction);
			final int loopCounterValue = currentItem.enterLoop(currentLoopHead);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageEnterLoop(loopCounterValue, currentLoopHead, currentItem.getState()));
			}
		}
	}

	private DisjunctiveAbstractState<STATE> savePreState(
			final BackwardsWorklistItem<STATE, ACTION, VARDECL, LOC> currentItem,
			final DisjunctiveAbstractState<STATE> preState) {
		final IAbstractStateStorage<STATE, ACTION, LOC> currentStorage = currentItem.getCurrentStorage();
		final ACTION currentAction = currentItem.getAction();

		if (mLogger.isDebugEnabled()) {
			mLogger.debug(getLogMessageNewState(preState));
		}

		final LOC source = mTransitionProvider.getSource(currentAction);
		return currentStorage.addAbstractState(source, preState);
	}

	private BackwardsWorklistItem<STATE, ACTION, VARDECL, LOC> createInitialWorklistItem(final ACTION elem) {
		final DisjunctiveAbstractState<STATE> preMultiState = createFreshPrestateWithVariables(elem);
		return new BackwardsWorklistItem<>(preMultiState, elem, mStateStorage, mSummaryMap);
	}

	private DisjunctiveAbstractState<STATE> createFreshPrestateWithVariables(final ACTION elem) {
		final STATE preState = mVarProvider.defineInitialVariables(elem, mDomain.createTopState());
		final DisjunctiveAbstractState<STATE> preMultiState =
				new DisjunctiveAbstractState<>(mMaxParallelStates, preState);
		return preMultiState;
	}

	private List<BackwardsWorklistItem<STATE, ACTION, VARDECL, LOC>> createPredecessorItems(
			final BackwardsWorklistItem<STATE, ACTION, VARDECL, LOC> currentItem,
			final DisjunctiveAbstractState<STATE> preState) {
		final ACTION current = currentItem.getAction();
		final Collection<ACTION> predecessors =
				mTransitionProvider.getPredecessors(current, currentItem.getCurrentScope());

		if (predecessors.isEmpty()) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" No predecessors"));
			}
			return Collections.emptyList();
		}

		final List<BackwardsWorklistItem<STATE, ACTION, VARDECL, LOC>> predecessorItems = predecessors.stream()
				.filter(a -> !mTransitionProvider.isSummaryWithImplementation(a))
				.map(succ -> new BackwardsWorklistItem<>(preState, succ, currentItem)).collect(Collectors.toList());

		if (mLogger.isDebugEnabled()) {
			predecessorItems.stream().map(this::getLogMessageAddTransition).forEach(mLogger::debug);
		}

		return predecessorItems;
	}

	private DisjunctiveAbstractState<STATE> widenIfNecessary(
			final BackwardsWorklistItem<STATE, ACTION, VARDECL, LOC> currentItem,
			final DisjunctiveAbstractState<STATE> preState, final IAbstractStateBinaryOperator<STATE> wideningOp) {

		final ACTION currentAction = currentItem.getAction();

		// check if we should widen at this location before adding new successors
		// we should widen if the current item is a transition to a loop head
		// or if a successor transition enters a scope
		final LOC source = mTransitionProvider.getSource(currentAction);
		final Pair<Integer, DisjunctiveAbstractState<STATE>> loopPair = currentItem.getLoopPair(source);
		final DisjunctiveAbstractState<STATE> oldState;
		boolean scopeWidening = false;
		if (loopPair != null && loopPair.getFirst() > mMaxUnwindings) {
			oldState = loopPair.getSecond();
		} else if (mTransitionProvider.isLeavingScope(currentAction)) {
			oldState = getWidenStateAtScopeEntry(currentItem);
			scopeWidening = true;
		} else {
			oldState = null;
		}

		if (oldState == null) {
			// no widening necessary
			return preState;
		}

		// we widen with the oldState and all postStates and keep the states that are not fixpoints
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(AbsIntPrefInitializer.DINDENT + "Applying widening op:");
			mLogger.debug(AbsIntPrefInitializer.DINDENT + "Op1: " + LoggingHelper.getStateString(oldState));
			mLogger.debug(AbsIntPrefInitializer.DINDENT + "Op2: " + LoggingHelper.getStateString(preState));
		}
		final DisjunctiveAbstractState<STATE> preStateAfterWidening = oldState.widen(wideningOp, preState);
		if (isFixpoint(oldState, preStateAfterWidening)) {
			if (scopeWidening) {
				// if we found a fixpoint during scope widening, it means that we will not continue into this scope but
				// rather subsume all calls to this scope by the current one
				currentItem.getCurrentStorage().scopeFixpointReached();
			}
			return null;
		}
		return preStateAfterWidening;
	}

	/**
	 * Check if we are entering or leaving a scope and if so, create or delete it.
	 *
	 * @param preState
	 */
	private DisjunctiveAbstractState<STATE> prepareScope(
			final BackwardsWorklistItem<STATE, ACTION, VARDECL, LOC> currentItem,
			final DisjunctiveAbstractState<STATE> preState) {
		final ACTION action = currentItem.getAction();

		if (mTransitionProvider.isEnteringScope(action, currentItem.getCurrentScope())) {
			final ACTION oldScope = currentItem.removeCurrentScope(currentItem.getState());
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageLeaveScope(oldScope, currentItem));
			}
			return preState;
		} else if (mTransitionProvider.isLeavingScope(action)) {
			currentItem.addScope(action, preState);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageEnterScope(currentItem));
			}
			return preState;
		} else {
			return preState;
		}
	}

	private DisjunctiveAbstractState<STATE>
			getWidenStateAtScopeEntry(final BackwardsWorklistItem<STATE, ACTION, VARDECL, LOC> currentItem) {
		final ACTION currentAction = currentItem.getAction();

		final Deque<Pair<ACTION, DisjunctiveAbstractState<STATE>>> scopeStack = currentItem.getScopeWideningStack();
		// count all stack items that are there more than once and the current item
		final Optional<Long> count = scopeStack.stream().map(a -> a.getFirst()).filter(a -> a != null)
				.collect(Collectors.groupingBy(a -> a, Collectors.counting())).entrySet().stream()
				.filter(e -> e.getValue() > 1 || e.getKey() == currentAction).map(e -> e.getValue())
				.reduce((a, b) -> a + b);
		if (!count.isPresent() || count.get() <= mMaxUnwindings) {
			// if the stack is too small, we do not need to widen
			return null;
		}

		if (mLogger.isDebugEnabled()) {
			mLogger.debug(AbsIntPrefInitializer.DINDENT + " Scope widening sequence for "
					+ LoggingHelper.getTransitionString(currentAction, mTransitionProvider) + " (MaxUnwindings="
					+ mMaxUnwindings + ")");
			mLogger.debug(AbsIntPrefInitializer.DINDENT + " Stack");
			scopeStack.stream().sequential().map(a1 -> a1.getFirst())
					.map(a2 -> a2 == null ? "[G]" : LoggingHelper.getTransitionString(a2, mTransitionProvider))
					.map(a3 -> AbsIntPrefInitializer.TINDENT + a3).forEach(mLogger::debug);
		}

		final List<Pair<ACTION, DisjunctiveAbstractState<STATE>>> relevantStackItems = scopeStack.stream().sequential()
				.filter(a -> a.getFirst() == currentAction).collect(Collectors.toList());
		if (relevantStackItems.isEmpty()) {
			// there is no relevant sequence
			return null;
		}

		if (mLogger.isDebugEnabled()) {
			mLogger.debug(AbsIntPrefInitializer.DINDENT + "Relevant stack states");
			relevantStackItems.stream().sequential()
					.map(a -> AbsIntPrefInitializer.TINDENT
							+ (a.getFirst() == null ? "[G]" : LoggingHelper.getHashCodeString(a.getFirst())) + " "
							+ LoggingHelper.getHashCodeString(a.getSecond()) + " " + a.getSecond().toString())
					.forEach(mLogger::debug);
		}

		// select the last state
		final int relevantStackSize = relevantStackItems.size();
		// we need the state before the current state as last state
		final int idx = relevantStackSize - 2;
		if (relevantStackSize - mMaxUnwindings < 0 || idx < 0) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(AbsIntPrefInitializer.DINDENT + "not enough states to widen");
			}
			return null;
		}
		final DisjunctiveAbstractState<STATE> lastState = relevantStackItems.get(idx).getSecond();

		if (mLogger.isDebugEnabled()) {
			mLogger.debug(AbsIntPrefInitializer.DINDENT + "Selected " + LoggingHelper.getHashCodeString(lastState));
		}
		return lastState;
	}

	private boolean isFixpoint(final DisjunctiveAbstractState<STATE> oldState,
			final DisjunctiveAbstractState<STATE> newState) {
		if (oldState.isEqualTo(newState)) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageFixpointFound(oldState, newState));
			}
			mResult.getBenchmark().addFixpoint();
			return true;
		}
		return false;
	}

	private boolean checkSubset(final IAbstractStateStorage<STATE, ACTION, LOC> currentStateStorage,
			final ACTION currentAction, final DisjunctiveAbstractState<STATE> pendingPreState) {
		final LOC source = mTransitionProvider.getSource(currentAction);
		final DisjunctiveAbstractState<STATE> oldPreState = currentStateStorage.getAbstractState(source);
		if (pendingPreState == oldPreState || pendingPreState.isSubsetOf(oldPreState) != SubsetResult.NONE) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessagePostIsSubsumed(pendingPreState, oldPreState));
			}
			return true;
		}
		return false;
	}

	private void checkTimeout() {
		if (!mTimer.continueProcessing()) {
			mLogger.warn("Received timeout, aborting fixpoint engine");
			throw new ToolchainCanceledException(getClass(), "executing abstract interpretation");
		}
	}

	private void logDebugPostChanged(final DisjunctiveAbstractState<STATE> postState,
			final DisjunctiveAbstractState<STATE> postStateAfterChange, final String reason) {
		if (!mLogger.isDebugEnabled()) {
			return;
		}
		if (postState == postStateAfterChange) {
			return;
		}
		final String prefix = AbsIntPrefInitializer.INDENT + AbsIntPrefInitializer.INDENT;
		mLogger.debug(prefix + reason);
		mLogger.debug(prefix + "Before: " + LoggingHelper.getStateString(postState));
		mLogger.debug(prefix + "After: " + LoggingHelper.getStateString(postStateAfterChange));
	}

	private String getLogMessageUnsoundPost(final DisjunctiveAbstractState<STATE> preState,
			final DisjunctiveAbstractState<STATE> preStateWithFreshVariables,
			final DisjunctiveAbstractState<STATE> postState, final ACTION currentAction) {
		final StringBuilder sb = new StringBuilder();
		sb.append("Post is unsound because the term-transformation of the following triple is not valid: {");
		sb.append(preState.toLogString());
		sb.append("} ");
		if (preState != preStateWithFreshVariables) {
			sb.append("{");
			sb.append(preStateWithFreshVariables.toLogString());
			sb.append("} ");
		}
		sb.append(mTransitionProvider.toLogString(currentAction));
		sb.append(" {");
		if (postState != null) {
			sb.append(postState.toLogString());
		}
		sb.append("}");
		return sb.toString();
	}

	private StringBuilder getLogMessagePreIsBottom(final DisjunctiveAbstractState<STATE> pendingNewPostState) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT)
				.append(" Skipping all successors because pre state [").append(pendingNewPostState.hashCode())
				.append("] is bottom");
	}

	private StringBuilder getLogMessagePostIsSubsumed(final DisjunctiveAbstractState<STATE> subState,
			final DisjunctiveAbstractState<STATE> superState) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT)
				.append(" Skipping all successors because post state ").append(LoggingHelper.getStateString(subState))
				.append(" is subsumed by pre-existing state ").append(LoggingHelper.getStateString(superState));
	}

	private StringBuilder getLogMessageLeaveScope(final ACTION oldScope,
			final BackwardsWorklistItem<STATE, ACTION, VARDECL, LOC> currentItem) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Transition [")
				.append(currentItem.getAction().hashCode()).append("] leaves scope ")
				.append(LoggingHelper.getHashCodeString(oldScope)).append(" (new depth=")
				.append(currentItem.getScopeStackDepth()).append("): ")
				.append(LoggingHelper.getScopeStackString(currentItem.getScopeStack()));
	}

	private StringBuilder
			getLogMessageEnterScope(final BackwardsWorklistItem<STATE, ACTION, VARDECL, LOC> currentItem) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Transition [")
				.append(currentItem.getAction().hashCode()).append("] enters scope (new depth=")
				.append(currentItem.getScopeStackDepth()).append("): ")
				.append(LoggingHelper.getScopeStackString(currentItem.getScopeStack()));

	}

	private StringBuilder getLogMessageFixpointFound(final DisjunctiveAbstractState<STATE> oldPostState,
			final DisjunctiveAbstractState<STATE> newPostState) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" State [")
				.append(oldPostState.hashCode()).append("] ").append(oldPostState.toLogString())
				.append(" is equal to [").append(newPostState.hashCode()).append("]");
	}

	private StringBuilder getLogMessageNewState(final DisjunctiveAbstractState<STATE> newPostState) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Adding pre state [")
				.append(newPostState.hashCode()).append("] ").append(newPostState.toLogString());
	}

	private StringBuilder getLogMessageEnterLoop(final int loopCounterValue, final LOC loopHead,
			final DisjunctiveAbstractState<STATE> state) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Entering loop ").append(loopHead)
				.append(" (").append(loopCounterValue).append("), saving ").append(LoggingHelper.getStateString(state));
	}

	private StringBuilder
			getLogMessageCurrentTransition(final BackwardsWorklistItem<STATE, ACTION, VARDECL, LOC> currentItem) {
		final DisjunctiveAbstractState<STATE> preState = currentItem.getState();
		final ACTION current = currentItem.getAction();
		final int depth = currentItem.getScopeStackDepth();
		final String preStateString = preState == null ? "NULL" : LoggingHelper.getStateString(preState).toString();
		return LoggingHelper.getTransitionString(current, mTransitionProvider).append(" processing for pre state ")
				.append(preStateString).append(" (depth=").append(depth).append(")");
	}

	private StringBuilder getLogMessageAddTransition(final BackwardsWorklistItem<STATE, ACTION, VARDECL, LOC> item) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Adding [")
				.append(item.getState().hashCode()).append("]").append(" --[").append(item.getAction().hashCode())
				.append("]->");
	}
}
