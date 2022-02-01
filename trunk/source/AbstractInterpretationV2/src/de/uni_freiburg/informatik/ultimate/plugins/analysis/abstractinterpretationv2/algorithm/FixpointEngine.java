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
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class FixpointEngine<STATE extends IAbstractState<STATE>, ACTION, VARDECL, LOC>
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
	private final boolean mUseHierachicalPre;

	public FixpointEngine(final FixpointEngineParameters<STATE, ACTION, VARDECL, LOC> params) {
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
		mUseHierachicalPre = mDomain.useHierachicalPre();
	}

	@Override
	public AbsIntResult<STATE, ACTION, LOC> run(final Collection<? extends LOC> initialNodes, final Script script) {
		mLogger.info("Starting fixpoint engine with domain " + mDomain.getClass().getSimpleName() + " (maxUnwinding="
				+ mMaxUnwindings + ", maxParallelStates=" + mMaxParallelStates + ")");
		mResult = new AbsIntResult<>(script, mDomain, mTransitionProvider, mVarProvider);
		mDomain.beforeFixpointComputation(mResult.getBenchmark());
		calculateFixpoint(initialNodes);
		mResult.saveRootStorage(mStateStorage);
		mResult.saveSummaryStorage(mSummaryMap);
		mLogger.debug("Fixpoint computation completed");
		mDomain.afterFixpointComputation(mResult);
		return mResult;
	}

	private void calculateFixpoint(final Collection<? extends LOC> start) {
		final Deque<WorklistItem<STATE, ACTION, VARDECL, LOC>> worklist = new ArrayDeque<>();
		final IAbstractPostOperator<STATE, ACTION> postOp = mDomain.getPostOperator();
		final IAbstractStateBinaryOperator<STATE> wideningOp = mDomain.getWideningOperator();
		final Set<ACTION> reachedErrors = new HashSet<>();

		// add all outgoing edges of nodes in the start set that are not unnecessary summaries to the worklist
		start.stream().flatMap(a -> mTransitionProvider.getSuccessorActions(a).stream())
				.filter(a -> !mTransitionProvider.isSummaryWithImplementation(a)).map(this::createInitialWorklistItem)
				.forEach(worklist::add);

		while (!worklist.isEmpty()) {
			checkTimeout();

			final WorklistItem<STATE, ACTION, VARDECL, LOC> currentItem = worklist.removeFirst();
			mResult.getBenchmark().addIteration(currentItem.getAction());

			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageCurrentTransition(currentItem));
			}

			final DisjunctiveAbstractState<STATE> postState = calculateAbstractPost(currentItem, postOp);

			if (isUnnecessaryPostState(currentItem, postState)) {
				continue;
			}

			// TODO: Fix summary calculation
			// if (useSummaryInstead(currentItem, postState, worklist)) {
			// continue;
			// }

			checkLoopState(currentItem);
			checkReachedError(currentItem, postState, reachedErrors);

			final DisjunctiveAbstractState<STATE> postStateAfterWidening =
					widenIfNecessary(currentItem, postState, wideningOp);
			if (postStateAfterWidening == null) {
				// we have reached a fixpoint
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(AbsIntPrefInitializer.INDENT
							+ " Skipping successors because post state is already contained");
				}
				continue;
			}
			logDebugPostChanged(postState, postStateAfterWidening, "Widening");
			final DisjunctiveAbstractState<STATE> postStatesAfterSave =
					savePostState(currentItem, postStateAfterWidening);
			assert postStatesAfterSave != null : "Saving a state is not allowed to return null";
			logDebugPostChanged(postStateAfterWidening, postStatesAfterSave, "Merge");

			final List<WorklistItem<STATE, ACTION, VARDECL, LOC>> newItems =
					createSuccessorItems(currentItem, postStatesAfterSave);
			worklist.addAll(newItems);
		}
	}

	/**
	 * This method checks whether the current item can be ignored by a summary. This is the case if this item is a call
	 * to a procedure for which a summary is already calculated. In this case, the item will count as processed and
	 * instead a new item will be added to the worklist.
	 *
	 * @param currentItem
	 * @param postState
	 * @param worklist
	 * @return true if a summary item was added to the worklist and this item should be ignored.
	 */
	private boolean useSummaryInstead(final WorklistItem<STATE, ACTION, VARDECL, LOC> currentItem,
			final DisjunctiveAbstractState<STATE> postState,
			final Deque<WorklistItem<STATE, ACTION, VARDECL, LOC>> worklist) {
		final ACTION callAction = currentItem.getAction();
		if (!mTransitionProvider.isEnteringScope(callAction)) {
			// can only use summary if entering a scope
			return false;
		}
		final ACTION summaryAction = mTransitionProvider.getSummaryForCall(callAction);

		final DisjunctiveAbstractState<STATE> summaryPostState =
				currentItem.getSummaryPostState(summaryAction, postState);
		if (summaryPostState == null) {
			// we do not have a usable summary for this call, we have to use it as-it
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(AbsIntPrefInitializer.INDENT + " No summary available for "
						+ LoggingHelper.getTransitionString(callAction, mTransitionProvider));
			}
			return false;
		}

		if (summaryPostState.isBottom()) {
			// skip this item without adding a new one if the summary is already bottom
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(AbsIntPrefInitializer.INDENT + " The summary for "
						+ LoggingHelper.getTransitionString(callAction, mTransitionProvider) + " is bottom");
			}
			return true;
		}

		// we have a usable summary for this call
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(AbsIntPrefInitializer.INDENT + " Using summary for "
					+ LoggingHelper.getTransitionString(callAction, mTransitionProvider));
			mLogger.debug(AbsIntPrefInitializer.DINDENT + " Using " + LoggingHelper.getStateString(summaryPostState));
			mLogger.debug(AbsIntPrefInitializer.DINDENT + " Instead of " + LoggingHelper.getStateString(postState));
		}
		final WorklistItem<STATE, ACTION, VARDECL, LOC> newItem =
				currentItem.createSummarySubstitution(summaryPostState, summaryAction);
		worklist.add(newItem);
		return true;
	}

	private DisjunctiveAbstractState<STATE> calculateAbstractPost(
			final WorklistItem<STATE, ACTION, VARDECL, LOC> currentItem,
			final IAbstractPostOperator<STATE, ACTION> postOp) {

		final DisjunctiveAbstractState<STATE> preState = currentItem.getState();
		final DisjunctiveAbstractState<STATE> hierachicalPreState = currentItem.getHierachicalState();
		final ACTION currentAction = currentItem.getAction();

		// calculate the (abstract) effect of the current action
		DisjunctiveAbstractState<STATE> postState;
		final DisjunctiveAbstractState<STATE> preStateWithFreshVariables;
		if (mTransitionProvider.isEnteringScope(currentAction) || mTransitionProvider.isLeavingScope(currentAction)) {
			// if we enter or leave a scope, we first declare variables in the prestate
			preStateWithFreshVariables =
					preState.defineVariablesAfter(mVarProvider, currentAction, hierachicalPreState);
			mResult.getBenchmark().addMaxVariables(preStateWithFreshVariables.getVariables().size());

			if (mUseHierachicalPre && mTransitionProvider.isLeavingScope(currentAction)) {
				postState = hierachicalPreState.apply(postOp, preState, currentAction);
			} else {
				postState = preStateWithFreshVariables.apply(postOp, preState, currentAction);
			}
			isHierachicalPostResultBottom(postState, currentItem);

		} else {
			preStateWithFreshVariables = preState;
			postState = preState.apply(postOp, currentAction);
		}
		mResult.getBenchmark().countPostApplication();

		assert postState != null;
		assert assertIsPostSound(preState, currentAction, preStateWithFreshVariables, hierachicalPreState,
				postState) : "Post is unsound";

		// check if we enter or leave a scope and act accordingly (saving summaries, creating new scope storages, etc.)
		postState = prepareScope(currentItem, postState);
		assert postState != null;
		return postState;
	}

	private boolean assertIsPostSound(final DisjunctiveAbstractState<STATE> preState, final ACTION currentAction,
			final DisjunctiveAbstractState<STATE> preStateWithFreshVariables,
			final DisjunctiveAbstractState<STATE> hierachicalPreState,
			final DisjunctiveAbstractState<STATE> postState) {
		final boolean rtr = mTransitionProvider.isSummaryWithImplementation(currentAction)
				|| mDebugHelper.isPostSound(preState, hierachicalPreState, postState, currentAction);
		if (rtr) {
			return true;
		}
		mLogger.fatal("Post is unsound because the term-transformation of the following triple is not valid: ");
		mLogger.fatal("PreBL : " + preState.toLogString());
		mLogger.fatal("PreH  : " + hierachicalPreState.toLogString());
		if (preState != preStateWithFreshVariables) {
			mLogger.fatal("PreAL : " + preStateWithFreshVariables.toLogString());
		}
		mLogger.fatal("Action: " + mTransitionProvider.toLogString(currentAction) + " (to "
				+ mTransitionProvider.getProcedureName(currentAction) + ")");

		if (postState != null) {
			mLogger.fatal("Post  :  " + postState.toLogString());
		}
		return false;
	}

	/**
	 * Check whether a pending post state is bottom or already subsumed by the current fixpoint.
	 *
	 * @param currentItem
	 *            The worklist item for which we calculate a post state.
	 * @param pendingPostState
	 *            The post state as computed by the abstract post.
	 * @return true if the pendingPostState is either false or already subsumed by an existing state (i.e., a fixpoint),
	 *         and false otherwise.
	 */
	private boolean isUnnecessaryPostState(final WorklistItem<STATE, ACTION, VARDECL, LOC> currentItem,
			final DisjunctiveAbstractState<STATE> pendingPostState) {
		if (pendingPostState.isBottom()) {
			// if the new abstract state is bottom, we do not enter loops and we do not add
			// new actions to the worklist
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessagePostIsBottom(pendingPostState));
			}
			return true;
		}

		final IAbstractStateStorage<STATE, ACTION, LOC> currentStateStorage = currentItem.getCurrentStorage();

		// check if the pending post state is already subsumed by a pre-existing state and if this is not a return
		if (checkSubset(currentStateStorage, currentItem.getAction(), pendingPostState)) {
			// it is subsumed, we can skip all successors safely
			mResult.getBenchmark().addFixpoint();
			return true;
		}

		return false;
	}

	private boolean isHierachicalPostResultBottom(final DisjunctiveAbstractState<STATE> postState,
			final WorklistItem<?, ?, ?, ?> currentItem) {
		if (postState.isBottom()) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("Predecessor sequence of current worklist item: " + CoreUtil.getPlatformLineSeparator()
						+ LoggingHelper.getPrecedessorSequence(currentItem));
			}
			return false;
		}
		return true;
	}

	private void checkLoopState(final WorklistItem<STATE, ACTION, VARDECL, LOC> currentItem) {
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

	private DisjunctiveAbstractState<STATE> savePostState(final WorklistItem<STATE, ACTION, VARDECL, LOC> currentItem,
			final DisjunctiveAbstractState<STATE> postState) {
		final IAbstractStateStorage<STATE, ACTION, LOC> currentStorage = currentItem.getCurrentStorage();
		final ACTION currentAction = currentItem.getAction();
		final LOC target = mTransitionProvider.getTarget(currentAction);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(getLogMessageNewPostState(postState));
		}
		final DisjunctiveAbstractState<STATE> rtrState = currentStorage.addAbstractState(target, postState);
		if (rtrState != postState) {
			mResult.getBenchmark().addMerge();
		}
		return rtrState;
	}

	private void checkReachedError(final WorklistItem<STATE, ACTION, VARDECL, LOC> currentItem,
			final DisjunctiveAbstractState<STATE> postState, final Set<ACTION> reachedErrors) {
		final ACTION currentAction = currentItem.getAction();
		final LOC postLoc = mTransitionProvider.getTarget(currentAction);
		if (!mTransitionProvider.isErrorLocation(postLoc) || postState.isBottom()
				|| !reachedErrors.add(currentAction)) {
			// no new error reached
			return;
		}
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Error state reached"));
		}

		mResult.reachedError(mTransitionProvider, currentItem, postState);
	}

	private WorklistItem<STATE, ACTION, VARDECL, LOC> createInitialWorklistItem(final ACTION elem) {
		final STATE preState = mVarProvider.defineInitialVariables(elem, mDomain.createTopState());
		assert preState != null;
		final DisjunctiveAbstractState<STATE> preMultiState =
				new DisjunctiveAbstractState<>(mMaxParallelStates, preState);
		return new WorklistItem<>(preMultiState, elem, mStateStorage, mSummaryMap);
	}

	private List<WorklistItem<STATE, ACTION, VARDECL, LOC>> createSuccessorItems(
			final WorklistItem<STATE, ACTION, VARDECL, LOC> currentItem,
			final DisjunctiveAbstractState<STATE> postState) {
		final ACTION current = currentItem.getAction();
		final Collection<ACTION> successors = mTransitionProvider.getSuccessors(current, currentItem.getCurrentScope());

		if (successors.isEmpty()) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" No successors"));
			}
			return Collections.emptyList();
		}

		final List<WorklistItem<STATE, ACTION, VARDECL, LOC>> successorItems =
				successors.stream().filter(a -> !mTransitionProvider.isSummaryWithImplementation(a))
						.map(succ -> new WorklistItem<>(postState, succ, currentItem)).collect(Collectors.toList());

		if (mLogger.isDebugEnabled()) {
			for (final WorklistItem<STATE, ACTION, VARDECL, LOC> succItem : successorItems) {
				mLogger.debug(getLogMessageAddTransition(succItem));
			}
		}

		return successorItems;
	}

	private DisjunctiveAbstractState<STATE> widenIfNecessary(
			final WorklistItem<STATE, ACTION, VARDECL, LOC> currentItem,
			final DisjunctiveAbstractState<STATE> postState, final IAbstractStateBinaryOperator<STATE> wideningOp) {

		final ACTION currentAction = currentItem.getAction();

		// check if we should widen at this location before adding new successors
		// we should widen if the current item is a transition to a loop head
		// or if a successor transition enters a scope
		final LOC target = mTransitionProvider.getTarget(currentAction);
		final Pair<Integer, DisjunctiveAbstractState<STATE>> loopPair = currentItem.getLoopPair(target);
		final DisjunctiveAbstractState<STATE> oldState;
		boolean scopeWidening = false;
		if (loopPair != null && loopPair.getFirst() > mMaxUnwindings) {
			oldState = loopPair.getSecond();
		} else if (mTransitionProvider.isEnteringScope(currentAction)) {
			oldState = getWidenStateAtScopeEntry(currentItem);
			scopeWidening = true;
		} else {
			oldState = null;
		}

		if (oldState == null) {
			// no widening necessary
			return postState;
		}

		// we widen with the oldState and all postStates and keep the states that are not fixpoints
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(AbsIntPrefInitializer.DINDENT + "Applying widening op:");
			mLogger.debug(AbsIntPrefInitializer.DINDENT + "Op1: " + LoggingHelper.getStateString(oldState));
			mLogger.debug(AbsIntPrefInitializer.DINDENT + "Op2: " + LoggingHelper.getStateString(postState));
		}
		final DisjunctiveAbstractState<STATE> postStateAfterWidening = oldState.widen(wideningOp, postState);
		if (isFixpoint(oldState, postStateAfterWidening)) {
			if (scopeWidening) {
				// if we found a fixpoint during scope widening, it means that we will not continue into this scope but
				// rather subsume all calls to this scope by the current one
				currentItem.getCurrentStorage().scopeFixpointReached();
			}
			return null;
		}
		mResult.getBenchmark().addWiden();
		return postStateAfterWidening;
	}

	/**
	 * Check if we are entering or leaving a scope and if so, create or delete it.
	 *
	 * @param postState
	 */
	private DisjunctiveAbstractState<STATE> prepareScope(final WorklistItem<STATE, ACTION, VARDECL, LOC> currentItem,
			final DisjunctiveAbstractState<STATE> postState) {
		final ACTION action = currentItem.getAction();
		if (mTransitionProvider.isEnteringScope(action)) {
			currentItem.addScope(action, postState);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageEnterScope(currentItem));
			}
			return postState;
		} else if (isLeavingScope(currentItem)) {
			final ACTION oldScope = currentItem.removeCurrentScope(currentItem.getState());
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageLeaveScope(oldScope, currentItem));
			}
			return postState;
		} else {
			return postState;
		}
	}

	private boolean isLeavingScope(final WorklistItem<STATE, ACTION, VARDECL, LOC> currentItem) {
		return mTransitionProvider.isLeavingScope(currentItem.getAction(), currentItem.getCurrentScope());
	}

	private DisjunctiveAbstractState<STATE>
			getWidenStateAtScopeEntry(final WorklistItem<STATE, ACTION, VARDECL, LOC> currentItem) {
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
			final ACTION currentAction, final DisjunctiveAbstractState<STATE> pendingPostState) {
		final LOC target = mTransitionProvider.getTarget(currentAction);
		final DisjunctiveAbstractState<STATE> oldPostState = currentStateStorage.getAbstractState(target);
		assert oldPostState == null || Objects.equals(pendingPostState.getVariables(),
				oldPostState.getVariables()) : "States in the same scope have different variables";
		if (pendingPostState == oldPostState || pendingPostState.isSubsetOf(oldPostState) != SubsetResult.NONE) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessagePostIsSubsumed(pendingPostState, oldPostState));
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

	private StringBuilder getLogMessagePostIsBottom(final DisjunctiveAbstractState<STATE> pendingNewPostState) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT)
				.append(" Skipping all successors because post state [").append(pendingNewPostState.hashCode())
				.append("] is bottom");
	}

	private StringBuilder getLogMessagePostIsSubsumed(final DisjunctiveAbstractState<STATE> subState,
			final DisjunctiveAbstractState<STATE> superState) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT)
				.append(" Skipping all successors because post state ").append(LoggingHelper.getStateString(subState))
				.append(" is subsumed by pre-existing state ").append(LoggingHelper.getStateString(superState));
	}

	private StringBuilder getLogMessageLeaveScope(final ACTION oldScope,
			final WorklistItem<STATE, ACTION, VARDECL, LOC> currentItem) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Transition [")
				.append(currentItem.getAction().hashCode()).append("] leaves scope ")
				.append(LoggingHelper.getHashCodeString(oldScope)).append(" (new depth=")
				.append(currentItem.getScopeStackDepth()).append("): ")
				.append(LoggingHelper.getScopeStackString(currentItem.getScopeStack()));
	}

	private StringBuilder getLogMessageEnterScope(final WorklistItem<STATE, ACTION, VARDECL, LOC> currentItem) {
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

	private StringBuilder getLogMessageNewPostState(final DisjunctiveAbstractState<STATE> newPostState) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Adding post state [")
				.append(newPostState.hashCode()).append("] ").append(newPostState.toLogString());
	}

	private StringBuilder getLogMessageEnterLoop(final int loopCounterValue, final LOC loopHead,
			final DisjunctiveAbstractState<STATE> state) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Entering loop ").append(loopHead)
				.append(" (").append(loopCounterValue).append("), saving ").append(LoggingHelper.getStateString(state));
	}

	private StringBuilder getLogMessageCurrentTransition(final WorklistItem<STATE, ACTION, VARDECL, LOC> currentItem) {
		final DisjunctiveAbstractState<STATE> preState = currentItem.getState();
		final ACTION current = currentItem.getAction();
		final int depth = currentItem.getScopeStackDepth();
		final String preStateString = preState == null ? "NULL" : LoggingHelper.getStateString(preState).toString();
		return LoggingHelper.getTransitionString(current, mTransitionProvider).append(" processing for pre state ")
				.append(preStateString).append(" (depth=").append(depth).append(")");
	}

	private StringBuilder getLogMessageAddTransition(final WorklistItem<STATE, ACTION, VARDECL, LOC> item) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Adding [")
				.append(item.getState().hashCode()).append("]").append(" --[").append(item.getAction().hashCode())
				.append("]->");
	}
}
