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
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.model.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbstractInterpretationPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class FixpointEngine<ACTION, VARDECL, LOCATION> {

	private static final String INDENT = "   ";

	private final int mMaxUnwindings;
	private final int mMaxParallelStates;

	private final ITransitionProvider<ACTION> mTransitionProvider;
	private final IAbstractStateStorage<ACTION, VARDECL, LOCATION> mStateStorage;
	private final IAbstractDomain<?, ACTION, VARDECL> mDomain;
	private final IVariableProvider<ACTION, VARDECL> mVarProvider;
	private final ILoopDetector<ACTION> mLoopDetector;
	private final IResultReporter<ACTION> mReporter;
	private final IProgressAwareTimer mTimer;
	private final Logger mLogger;

	public FixpointEngine(final IUltimateServiceProvider services, final IProgressAwareTimer timer,
			final ITransitionProvider<ACTION> post, final IAbstractStateStorage<ACTION, VARDECL, LOCATION> storage,
			final IAbstractDomain<?, ACTION, VARDECL> domain, final IVariableProvider<ACTION, VARDECL> varProvider,
			final ILoopDetector<ACTION> loopDetector, final IResultReporter<ACTION> reporter) {
		assert timer != null;
		assert services != null;
		assert post != null;
		assert storage != null;
		assert domain != null;
		assert varProvider != null;
		assert loopDetector != null;
		assert reporter != null;

		mTimer = timer;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mTransitionProvider = post;
		mStateStorage = storage;
		mDomain = domain;
		mVarProvider = varProvider;
		mLoopDetector = loopDetector;
		mReporter = reporter;

		final UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.PLUGIN_ID);
		mMaxUnwindings = ups.getInt(AbstractInterpretationPreferenceInitializer.LABEL_ITERATIONS_UNTIL_WIDENING);
		mMaxParallelStates = ups.getInt(AbstractInterpretationPreferenceInitializer.LABEL_STATES_UNTIL_MERGE);
	}

	public void run(ACTION start) {
		if (!runInternal(start)) {
			mReporter.reportSafe();
		}
	}

	// TODO: Recursion
	private boolean runInternal(final ACTION start) {
		final Deque<WorklistItem<ACTION, VARDECL, LOCATION>> worklist = new ArrayDeque<WorklistItem<ACTION, VARDECL, LOCATION>>();
		final Deque<Pair<ACTION, ACTION>> activeLoops = new ArrayDeque<>();
		final Map<Pair<ACTION, ACTION>, Integer> loopCounters = new HashMap<>();
		final IAbstractPostOperator<ACTION, VARDECL> post = mDomain.getPostOperator();
		final IAbstractStateBinaryOperator<ACTION, VARDECL> widening = mDomain.getWideningOperator();
		final Set<ACTION> reachedErrors = new HashSet<>();

		boolean errorReached = false;
		worklist.add(createWorklistItem(start));

		while (!worklist.isEmpty()) {
			checkTimeout();

			final WorklistItem<ACTION, VARDECL, LOCATION> currentItem = worklist.removeFirst();
			final IAbstractState<ACTION, VARDECL> preState = currentItem.getPreState();
			final ACTION current = currentItem.getAction();
			final IAbstractStateStorage<ACTION, VARDECL, LOCATION> currentStateStorage = currentItem
					.getCurrentStorage();
			final IAbstractState<ACTION, VARDECL> oldPostState = currentStateStorage
					.getCurrentAbstractPostState(current);

			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageCurrentTransition(preState, current));
			}

			// calculate the (abstract) effect of the current action by first
			// declaring variables in the prestate, and then calculating their
			// values
			final IAbstractState<ACTION, VARDECL> preStateWithFreshVariables = mVarProvider.defineVariablesPost(current,
					preState);
			IAbstractState<ACTION, VARDECL> newPostState = post.apply(preStateWithFreshVariables, current);

			// check if this action leaves a loop
			if (!activeLoops.isEmpty()) {
				// are we leaving a loop?
				final Pair<ACTION, ACTION> lastPair = activeLoops.peek();
				if (lastPair.getSecond().equals(current)) {
					newPostState = loopLeave(activeLoops, loopCounters, widening, oldPostState, newPostState, lastPair);
				}
			}

			if (newPostState.isBottom()) {
				// if the new abstract state is bottom, we did not actually
				// execute the action (i.e., we do not enter loops, do not add
				// new actions to the worklist, etc.)
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(new StringBuilder().append(INDENT)
							.append(" Skipping all successors because post is bottom"));
				}
				continue;
			}

			// check if we are about to enter a loop
			final ACTION loopExit = mLoopDetector.getLoopExit(current);
			if (loopExit != null) {
				loopEnter(activeLoops, loopCounters, current, loopExit);
			}

			if (newPostState.isEqualTo(oldPostState)) {
				// found fixpoint, mark old post state as fixpoint, do not add
				// new post state, replace all occurences of old post state as
				// pre-state in worklist with new post state
				newPostState = setFixpoint(worklist, currentItem, oldPostState);

			} else {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(getLogMessageNewPostState(newPostState));
				}
				currentStateStorage.addAbstractPostState(current, newPostState);
			}
			if (mTransitionProvider.isPostErrorLocation(current, currentItem.getCurrentScope())
					&& !newPostState.isBottom() && reachedErrors.add(current)) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(new StringBuilder().append(INDENT).append(" Error state reached"));
				}
				errorReached = true;
				mReporter.reportPossibleError(start, current);
			}

			if (newPostState.isFixpoint() && preState.isFixpoint()) {
				// if our post state is a fixpoint, we do not add successors
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(new StringBuilder().append(INDENT)
							.append(" Skipping successors because pre and post states are fixpoints"));
				}
				continue;
			}

			// now add successors
			addSuccessors(worklist, currentItem);
		}
		return errorReached;
	}

	private void loopEnter(final Deque<Pair<ACTION, ACTION>> activeLoops,
			final Map<Pair<ACTION, ACTION>, Integer> loopCounters, final ACTION current, final ACTION loopExit) {
		// we are entering a loop
		final Pair<ACTION, ACTION> pair = new Pair<ACTION, ACTION>(current, loopExit);
		activeLoops.push(pair);
		if (!loopCounters.containsKey(pair)) {
			loopCounters.put(pair, 0);
		}
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(getLogMessageEnterLoop(loopCounters, pair));
		}
	}

	private IAbstractState<ACTION, VARDECL> loopLeave(final Deque<Pair<ACTION, ACTION>> activeLoops,
			final Map<Pair<ACTION, ACTION>, Integer> loopCounters,
			final IAbstractStateBinaryOperator<ACTION, VARDECL> widening,
			final IAbstractState<ACTION, VARDECL> oldPostState, final IAbstractState<ACTION, VARDECL> pendingPostState,
			final Pair<ACTION, ACTION> lastPair) {
		// yes, we are leaving a loop
		activeLoops.pop();
		Integer loopCounterValue = loopCounters.get(lastPair);
		assert loopCounterValue != null;
		loopCounterValue++;
		loopCounters.put(lastPair, loopCounterValue);

		if (mLogger.isDebugEnabled()) {
			mLogger.debug(new StringBuilder().append(INDENT).append(" Leaving loop"));
		}

		if (loopCounterValue > mMaxUnwindings) {
			return applyWidening(widening, oldPostState, pendingPostState);
		}
		return pendingPostState;
	}

	private WorklistItem<ACTION, VARDECL, LOCATION> createWorklistItem(final ACTION elem) {
		final WorklistItem<ACTION, VARDECL, LOCATION> startItem = new WorklistItem<ACTION, VARDECL, LOCATION>(
				getCurrentAbstractPreState(elem, mStateStorage), elem, mStateStorage);
		if (mTransitionProvider.isEnteringScope(elem)) {
			startItem.addScope(elem);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(new StringBuilder().append(INDENT).append(" Entering (initial) scope"));
			}
		}
		return startItem;
	}

	private IAbstractState<ACTION, VARDECL> applyWidening(final IAbstractStateBinaryOperator<ACTION, VARDECL> widening,
			final IAbstractState<ACTION, VARDECL> oldPostState, IAbstractState<ACTION, VARDECL> pendingPostState) {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(getLogMessageUnwinding(oldPostState, pendingPostState));
		}
		final IAbstractState<ACTION, VARDECL> newPostState = widening.apply(oldPostState, pendingPostState);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(getLogMessageUnwindingResult(newPostState));
		}
		return newPostState;
	}

	private void addSuccessors(final Deque<WorklistItem<ACTION, VARDECL, LOCATION>> worklist,
			final WorklistItem<ACTION, VARDECL, LOCATION> currentItem) {
		final ACTION current = currentItem.getAction();
		final Collection<ACTION> successors = mTransitionProvider.getSuccessors(current, currentItem.getCurrentScope());

		if (successors.isEmpty()) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(new StringBuilder().append(INDENT).append(" No successors"));
			}
			return;
		}

		final IAbstractStateStorage<ACTION, VARDECL, LOCATION> currentStateStorage = currentItem.getCurrentStorage();
		final Collection<IAbstractState<ACTION, VARDECL>> availablePostStates = currentStateStorage
				.getAbstractPostStates(current);
		final int availablePostStatesCount = availablePostStates.size();

		if (availablePostStatesCount > mMaxParallelStates) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageMergeStates(availablePostStatesCount));
			}
			final IAbstractState<ACTION, VARDECL> newPostState = currentStateStorage.mergePostStates(current);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageMergeResult(newPostState));
			}
			addSuccessorsForPostState(worklist, currentItem, successors, newPostState);
		} else {
			for (final IAbstractState<ACTION, VARDECL> postState : availablePostStates) {
				addSuccessorsForPostState(worklist, currentItem, successors, postState);
			}
		}
	}

	private void addSuccessorsForPostState(final Deque<WorklistItem<ACTION, VARDECL, LOCATION>> worklist,
			final WorklistItem<ACTION, VARDECL, LOCATION> currentItem, final Collection<ACTION> successors,
			final IAbstractState<ACTION, VARDECL> postState) {
		for (final ACTION successor : successors) {
			final WorklistItem<ACTION, VARDECL, LOCATION> successorItem = new WorklistItem<ACTION, VARDECL, LOCATION>(
					postState, successor, currentItem);

			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageAddTransition(successorItem));
			}
			scopeEnterOrLeave(currentItem, successor, successorItem);
			worklist.add(successorItem);
		}
	}

	private void scopeEnterOrLeave(final WorklistItem<ACTION, VARDECL, LOCATION> currentItem, final ACTION successor,
			final WorklistItem<ACTION, VARDECL, LOCATION> successorItem) {
		if (mTransitionProvider.isEnteringScope(successor)) {
			successorItem.addScope(successor);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(
						new StringBuilder().append(INDENT).append(INDENT).append(" Successor enters scope (new depth=")
								.append(successorItem.getCallStackDepth()).append(")"));
			}
		} else if (mTransitionProvider.isLeavingScope(successor, currentItem.getCurrentScope())) {
			successorItem.removeCurrentScope();
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(
						new StringBuilder().append(INDENT).append(INDENT).append(" Successor leaves scope (new depth=")
								.append(successorItem.getCallStackDepth()).append(")"));
			}
		}
	}

	private IAbstractState<ACTION, VARDECL> setFixpoint(Deque<WorklistItem<ACTION, VARDECL, LOCATION>> worklist,
			final WorklistItem<ACTION, VARDECL, LOCATION> currentItem, IAbstractState<ACTION, VARDECL> oldPostState) {
		final IAbstractState<ACTION, VARDECL> newPostState = currentItem.getCurrentStorage()
				.setPostStateIsFixpoint(currentItem.getAction(), oldPostState, true);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(getLogMessageFixpointFound(oldPostState, newPostState));
		}

		// now, replace all occurences of oldPostState as prestate in worklist
		// with newPostState
		for (final WorklistItem<ACTION, VARDECL, LOCATION> entry : worklist) {
			if (oldPostState.equals(entry.getPreState())) {
				entry.setPreState(newPostState);
			}
		}

		return newPostState;
	}

	private IAbstractState<ACTION, VARDECL> getCurrentAbstractPreState(final ACTION current,
			IAbstractStateStorage<ACTION, VARDECL, LOCATION> stateStorage) {
		IAbstractState<ACTION, VARDECL> preState = stateStorage.getCurrentAbstractPreState(current);
		if (preState == null) {
			preState = mDomain.createFreshState();
			preState = mVarProvider.defineVariablesPre(current, preState);
			stateStorage.addAbstractPreState(current, preState);
		}
		return preState;
	}

	private void checkTimeout() {
		if (!mTimer.continueProcessing()) {
			throw new ToolchainCanceledException(getClass(), "Got cancel request during abstract interpretation");
		}
	}

	private StringBuilder getLogMessageFixpointFound(IAbstractState<ACTION, VARDECL> oldPostState,
			final IAbstractState<ACTION, VARDECL> newPostState) {
		return new StringBuilder().append(INDENT).append(" post state ").append(oldPostState.hashCode())
				.append(" is fixpoint, replacing with ").append(newPostState.hashCode());
	}

	private StringBuilder getLogMessageMergeResult(IAbstractState<ACTION, VARDECL> newPostState) {
		return new StringBuilder().append(INDENT).append(" Merging resulted in [").append(newPostState.hashCode())
				.append("]");
	}

	private StringBuilder getLogMessageMergeStates(final int availablePostStatesCount) {
		return new StringBuilder().append(INDENT).append(" Merging ").append(availablePostStatesCount)
				.append(" states at target location");
	}

	private StringBuilder getLogMessageNewPostState(IAbstractState<ACTION, VARDECL> newPostState) {
		return new StringBuilder().append(INDENT).append(" adding post state [").append(newPostState.hashCode())
				.append("] ").append(newPostState.toLogString());
	}

	private StringBuilder getLogMessageEnterLoop(final Map<Pair<ACTION, ACTION>, Integer> loopCounters,
			final Pair<ACTION, ACTION> pair) {
		return new StringBuilder().append(INDENT).append(" Entering loop (").append(loopCounters.get(pair)).append(")");
	}

	private StringBuilder getLogMessageUnwindingResult(IAbstractState<ACTION, VARDECL> newPostState) {
		return new StringBuilder().append(INDENT).append(" Widening resulted in post state [")
				.append(newPostState.hashCode()).append("]");
	}

	private StringBuilder getLogMessageUnwinding(final IAbstractState<ACTION, VARDECL> oldPostState,
			IAbstractState<ACTION, VARDECL> newPostState) {
		return new StringBuilder().append(INDENT).append(" Widening with old post state [")
				.append(oldPostState.hashCode()).append("] and new post state [").append(newPostState.hashCode())
				.append("]");
	}

	private StringBuilder getLogMessageCurrentTransition(final IAbstractState<ACTION, VARDECL> preState,
			final ACTION current) {
		final String preStateString = preState == null ? "NULL"
				: addHashCodeString(new StringBuilder(), preState).append(" ").append(preState.toLogString())
						.toString();
		return addHashCodeString(new StringBuilder(), current).append(" ")
				.append(mTransitionProvider.toLogString(current)).append(" processing for pre state ")
				.append(preStateString);
	}

	private StringBuilder getLogMessageAddTransition(final WorklistItem<ACTION, VARDECL, LOCATION> newTransition) {
		return new StringBuilder().append(INDENT).append(" Adding [").append(newTransition.getPreState().hashCode())
				.append("]").append(" --[").append(newTransition.getAction().hashCode()).append("]->");
	}

	private StringBuilder addHashCodeString(StringBuilder builder, final Object current) {
		if (current == null) {
			return builder.append("[?]");
		}
		return builder.append("[").append(current.hashCode()).append("]");
	}
}
