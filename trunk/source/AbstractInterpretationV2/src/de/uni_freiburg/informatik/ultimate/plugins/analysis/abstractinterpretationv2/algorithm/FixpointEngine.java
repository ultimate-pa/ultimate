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
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.model.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class FixpointEngine<STATE extends IAbstractState<STATE, ACTION, VARDECL>, ACTION, VARDECL, LOCATION> {

	private final int mMaxUnwindings;
	private final int mMaxParallelStates;

	private final ITransitionProvider<ACTION> mTransitionProvider;
	private final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> mStateStorage;
	private final IAbstractDomain<STATE, ACTION, VARDECL> mDomain;
	private final IVariableProvider<STATE, ACTION, VARDECL, LOCATION> mVarProvider;
	private final ILoopDetector<ACTION> mLoopDetector;
	private final IResultReporter<ACTION> mReporter;
	private final IProgressAwareTimer mTimer;
	private final Logger mLogger;

	public FixpointEngine(final IUltimateServiceProvider services, final IProgressAwareTimer timer,
			final ITransitionProvider<ACTION> post,
			final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> storage,
			final IAbstractDomain<STATE, ACTION, VARDECL> domain,
			final IVariableProvider<STATE, ACTION, VARDECL, LOCATION> varProvider,
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
		mMaxUnwindings = ups.getInt(AbsIntPrefInitializer.LABEL_ITERATIONS_UNTIL_WIDENING);
		mMaxParallelStates = ups.getInt(AbsIntPrefInitializer.LABEL_STATES_UNTIL_MERGE);
	}

	/**
	 * @return true iff safe
	 */
	public boolean run(ACTION start) {
		if (!runInternal(start)) {
			mReporter.reportSafe(start);
			return true;
		}
		return false;
	}

	// TODO: Recursion
	private boolean runInternal(final ACTION start) {
		final Deque<WorklistItem<STATE, ACTION, VARDECL, LOCATION>> worklist = new ArrayDeque<WorklistItem<STATE, ACTION, VARDECL, LOCATION>>();
		final Deque<Pair<ACTION, ACTION>> activeLoops = new ArrayDeque<>();
		final Map<Pair<ACTION, ACTION>, Integer> loopCounters = new HashMap<>();
		final IAbstractPostOperator<STATE, ACTION, VARDECL> post = mDomain.getPostOperator();
		final IAbstractStateBinaryOperator<STATE> widening = mDomain.getWideningOperator();
		final Set<ACTION> reachedErrors = new HashSet<>();

		boolean errorReached = false;
		worklist.add(createWorklistItem(start));

		while (!worklist.isEmpty()) {
			checkTimeout();

			final WorklistItem<STATE, ACTION, VARDECL, LOCATION> currentItem = worklist.removeFirst();
			final STATE preState = currentItem.getPreState();
			final ACTION currentAction = currentItem.getAction();
			final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> currentStateStorage = currentItem
					.getCurrentStorage();

			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageCurrentTransition(preState, currentAction, currentItem.getCallStackDepth()));
			}

			// calculate the (abstract) effect of the current action by first
			// declaring variables in the prestate, and then calculating their
			// values
			final STATE preStateWithFreshVariables = mVarProvider.defineVariablesAfter(currentAction, preState,
					currentItem.getCurrentStorage());

			STATE pendingNewPostState;
			final List<STATE> postStates;
			if (preState == preStateWithFreshVariables) {
				postStates = post.apply(preStateWithFreshVariables, currentAction);
			} else {
				// a context switch happened
				postStates = post.apply(preState, preStateWithFreshVariables, currentAction);
			}

			// TODO: Handle multiple states from post correctly here; for now, we merge the states 
			pendingNewPostState = mergeStates(postStates);

			// check if this action leaves a loop
			if (!activeLoops.isEmpty()) {
				// are we leaving a loop?
				final Pair<ACTION, ACTION> lastPair = activeLoops.peek();
				if (lastPair.getSecond() == currentAction) {
					// yes, we are leaving a loop
					final List<STATE> currentStateStack = currentStateStorage.getAbstractPostStates(currentAction);
					pendingNewPostState = loopLeave(activeLoops, loopCounters, widening, currentStateStack,
							pendingNewPostState, lastPair);
				}
			}

			final STATE newPostState = pendingNewPostState;

			if (newPostState.isBottom()) {
				// if the new abstract state is bottom, we did not actually
				// execute the action (i.e., we do not enter loops, do not add
				// new actions to the worklist, etc.)
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(new StringBuilder().append(AbsIntPrefInitializer.INDENT)
							.append(" Skipping all successors because post is bottom"));
				}
				continue;
			}

			// check if we are about to enter a loop
			final ACTION loopExit = mLoopDetector.getLoopExit(currentAction);
			if (loopExit != null) {
				// we are entering a loop
				loopEnter(activeLoops, loopCounters, currentAction, loopExit);
			}

			if (checkFixpoint(currentItem, currentAction, newPostState)) {
				continue;
			}

			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageNewPostState(newPostState));
			}
			currentStateStorage.addAbstractPostState(currentAction, newPostState);

			if (mTransitionProvider.isPostErrorLocation(currentAction, currentItem.getCurrentScope())
					&& !newPostState.isBottom() && reachedErrors.add(currentAction)) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(
							new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Error state reached"));
				}
				errorReached = true;
				mReporter.reportPossibleError(start, currentAction);
			}

			// now add successors
			addSuccessors(worklist, currentItem);
		}
		return errorReached;
	}

	/**
	 * Merges a list of states into one single state.
	 * 
	 * @param states
	 *            The list of states to merge.
	 * @return A new {@link IntervalDomainState} which is the result of the merger of all states in the list of states.
	 */
	private STATE mergeStates(final List<STATE> states) {
		assert states != null;

		STATE returnState = null;
		final IAbstractStateBinaryOperator<STATE> mergeOperator = mDomain.getMergeOperator();

		for (int i = 0; i < states.size(); i++) {
			if (i == 0) {
				returnState = states.get(0);
			} else {
				returnState = mergeOperator.apply(returnState, states.get(i));
			}
		}

		return returnState;
	}

	private boolean checkFixpoint(WorklistItem<STATE, ACTION, VARDECL, LOCATION> currentItem, ACTION currentAction,
			STATE newPostState) {
		final Collection<STATE> oldPostStates = currentItem.getCurrentStorage().getAbstractPostStates(currentAction);
		final Optional<STATE> fixpointState = oldPostStates.stream().filter(old -> newPostState.isEqualTo(old))
				.findAny();

		if (fixpointState.isPresent()) {
			// if the state is a fixpoint, we do not need to continue
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageFixpointFound(fixpointState.get(), newPostState));
			}
			return true;
		}
		return false;

	}

	private void loopEnter(final Deque<Pair<ACTION, ACTION>> activeLoops,
			final Map<Pair<ACTION, ACTION>, Integer> loopCounters, final ACTION current, final ACTION loopExit) {
		final Pair<ACTION, ACTION> pair = new Pair<ACTION, ACTION>(current, loopExit);
		activeLoops.push(pair);
		if (!loopCounters.containsKey(pair)) {
			loopCounters.put(pair, 0);
		}
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(getLogMessageEnterLoop(loopCounters, pair));
		}
	}

	private STATE loopLeave(final Deque<Pair<ACTION, ACTION>> activeLoops,
			final Map<Pair<ACTION, ACTION>, Integer> loopCounters, final IAbstractStateBinaryOperator<STATE> widening,
			final List<STATE> currentStateStack, final STATE pendingPostState, final Pair<ACTION, ACTION> lastPair) {
		activeLoops.pop();
		Integer loopCounterValue = loopCounters.get(lastPair);
		assert loopCounterValue != null;
		loopCounterValue++;
		loopCounters.put(lastPair, loopCounterValue);

		if (mLogger.isDebugEnabled()) {
			mLogger.debug(getLogMessageLeaveLoop(loopCounters, lastPair));
		}
		
		if (loopCounterValue > mMaxUnwindings) {
			assert !currentStateStack.isEmpty();
			//we widen with the last state at this location, but we could widen from the beginning 
			return applyWidening(widening, currentStateStack.get(currentStateStack.size()-1), pendingPostState);
		}
		return pendingPostState;
	}

	private WorklistItem<STATE, ACTION, VARDECL, LOCATION> createWorklistItem(final ACTION elem) {
		final WorklistItem<STATE, ACTION, VARDECL, LOCATION> startItem = new WorklistItem<STATE, ACTION, VARDECL, LOCATION>(
				getCurrentAbstractPreState(elem, mStateStorage), elem, mStateStorage);
		if (mTransitionProvider.isEnteringScope(elem)) {
			startItem.addScope(elem);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(
						new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Entering (initial) scope"));
			}
		}
		return startItem;
	}

	private STATE applyWidening(final IAbstractStateBinaryOperator<STATE> widening, final STATE oldPostState,
			STATE pendingPostState) {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(getLogMessageUnwinding(oldPostState, pendingPostState));
		}
		final STATE newPostState = widening.apply(oldPostState, pendingPostState);
		assert oldPostState.getVariables().keySet()
				.equals(newPostState.getVariables().keySet()) : "Widening destroyed the state";
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(getLogMessageUnwindingResult(newPostState));
		}
		return newPostState;
	}

	private void addSuccessors(final Deque<WorklistItem<STATE, ACTION, VARDECL, LOCATION>> worklist,
			final WorklistItem<STATE, ACTION, VARDECL, LOCATION> currentItem) {
		final ACTION current = currentItem.getAction();
		final Collection<ACTION> successors = mTransitionProvider.getSuccessors(current, currentItem.getCurrentScope());

		if (successors.isEmpty()) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" No successors"));
			}
			return;
		}

		final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> currentStateStorage = currentItem
				.getCurrentStorage();
		final Collection<STATE> availablePostStates = currentStateStorage.getAbstractPostStates(current);
		final int availablePostStatesCount = availablePostStates.size();

		if (availablePostStatesCount > mMaxParallelStates) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageMergeStates(availablePostStatesCount, availablePostStates));
			}
			removeMergedStatesFromWorklist(worklist, availablePostStates, current);
			final STATE newPostState = currentStateStorage.mergePostStates(current);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageMergeResult(newPostState));
			}
			addSuccessorsForPostState(worklist, currentItem, successors, newPostState);
		} else {
			for (final STATE postState : availablePostStates) {
				addSuccessorsForPostState(worklist, currentItem, successors, postState);
			}
		}
	}

	private void removeMergedStatesFromWorklist(final Deque<WorklistItem<STATE, ACTION, VARDECL, LOCATION>> worklist,
			final Collection<STATE> availablePostStates, final ACTION current) {
		final Iterator<WorklistItem<STATE, ACTION, VARDECL, LOCATION>> iter = worklist.iterator();
		while (iter.hasNext()) {
			final WorklistItem<STATE, ACTION, VARDECL, LOCATION> currentItem = iter.next();
			// note that here the state has to be equal, i.e., the same instance
			if (currentItem.getAction() == current && availablePostStates.contains(currentItem.getPreState())) {
				iter.remove();
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(getLogMessageRemoveFromWorklistDuringMerge(currentItem));
				}
			}
		}
	}

	private void addSuccessorsForPostState(final Deque<WorklistItem<STATE, ACTION, VARDECL, LOCATION>> worklist,
			final WorklistItem<STATE, ACTION, VARDECL, LOCATION> currentItem, final Collection<ACTION> successors,
			final STATE postState) {
		for (final ACTION successor : successors) {
			final WorklistItem<STATE, ACTION, VARDECL, LOCATION> successorItem = new WorklistItem<STATE, ACTION, VARDECL, LOCATION>(
					postState, successor, currentItem);

			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageAddTransition(successorItem));
			}
			scopeEnterOrLeave(currentItem, successor, successorItem);
			worklist.add(successorItem);
		}
	}

	private void scopeEnterOrLeave(final WorklistItem<STATE, ACTION, VARDECL, LOCATION> currentItem,
			final ACTION successor, final WorklistItem<STATE, ACTION, VARDECL, LOCATION> successorItem) {
		if (mTransitionProvider.isEnteringScope(successor)) {
			successorItem.addScope(successor);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(new StringBuilder().append(AbsIntPrefInitializer.INDENT)
						.append(AbsIntPrefInitializer.INDENT).append(" Successor enters scope (new depth=")
						.append(successorItem.getCallStackDepth()).append(")"));
			}
		} else if (mTransitionProvider.isLeavingScope(successor, currentItem.getCurrentScope())) {
			successorItem.removeCurrentScope();
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(new StringBuilder().append(AbsIntPrefInitializer.INDENT)
						.append(AbsIntPrefInitializer.INDENT).append(" Successor leaves scope (new depth=")
						.append(successorItem.getCallStackDepth()).append(")"));
			}
		}
	}

	private STATE getCurrentAbstractPreState(final ACTION current,
			IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> stateStorage) {
		STATE preState = stateStorage.getCurrentAbstractPreState(current);
		if (preState == null) {
			preState = mDomain.createFreshState();
			preState = mVarProvider.defineVariablesBefore(current, preState);
			stateStorage.addAbstractPreState(current, preState);
		}
		return preState;
	}

	private void checkTimeout() {
		if (!mTimer.continueProcessing()) {
			throw new ToolchainCanceledException(getClass(), "Got cancel request during abstract interpretation");
		}
	}

	private StringBuilder getLogMessageFixpointFound(STATE oldPostState, final STATE newPostState) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" new post state [")
				.append(oldPostState.hashCode()).append("] ").append(oldPostState.toLogString())
				.append(" is fixpoint, replacing with [").append(newPostState.hashCode()).append("]");
	}

	private StringBuilder getLogMessageMergeResult(STATE newPostState) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Merging resulted in [")
				.append(newPostState.hashCode()).append("] ").append(newPostState.toLogString());
	}

	private StringBuilder getLogMessageRemoveFromWorklistDuringMerge(
			final WorklistItem<STATE, ACTION, VARDECL, LOCATION> item) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Removing [")
				.append(item.getPreState().hashCode()).append("]").append(" --[").append(item.getAction().hashCode())
				.append("]-> from worklist during merge");
	}

	private StringBuilder getLogMessageMergeStates(final int availablePostStatesCount,
			Collection<STATE> availablePostStates) {
		final List<String> postStates = availablePostStates.stream().map(a -> "[" + String.valueOf(a.hashCode()) + "]")
				.collect(Collectors.toList());
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Merging ")
				.append(availablePostStatesCount).append(" states at target location: ")
				.append(String.join(",", postStates));
	}

	private StringBuilder getLogMessageNewPostState(STATE newPostState) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Adding post state [")
				.append(newPostState.hashCode()).append("] ").append(newPostState.toLogString());
	}

	private StringBuilder getLogMessageEnterLoop(final Map<Pair<ACTION, ACTION>, Integer> loopCounters,
			final Pair<ACTION, ACTION> pair) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Entering loop (")
				.append(loopCounters.get(pair)).append(") via [").append(pair.getFirst().hashCode()).append("],[")
				.append(pair.getSecond().hashCode()).append("]");
	}

	private StringBuilder getLogMessageLeaveLoop(final Map<Pair<ACTION, ACTION>, Integer> loopCounters,
			final Pair<ACTION, ACTION> pair) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Leaving loop (")
				.append(loopCounters.get(pair)).append(") via [").append(pair.getFirst().hashCode()).append("],[")
				.append(pair.getSecond().hashCode()).append("]");
//		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Leaving loop");
	}

	private StringBuilder getLogMessageUnwindingResult(STATE newPostState) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Widening resulted in post state [")
				.append(newPostState.hashCode()).append("] ").append(newPostState.toLogString());
	}

	private StringBuilder getLogMessageUnwinding(final STATE oldPostState, STATE newPostState) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Widening with old post state [")
				.append(oldPostState.hashCode()).append("] ").append(oldPostState.toLogString())
				.append(" and new post state [").append(newPostState.hashCode()).append("] ")
				.append(newPostState.toLogString());
	}

	private StringBuilder getLogMessageCurrentTransition(final STATE preState, final ACTION current, int depth) {
		final String preStateString = preState == null ? "NULL"
				: addHashCodeString(new StringBuilder(), preState).append(" ").append(preState.toLogString())
						.toString();
		return addHashCodeString(new StringBuilder(), current).append(" ")
				.append(mTransitionProvider.toLogString(current)).append(" processing for pre state ")
				.append(preStateString).append(" (depth=").append(depth).append(")");
	}

	private StringBuilder getLogMessageAddTransition(
			final WorklistItem<STATE, ACTION, VARDECL, LOCATION> newTransition) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Adding [")
				.append(newTransition.getPreState().hashCode()).append("]").append(" --[")
				.append(newTransition.getAction().hashCode()).append("]->");
	}

	private StringBuilder addHashCodeString(StringBuilder builder, final Object current) {
		if (current == null) {
			return builder.append("[?]");
		}
		return builder.append("[").append(current.hashCode()).append("]");
	}
}
