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

	private final ITransitionProvider<ACTION, LOCATION> mTransitionProvider;
	private final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> mStateStorage;
	private final IAbstractDomain<STATE, ACTION, VARDECL> mDomain;
	private final IVariableProvider<STATE, ACTION, VARDECL, LOCATION> mVarProvider;
	private final ILoopDetector<ACTION> mLoopDetector;
	private final IResultReporter<ACTION> mReporter;
	private final IProgressAwareTimer mTimer;
	private final Logger mLogger;

	public FixpointEngine(final IUltimateServiceProvider services, final IProgressAwareTimer timer,
			final ITransitionProvider<ACTION, LOCATION> post,
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
		mLogger.info("Starting fixpoint engine");
		if (!runInternal(start)) {
			mReporter.reportSafe(start);
			return true;
		}
		return false;
	}

	// TODO: Recursion
	private boolean runInternal(final ACTION start) {
		final Deque<WorklistItem<STATE, ACTION, VARDECL, LOCATION>> worklist = new ArrayDeque<WorklistItem<STATE, ACTION, VARDECL, LOCATION>>();
		final Deque<LOCATION> activeLoops = new ArrayDeque<>();
		final Map<LOCATION, Integer> loopCounters = new HashMap<>();
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
					currentStateStorage);

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

			if (pendingNewPostState.isBottom()) {
				// if the new abstract state is bottom, we did not actually
				// execute the action (i.e., we do not enter loops, do not add
				// new actions to the worklist, etc.)
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(new StringBuilder().append(AbsIntPrefInitializer.INDENT)
							.append(" Skipping all successors because post is bottom"));
				}
				continue;
			}

			// check if this action leaves a loop
			if (!activeLoops.isEmpty()) {
				// are we leaving a loop?
				final LOCATION lastLoopHead = activeLoops.peek();
				LOCATION currentLoopHead = mTransitionProvider.getTarget(currentAction);
				if (lastLoopHead == currentLoopHead) {
					// yes, we are leaving a loop
					// here we also check if we have to widen
					final List<STATE> currentStateStack = currentStateStorage.getAbstractPostStates(currentAction);
					pendingNewPostState = loopLeave(activeLoops, loopCounters, widening, currentStateStack,
							pendingNewPostState, lastLoopHead);
				}
			}

			// check if we should widen after entering a new scope
			if (mTransitionProvider.isEnteringScope(currentAction)) {
				pendingNewPostState = widenAtScopeEntry(currentItem, widening, pendingNewPostState);
				// check if the resulting state is a fixpoint
				if (checkFixpointAtScopeEntry(currentItem, pendingNewPostState)) {
					// TODO: single function recursion (e.g., collatz) has to somehow add the inner function return
					continue;
				}
			}

			final STATE newPostState = pendingNewPostState;

			// check if we are about to enter a loop
			if (mLoopDetector.isEnteringLoop(currentAction)) {
				// we are entering a loop
				loopEnter(activeLoops, loopCounters, currentAction);
			}

			// check if the current state is a fixpoint
			if (checkFixpoint(currentStateStorage, currentAction, newPostState)) {
				continue;
			}

			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageNewPostState(newPostState));
			}
			// add post state to this location
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

	private boolean checkFixpoint(final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> currentStorage,
			ACTION currentAction, STATE newPostState) {
		final Collection<STATE> oldPostStates = currentStorage.getAbstractPostStates(currentAction);
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

	private void loopEnter(final Deque<LOCATION> activeLoops, final Map<LOCATION, Integer> loopCounters,
			final ACTION current) {
		final LOCATION loopHead = mTransitionProvider.getSource(current);
		activeLoops.push(loopHead);
		if (!loopCounters.containsKey(loopHead)) {
			loopCounters.put(loopHead, 0);
		}
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(getLogMessageEnterLoop(loopCounters, loopHead));
		}
	}

	private STATE loopLeave(final Deque<LOCATION> activeLoops, final Map<LOCATION, Integer> loopCounters,
			final IAbstractStateBinaryOperator<STATE> widening, final List<STATE> currentStateStack,
			final STATE pendingPostState, final LOCATION lastLoopHead) {
		activeLoops.pop();
		Integer loopCounterValue = loopCounters.get(lastLoopHead);
		assert loopCounterValue != null;
		loopCounterValue++;
		loopCounters.put(lastLoopHead, loopCounterValue);

		if (mLogger.isDebugEnabled()) {
			mLogger.debug(getLogMessageLeaveLoop(loopCounters, lastLoopHead));
		}

		if (loopCounterValue > mMaxUnwindings) {
			assert !currentStateStack.isEmpty();
			// we widen with the last state at this location, but we could widen from the beginning
			return applyWidening(widening, currentStateStack.get(currentStateStack.size() - 1), pendingPostState);
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
		// TODO: Remove all worklist items that will be superseded by this widening operation,i.e. all abstract states
		// from the source of oldPostState
		// TODO: Remove all stored states that are superseded
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

	/**
	 * Check if a new scope has to be opened and if so, add the scope to the successor item.
	 * 
	 * Also checks if there is a fixpoint when entering a recursive function and returns false if no successors should
	 * be added because of this
	 */
	private boolean scopeEnterOrLeave(final WorklistItem<STATE, ACTION, VARDECL, LOCATION> currentItem,
			final ACTION successor, final WorklistItem<STATE, ACTION, VARDECL, LOCATION> successorItem) {
		if (mTransitionProvider.isEnteringScope(successor)) {
			successorItem.addScope(successor);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageEnterScope(successorItem));
			}
		} else if (mTransitionProvider.isLeavingScope(successor, currentItem.getCurrentScope())) {
			successorItem.removeCurrentScope();
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageLeaveScope(successorItem));
			}
		}
		return true;
	}

	private STATE widenAtScopeEntry(final WorklistItem<STATE, ACTION, VARDECL, LOCATION> currentItem,
			final IAbstractStateBinaryOperator<STATE> widening, final STATE pendingPostState) {
		final ACTION currentAction = currentItem.getAction();

		// check for fixpoint and/or widening
		final Deque<Pair<ACTION, IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION>>> stackAtCallLocation = currentItem
				.getStack();
		// get all stack items in the correct order that contain only calls to the current scope
		final List<Pair<ACTION, IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION>>> relevantStackItems = stackAtCallLocation
				.stream().sequential().filter(a -> a.getFirst() == currentAction || a.getFirst() == null)
				.collect(Collectors.toList());
		if (relevantStackItems.isEmpty()) {
			// cannot widen if there is no sequence
			return pendingPostState;
		}

		if (relevantStackItems.size() > mMaxUnwindings) {
			// we have to apply widening to the last state at this location and the new pending post state
			// the relevant stack contains
			final Optional<STATE> lastState = relevantStackItems.stream().sequential()
					.map(a -> a.getSecond().getAbstractPostStates(currentAction)).flatMap(a -> a.stream().sequential())
					.findFirst();
			if (lastState.isPresent()) {
				return applyWidening(widening, lastState.get(), pendingPostState);
			}

			final Optional<STATE> lastAllState = stackAtCallLocation.stream().sequential()
					.map(a -> a.getSecond().getAbstractPostStates(currentAction)).flatMap(a -> a.stream().sequential())
					.findFirst();
			if (lastAllState.isPresent()) {
				mLogger.warn(AbsIntPrefInitializer.INDENT + " Widening uses all states");
				return applyWidening(widening, lastAllState.get(), pendingPostState);
			}
			mLogger.warn("Could not widen at " + getHashCodeString(currentAction) + currentAction);
		}
		return pendingPostState;
	}

	private boolean checkFixpointAtScopeEntry(final WorklistItem<STATE, ACTION, VARDECL, LOCATION> currentItem,
			final STATE pendingPostState) {
		final ACTION currentAction = currentItem.getAction();

		// get all calls at the current locations
		final Deque<Pair<ACTION, IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION>>> stackAtCallLocation = currentItem
				.getStack();

		// get all stack items in the correct order that contain only calls to the current scope
		// the global stack item has null as action
		// final List<Pair<ACTION, IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION>>> relevantStackItems =
		// stackAtCallLocation
		// .stream().sequential().filter(a -> a.getFirst() == currentAction)
		// .collect(Collectors.toList());

		if (stackAtCallLocation.isEmpty()) {
			// if there are no relevant stack items, there cannot be a fixpoint
			return false;
		}

		for (final Pair<ACTION, IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION>> stackItem : stackAtCallLocation) {
			final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> stateStorage = stackItem.getSecond();
			if (checkFixpoint(stateStorage, currentAction, pendingPostState)) {
				// it is a fixpoint
				return true;
			}
		}
		return false;
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
			mLogger.warn("Received timeout, aborting fixpoint engine");
			throw new ToolchainCanceledException(getClass(), "Got cancel request during abstract interpretation");
		}
	}

	private StringBuilder getLogMessageLeaveScope(final WorklistItem<STATE, ACTION, VARDECL, LOCATION> successorItem) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(AbsIntPrefInitializer.INDENT)
				.append(" Successor transition [").append(successorItem.getAction().hashCode())
				.append("] leaves scope (new depth=").append(successorItem.getCallStackDepth()).append(")");
	}

	private StringBuilder getLogMessageEnterScope(final WorklistItem<STATE, ACTION, VARDECL, LOCATION> successorItem) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(AbsIntPrefInitializer.INDENT)
				.append(" Successor transition [").append(successorItem.getAction().hashCode())
				.append("] enters scope (new depth=").append(successorItem.getCallStackDepth()).append(")");
	}

	private StringBuilder getLogMessageFixpointFound(STATE oldPostState, final STATE newPostState) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Found fixpoint state [")
				.append(oldPostState.hashCode()).append("] ").append(oldPostState.toLogString())
				.append(" -- replacing with [").append(newPostState.hashCode()).append("]");
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

	private StringBuilder getLogMessageEnterLoop(final Map<LOCATION, Integer> loopCounters, final LOCATION pair) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Entering loop (")
				.append(loopCounters.get(pair)).append(")");
	}

	private StringBuilder getLogMessageLeaveLoop(final Map<LOCATION, Integer> loopCounters, final LOCATION lastPair) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Leaving loop (")
				.append(loopCounters.get(lastPair)).append(")");
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

	private String getHashCodeString(final Object current) {
		return addHashCodeString(new StringBuilder(), current).toString();
	}

	private StringBuilder addHashCodeString(final StringBuilder builder, final Object current) {
		if (current == null) {
			return builder.append("[?]");
		}
		return builder.append("[").append(current.hashCode()).append("]");
	}
}
