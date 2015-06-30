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
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbstractInterpretationPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class AbstractInterpreter<ACTION, VARDECL> {

	private static final String INDENT = "   ";

	private final int mMaxUnwindings;
	private final int mMaxParallelStates;

	private final ITransitionProvider<ACTION> mTransitionProvider;
	private final Logger mLogger;
	private final IAbstractStateStorage<ACTION, VARDECL> mStateStorage;
	private final IAbstractDomain<?, ACTION, VARDECL> mDomain;
	private final IVariableProvider<ACTION, VARDECL> mVarProvider;
	private final ILoopDetector<ACTION> mLoopDetector;
	private final IResultReporter<ACTION> mReporter;
	private final IUltimateServiceProvider mServices;

	public AbstractInterpreter(IUltimateServiceProvider services, ITransitionProvider<ACTION> post,
			IAbstractStateStorage<ACTION, VARDECL> storage, IAbstractDomain<?, ACTION, VARDECL> domain,
			IVariableProvider<ACTION, VARDECL> varProvider, ILoopDetector<ACTION> loopDetector,
			IResultReporter<ACTION> reporter) {
		assert services != null;
		assert post != null;
		assert storage != null;
		assert domain != null;
		assert varProvider != null;
		assert loopDetector != null;
		assert reporter != null;

		mServices = services;
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

	// TODO: Recursion
	// TODO: Refactoring (not one process method)

	public void process(Collection<ACTION> initialElements) {
		final Deque<WorklistItem<ACTION, VARDECL>> worklist = new ArrayDeque<WorklistItem<ACTION, VARDECL>>();
		final Deque<Pair<ACTION, ACTION>> activeLoops = new ArrayDeque<>();
		final Map<Pair<ACTION, ACTION>, Integer> loopCounters = new HashMap<>();
		final IAbstractPostOperator<ACTION, VARDECL> post = mDomain.getPostOperator();
		final IAbstractStateBinaryOperator<ACTION, VARDECL> widening = mDomain.getWideningOperator();
		final Set<ACTION> reachedErrors = new HashSet<>();

		boolean errorReached = false;

		// add the initial state
		final Collection<ACTION> filteredInitialElements = mTransitionProvider.filterInitialElements(initialElements);
		for (ACTION elem : filteredInitialElements) {
			final ACTION successor = elem;
			final WorklistItem<ACTION, VARDECL> startItem = new WorklistItem<ACTION, VARDECL>(
					getCurrentAbstractPreState(elem, mStateStorage), successor, mStateStorage);
			if (mTransitionProvider.isEnteringScope(elem)) {
				startItem.addScope(elem);
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(new StringBuilder().append(INDENT).append(" Entering (initial) scope"));
				}
			}
			worklist.add(startItem);
		}
		// TODO: We should think about reducing this to really distinct start
		// elements; for now, we just pick one
		final ACTION arbitraryStartElement = filteredInitialElements.iterator().next();

		while (!worklist.isEmpty()) {
			checkTimeout();

			final WorklistItem<ACTION, VARDECL> currentItem = worklist.removeFirst();
			final IAbstractState<ACTION, VARDECL> preState = currentItem.getPreState();
			final ACTION current = currentItem.getAction();
			final IAbstractStateStorage<ACTION, VARDECL> currentStateStorage = currentItem.getCurrentStorage();
			final IAbstractState<ACTION, VARDECL> oldPostState = currentStateStorage
					.getCurrentAbstractPostState(current);

			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getCurrentTransitionLogMessage(preState, current));
			}

			// calculate the (abstract) effect of the current action by first
			// declaring variables in the prestate, and then calculating their
			// values
			final IAbstractState<ACTION, VARDECL> preStateWithFreshVariables = mVarProvider.defineVariablesPost(
					current, preState);
			IAbstractState<ACTION, VARDECL> newPostState = post.apply(preStateWithFreshVariables, current);

			// check if this action leaves a loop
			if (!activeLoops.isEmpty()) {
				// are we leaving a loop?
				final Pair<ACTION, ACTION> lastPair = activeLoops.peek();
				if (lastPair.getSecond().equals(current)) {
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
						if (mLogger.isDebugEnabled()) {
							mLogger.debug(getUnwindingLogMessage(oldPostState, newPostState));
						}
						newPostState = widening.apply(oldPostState, newPostState);
						if (mLogger.isDebugEnabled()) {
							mLogger.debug(getUnwindingResultLogMessage(newPostState));
						}
					}
				}
			}

			if (newPostState.isBottom()) {
				// if the new abstract state is bottom, we did not actually
				// execute the action (i.e., we do not enter loops, do not add
				// new actions to the worklist, etc.)
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(new StringBuilder().append(INDENT).append(
							" Skipping all successors because post is bottom"));
				}
				continue;
			}

			// check if we are about to enter a loop
			final ACTION loopExit = mLoopDetector.getLoopExit(current);
			if (loopExit != null) {
				// we are entering a loop
				final Pair<ACTION, ACTION> pair = new Pair<ACTION, ACTION>(current, loopExit);
				activeLoops.push(pair);
				if (!loopCounters.containsKey(pair)) {
					loopCounters.put(pair, 0);
				}
				if (mLogger.isDebugEnabled()) {
					final StringBuilder logMessage = new StringBuilder().append(INDENT).append(" Entering loop (")
							.append(loopCounters.get(pair)).append(")");
					mLogger.debug(logMessage);
				}
			}

			if (newPostState.isEqualTo(oldPostState)) {
				// found fixpoint, mark old post state as fixpoint, do not add
				// new post state, replace all occurences of old post state as
				// pre-state in worklist with new post state
				newPostState = setFixpoint(worklist, currentItem, oldPostState);

			} else {
				if (mLogger.isDebugEnabled()) {
					final StringBuilder logMessage = new StringBuilder().append(INDENT).append(" adding post state [")
							.append(newPostState.hashCode()).append("] ").append(newPostState.toLogString());
					mLogger.debug(logMessage);
				}
				currentStateStorage.addAbstractPostState(current, newPostState);
			}
			if (mTransitionProvider.isPostErrorLocation(current, currentItem.getCurrentScope())
					&& !newPostState.isBottom() && reachedErrors.add(current)) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(new StringBuilder().append(INDENT).append(" Error state reached"));
				}
				errorReached = true;
				mReporter.reportPossibleError(arbitraryStartElement, current);
			}

			if (newPostState.isFixpoint() && preState.isFixpoint()) {
				// if our post state is a fixpoint, we do not add successors
				if (mLogger.isDebugEnabled()) {
					final StringBuilder logMessage = new StringBuilder().append(INDENT).append(
							" Skipping successors because pre and post states are fixpoints");
					mLogger.debug(logMessage);
				}
				continue;
			}

			// now add successors
			addSuccessors(worklist, currentItem, newPostState);
		}

		if (!errorReached) {
			mReporter.reportSafe(arbitraryStartElement);
		}
	}

	private StringBuilder getUnwindingResultLogMessage(IAbstractState<ACTION, VARDECL> newPostState) {
		final StringBuilder logMessage = new StringBuilder().append(INDENT)
				.append(" Widening resulted in post state [").append(newPostState.hashCode()).append("]");
		return logMessage;
	}

	private StringBuilder getUnwindingLogMessage(final IAbstractState<ACTION, VARDECL> oldPostState,
			IAbstractState<ACTION, VARDECL> newPostState) {
		final StringBuilder logMessage = new StringBuilder().append(INDENT).append(" Widening with old post state [")
				.append(oldPostState.hashCode()).append("] and new post state [").append(newPostState.hashCode())
				.append("]");
		return logMessage;
	}

	private void addSuccessors(final Deque<WorklistItem<ACTION, VARDECL>> worklist,
			final WorklistItem<ACTION, VARDECL> currentItem, IAbstractState<ACTION, VARDECL> newPostState) {
		final ACTION current = currentItem.getAction();
		final Collection<ACTION> successors = mTransitionProvider.getSuccessors(current, currentItem.getCurrentScope());
		final IAbstractStateStorage<ACTION, VARDECL> currentStateStorage = currentItem.getCurrentStorage();
		if (successors.isEmpty()) {
			if (mLogger.isDebugEnabled()) {
				final StringBuilder logMessage = new StringBuilder().append(INDENT).append(" No successors");
				mLogger.debug(logMessage);
			}
			return;
		}

		final Collection<IAbstractState<ACTION, VARDECL>> availablePostStates = currentStateStorage
				.getAbstractPostStates(current);
		final int availablePostStatesCount = availablePostStates.size();

		if (availablePostStatesCount > mMaxParallelStates) {
			if (mLogger.isDebugEnabled()) {
				final StringBuilder logMessage = new StringBuilder().append(INDENT).append(" Merging ")
						.append(availablePostStatesCount).append(" states at target location");
				mLogger.debug(logMessage);
			}
			newPostState = currentStateStorage.mergePostStates(current);
			if (mLogger.isDebugEnabled()) {
				final StringBuilder logMessage = new StringBuilder().append(INDENT).append(" Merging resulted in [")
						.append(newPostState.hashCode()).append("]");
				mLogger.debug(logMessage);
			}
			addSuccessorsForPostState(worklist, currentItem, successors, newPostState);
		} else {
			for (final IAbstractState<ACTION, VARDECL> postState : availablePostStates) {
				addSuccessorsForPostState(worklist, currentItem, successors, postState);
			}
		}
	}

	private void addSuccessorsForPostState(final Deque<WorklistItem<ACTION, VARDECL>> worklist,
			final WorklistItem<ACTION, VARDECL> currentItem, final Collection<ACTION> successors,
			final IAbstractState<ACTION, VARDECL> postState) {
		for (final ACTION successor : successors) {
			final WorklistItem<ACTION, VARDECL> successorItem = new WorklistItem<ACTION, VARDECL>(postState, successor,
					currentItem);

			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getAddTransitionLogMessage(successorItem));
			}

			if (mTransitionProvider.isEnteringScope(successor)) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(new StringBuilder().append(INDENT).append(" Entering scope"));
				}
				successorItem.addScope(successor);
			} else if (mTransitionProvider.isLeavingScope(successor, currentItem.getCurrentScope())) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(new StringBuilder().append(INDENT).append(" Leaving scope"));
				}
				successorItem.removeCurrentScope();
			}

			worklist.add(successorItem);
		}
	}

	private IAbstractState<ACTION, VARDECL> setFixpoint(Deque<WorklistItem<ACTION, VARDECL>> worklist,
			final WorklistItem<ACTION, VARDECL> currentItem, IAbstractState<ACTION, VARDECL> oldPostState) {
		final IAbstractState<ACTION, VARDECL> newPostState = currentItem.getCurrentStorage().setPostStateIsFixpoint(
				currentItem.getAction(), oldPostState, true);
		if (mLogger.isDebugEnabled()) {
			final StringBuilder logMessage = new StringBuilder().append(INDENT).append(" post state ")
					.append(oldPostState.hashCode()).append(" is fixpoint, replacing with ")
					.append(newPostState.hashCode());
			mLogger.debug(logMessage);
		}

		// now, replace all occurences of oldPostState as prestate in worklist
		// with newPostState
		for (WorklistItem<ACTION, VARDECL> entry : worklist) {
			if (oldPostState.equals(entry.getPreState())) {
				entry.setPreState(newPostState);
			}
		}

		return newPostState;
	}

	private IAbstractState<ACTION, VARDECL> getCurrentAbstractPreState(final ACTION current,
			IAbstractStateStorage<ACTION, VARDECL> stateStorage) {
		IAbstractState<ACTION, VARDECL> preState = stateStorage.getCurrentAbstractPreState(current);
		if (preState == null) {
			preState = mDomain.createFreshState();
			preState = mVarProvider.defineVariablesPre(current, preState);
			stateStorage.addAbstractPreState(current, preState);
		}
		return preState;
	}

	private void checkTimeout() {
		if (!mServices.getProgressMonitorService().continueProcessing()) {
			throw new ToolchainCanceledException(getClass(), "Got cancel request during abstract interpretation");
		}
	}

	private StringBuilder getCurrentTransitionLogMessage(final IAbstractState<ACTION, VARDECL> preState,
			final ACTION current) {
		final String preStateString = preState == null ? "NULL" : addHashCodeString(new StringBuilder(), preState)
				.append(" ").append(preState.toLogString()).toString();
		final StringBuilder logMessage = addHashCodeString(new StringBuilder(), current).append(" ")
				.append(mTransitionProvider.toLogString(current)).append(" processing for pre state ")
				.append(preStateString);
		return logMessage;
	}

	private StringBuilder getAddTransitionLogMessage(final WorklistItem<ACTION, VARDECL> newTransition) {
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
