package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.Map;

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
import de.uni_freiburg.informatik.ultimate.util.relation.ModifiablePair;
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
	private final IResultReporter mReporter;
	private final IUltimateServiceProvider mServices;

	public AbstractInterpreter(IUltimateServiceProvider services, ITransitionProvider<ACTION> post,
			IAbstractStateStorage<ACTION, VARDECL> storage, IAbstractDomain<?, ACTION, VARDECL> domain,
			IVariableProvider<ACTION, VARDECL> varProvider, ILoopDetector<ACTION> loopDetector, IResultReporter reporter) {
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
	// TODO: Correct call/return order
	// TODO: Refactoring (not one process method)

	public void process(Collection<ACTION> initialElements) {
		final Deque<ModifiablePair<IAbstractState<ACTION, VARDECL>, ACTION>> worklist = new ArrayDeque<ModifiablePair<IAbstractState<ACTION, VARDECL>, ACTION>>();
		final Deque<Pair<ACTION, ACTION>> activeLoops = new ArrayDeque<>();
		final Map<Pair<ACTION, ACTION>, Integer> loopCounters = new HashMap<>();
		final IAbstractPostOperator<ACTION, VARDECL> post = mDomain.getPostOperator();
		final IAbstractStateBinaryOperator<ACTION, VARDECL> widening = mDomain.getWideningOperator();

		boolean errorReached = false;

		// add the initial state
		final Collection<ACTION> filteredInitialElements = mTransitionProvider.filterInitialElements(initialElements);
		for (ACTION elem : filteredInitialElements) {
			worklist.add(createPair(getCurrentAbstractPreState(elem), elem));
		}

		while (!worklist.isEmpty()) {
			CheckTimeout();

			final Pair<IAbstractState<ACTION, VARDECL>, ACTION> currentPair = worklist.removeFirst();
			final IAbstractState<ACTION, VARDECL> preState = currentPair.getFirst();
			final ACTION current = currentPair.getSecond();
			final IAbstractState<ACTION, VARDECL> oldPostState = mStateStorage.getCurrentAbstractPostState(current);

			if (mLogger.isDebugEnabled()) {
				final String preStateString = preState == null ? "NULL" : preState.toLogString();
				final StringBuilder logMessage = addHashCodeString(new StringBuilder(), current).append(" ")
						.append(mTransitionProvider.toLogString(current)).append(" processing for pre state ")
						.append(preStateString);
				mLogger.debug(logMessage);
			}

			// if (oldPostState != null && oldPostState.isBottom()) {
			// // unreachable, just continue (do not add successors to
			// // worklist)
			// if (mLogger.isDebugEnabled()) {
			// final StringBuilder logMessage = new
			// StringBuilder().append(INDENT).append(
			// " Skipping all successors because post is bottom");
			// mLogger.debug(logMessage);
			// }
			// continue;
			// }

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
						final StringBuilder logMessage = new StringBuilder().append(INDENT).append(" Leaving loop");
						mLogger.debug(logMessage);
					}

					if (loopCounterValue > mMaxUnwindings) {
						if (mLogger.isDebugEnabled()) {
							final StringBuilder logMessage = new StringBuilder().append(INDENT)
									.append(" Widening with old post state [").append(oldPostState.hashCode())
									.append("] and new post state [").append(newPostState.hashCode()).append("]");
							mLogger.debug(logMessage);
						}
						newPostState = widening.apply(oldPostState, newPostState);
						if (mLogger.isDebugEnabled()) {
							final StringBuilder logMessage = new StringBuilder().append(INDENT)
									.append(" Widening resulted in post state [").append(newPostState.hashCode())
									.append("]");
							mLogger.debug(logMessage);
						}
					}
				}
			}

			if (newPostState.isBottom()) {
				// if the new abstract state is bottom, we did not actually
				// execute the action (i.e., we do not enter loops, do not add
				// new actions to the worklist, etc.)
				if (mLogger.isDebugEnabled()) {
					final StringBuilder logMessage = new StringBuilder().append(INDENT).append(
							" Skipping all successors because post is bottom");
					mLogger.debug(logMessage);
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
				newPostState = setFixpoint(worklist, current, oldPostState);

			} else {
				if (mLogger.isDebugEnabled()) {
					final StringBuilder logMessage = new StringBuilder().append(INDENT).append(" adding post state ")
							.append(newPostState.toLogString());
					mLogger.debug(logMessage);
				}
				mStateStorage.addAbstractPostState(current, newPostState);
			}

			if (mTransitionProvider.isPostErrorLocation(current) && !newPostState.isBottom()) {
				// TODO: How do we create a counter example, i.e. a program
				// execution?
				errorReached = true;
				mReporter.reportPossibleError();
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
			addSuccessors(worklist, current, newPostState);
		}

		if (!errorReached) {
			mReporter.reportSafe();
		}
	}

	private void addSuccessors(final Deque<ModifiablePair<IAbstractState<ACTION, VARDECL>, ACTION>> worklist,
			final ACTION current, IAbstractState<ACTION, VARDECL> newPostState) {
		final Collection<ACTION> successors = mTransitionProvider.getSuccessors(current);

		if (successors.isEmpty()) {
			if (mLogger.isDebugEnabled()) {
				final StringBuilder logMessage = new StringBuilder().append(INDENT).append(" No successors");
				mLogger.debug(logMessage);
			}
			return;
		}

		final Collection<IAbstractState<ACTION, VARDECL>> availablePostStates = mStateStorage
				.getAbstractPostStates(current);
		final int availablePostStatesCount = availablePostStates.size();

		if (availablePostStatesCount > mMaxParallelStates) {
			if (mLogger.isDebugEnabled()) {
				final StringBuilder logMessage = new StringBuilder().append(INDENT).append(" Merging ")
						.append(availablePostStatesCount).append(" states at target location");
				mLogger.debug(logMessage);
			}
			newPostState = mStateStorage.mergePostStates(current);
			if (mLogger.isDebugEnabled()) {
				final StringBuilder logMessage = new StringBuilder().append(INDENT).append(" Merging resulted in [")
						.append(newPostState.hashCode()).append("]");
				mLogger.debug(logMessage);
			}
			addSuccessorsForPostState(worklist, successors, newPostState);
		} else {
			for (final IAbstractState<ACTION, VARDECL> postState : availablePostStates) {
				addSuccessorsForPostState(worklist, successors, postState);
			}
		}
	}

	private void addSuccessorsForPostState(
			final Deque<ModifiablePair<IAbstractState<ACTION, VARDECL>, ACTION>> worklist,
			final Collection<ACTION> successors, final IAbstractState<ACTION, VARDECL> postState) {
		for (final ACTION successor : successors) {
			final ModifiablePair<IAbstractState<ACTION, VARDECL>, ACTION> succPair = createPair(postState, successor);
			worklist.add(succPair);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getAddTransitionLogMessage(succPair));
			}
		}
	}

	private IAbstractState<ACTION, VARDECL> setFixpoint(
			Deque<ModifiablePair<IAbstractState<ACTION, VARDECL>, ACTION>> worklist, ACTION current,
			IAbstractState<ACTION, VARDECL> oldPostState) {
		final IAbstractState<ACTION, VARDECL> newPostState = mStateStorage.setPostStateIsFixpoint(current,
				oldPostState, true);
		if (mLogger.isDebugEnabled()) {
			final StringBuilder logMessage = new StringBuilder().append(INDENT).append(" post state ")
					.append(oldPostState.hashCode()).append(" is fixpoint, replacing with ")
					.append(newPostState.hashCode());
			mLogger.debug(logMessage);
		}

		// now, replace all occurences of oldPostState as prestate in worklist
		// with newPostState
		for (ModifiablePair<IAbstractState<ACTION, VARDECL>, ACTION> entry : worklist) {
			if (oldPostState.equals(entry.getFirst())) {
				entry.setFirst(newPostState);
			}
		}

		return newPostState;
	}

	private StringBuilder getAddTransitionLogMessage(final Pair<IAbstractState<ACTION, VARDECL>, ACTION> succPair) {
		return new StringBuilder().append(INDENT).append(" Adding [").append(succPair.getFirst().hashCode())
				.append("]").append(" --[").append(succPair.getSecond().hashCode()).append("]->");
	}

	private ModifiablePair<IAbstractState<ACTION, VARDECL>, ACTION> createPair(
			IAbstractState<ACTION, VARDECL> newPostState, final ACTION successor) {
		return new ModifiablePair<IAbstractState<ACTION, VARDECL>, ACTION>(newPostState, successor);
	}

	private IAbstractState<ACTION, VARDECL> getCurrentAbstractPreState(final ACTION current) {
		IAbstractState<ACTION, VARDECL> preState = mStateStorage.getCurrentAbstractPreState(current);
		if (preState == null) {
			preState = mDomain.createFreshState();
			preState = mVarProvider.defineVariablesPre(current, preState);
			mStateStorage.addAbstractPreState(current, preState);
		}
		return preState;
	}

	private StringBuilder addHashCodeString(StringBuilder builder, final Object current) {
		if (current == null) {
			return builder.append("[?]");
		}
		return builder.append("[").append(current.hashCode()).append("]");
	}

	private void CheckTimeout() {
		if (!mServices.getProgressMonitorService().continueProcessing()) {
			throw new ToolchainCanceledException(getClass(), "Got cancel request during abstract interpretation");
		}
	}
}
