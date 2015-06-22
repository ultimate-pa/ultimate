package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class AbstractInterpreter<ACTION, VARDECL> {

	// TODO: Replace with setting by replacing all reads with accesses to
	// ultimatepreferencestorage, i.e. final UltimatePreferenceStore preferences
	// = new UltimatePreferenceStore(Activator.PLUGIN_ID);
	private static final int MAX_UNWINDINGS = 10;
	private static final int MAX_STATES = 2;
	private static final String INDENT = "   ";

	private final ITransitionProvider<ACTION> mTransitionProvider;
	private final Logger mLogger;
	private final IAbstractStateStorage<ACTION, VARDECL> mStateStorage;
	private final IAbstractDomain<?, ACTION, VARDECL> mDomain;
	private final IVariableProvider<ACTION, VARDECL> mVarProvider;
	private final ILoopDetector<ACTION> mLoopDetector;
	private final IResultReporter mReporter;

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

		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mTransitionProvider = post;
		mStateStorage = storage;
		mDomain = domain;
		mVarProvider = varProvider;
		mLoopDetector = loopDetector;
		mReporter = reporter;
	}

	public void process(Collection<ACTION> initialElements) {
		final Deque<Pair<IAbstractState<ACTION, VARDECL>, ACTION>> worklist = new ArrayDeque<Pair<IAbstractState<ACTION, VARDECL>, ACTION>>();
		final Set<ACTION> closedSet = new HashSet<>();
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
			final Pair<IAbstractState<ACTION, VARDECL>, ACTION> currentPair = worklist.removeLast();
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

			if (oldPostState != null && oldPostState.isBottom()) {
				// unreachable, just continue (do not add successors to
				// worklist)
				if (mLogger.isDebugEnabled()) {
					final StringBuilder logMessage = new StringBuilder().append(INDENT).append(
							" Skipping all successors because post is bottom");
					mLogger.debug(logMessage);
				}
				closedSet.add(current);
				continue;
			}

			// calculate the (abstract) effect of the current action by first
			// declaring variables in the prestate, and then calculating their
			// values
			final IAbstractState<ACTION, VARDECL> preStateWithFreshVariables = mVarProvider.defineVariablesPost(
					current, preState);
			IAbstractState<ACTION, VARDECL> newPostState = post.apply(preStateWithFreshVariables, current);

			boolean leavingLoop = false;
			// check if this action leaves a loop
			if (!activeLoops.isEmpty()) {
				// are we leaving a loop?
				final Pair<ACTION, ACTION> lastPair = activeLoops.peek();
				if (lastPair.getSecond().equals(current)) {
					// yes, we are leaving a loop
					leavingLoop = true;
					activeLoops.pop();
					Integer loopCounterValue = loopCounters.get(lastPair);
					assert loopCounterValue != null;
					loopCounterValue++;
					loopCounters.put(lastPair, loopCounterValue);

					if (mLogger.isDebugEnabled()) {
						final StringBuilder logMessage = new StringBuilder().append(INDENT).append(" Leaving loop");
						mLogger.debug(logMessage);
					}

					if (loopCounterValue > MAX_UNWINDINGS) {
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
				closedSet.add(current);
				continue;
			}

			// check if we are about to enter a loop
			final ACTION loopExit = mLoopDetector.getLoopExit(current);
			if (loopExit != null) {
				// we are entering a loop
				if (preState.isFixpoint()) {
					// if our pre-state is a fixpoint, we do not actually
					// execute the action and do not actually enter the loop
					if (mLogger.isDebugEnabled()) {
						final StringBuilder logMessage = new StringBuilder().append(INDENT).append(
								" Skipping loop entry because pre is already fixpoint");
						mLogger.debug(logMessage);
					}
					closedSet.add(current);
					continue;
				}
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
				// new post state
				newPostState = mStateStorage.setPostStateIsFixpoint(current, oldPostState, true);
				if (mLogger.isDebugEnabled()) {
					final StringBuilder logMessage = new StringBuilder().append(INDENT).append(" post state ")
							.append(oldPostState.hashCode()).append(" is fixpoint, replacing with ")
							.append(newPostState.hashCode());
					mLogger.debug(logMessage);
				}
			} else {
				if (mLogger.isDebugEnabled()) {
					final StringBuilder logMessage = new StringBuilder().append(INDENT).append(" adding post state ")
							.append(newPostState.toLogString());
					mLogger.debug(logMessage);
				}
				mStateStorage.addAbstractPostState(current, newPostState);
			}

			if (mTransitionProvider.isPostErrorLocation(current)) {
				// TODO: How do we create a counter example, i.e. a program
				// execution?
				errorReached = true;
				mReporter.reportPossibleError();
			}

			final Collection<ACTION> successors = mTransitionProvider.getSuccessors(current);
			final Collection<ACTION> siblings = mTransitionProvider.getSiblings(current);

			if (!closedSet.containsAll(siblings)) {
				if (mLogger.isDebugEnabled()) {
					final StringBuilder logMessage = new StringBuilder().append(INDENT).append(
							" Unprocessed incoming siblings left");
					mLogger.debug(logMessage);
				}
				boolean hasLoopEntry = false;
				for (final ACTION successor : successors) {
					if (mLoopDetector.getLoopExit(successor) != null) {
						// this is a loop entry
						hasLoopEntry = true;
						break;
					}
				}
				if (!hasLoopEntry) {
					// there is no loop entry as successor, we wait until we
					// have processed all the incoming siblings
					closedSet.add(current);
					continue;
				}

				if (mLogger.isDebugEnabled()) {
					final StringBuilder logMessage = new StringBuilder().append(INDENT).append(
							" Adding anyways because its a loop entry");
					mLogger.debug(logMessage);
				}
			}

			// now add successors

			final Collection<IAbstractState<ACTION, VARDECL>> availablePostStates = mStateStorage
					.getAbstractPostStates(current);
			final int availablePostStatesCount = availablePostStates.size();

			if (availablePostStatesCount > MAX_STATES || leavingLoop) {
				if (mLogger.isDebugEnabled()) {
					final StringBuilder logMessage = new StringBuilder().append(INDENT).append(" Merging ")
							.append(availablePostStatesCount).append(" states at target location");
					mLogger.debug(logMessage);
				}
				newPostState = mStateStorage.mergePostStates(current);
				if (mLogger.isDebugEnabled()) {
					final StringBuilder logMessage = new StringBuilder().append(INDENT)
							.append(" Merging resulted in [").append(newPostState.hashCode()).append("]");
					mLogger.debug(logMessage);
				}
				for (final ACTION successor : successors) {
					final Pair<IAbstractState<ACTION, VARDECL>, ACTION> succPair = createPair(newPostState, successor);
					worklist.add(succPair);
					if (mLogger.isDebugEnabled()) {
						mLogger.debug(getTransitionLogMessage(succPair));
					}
				}
			} else {
				for (final IAbstractState<ACTION, VARDECL> postState : availablePostStates) {
					for (final ACTION successor : successors) {
						final Pair<IAbstractState<ACTION, VARDECL>, ACTION> succPair = createPair(postState, successor);
						worklist.add(succPair);
						if (mLogger.isDebugEnabled()) {
							mLogger.debug(getTransitionLogMessage(succPair));
						}

					}
				}
			}

			closedSet.add(current);
		}

		if (!errorReached) {
			mReporter.reportSafe();
		}
	}

	private StringBuilder getTransitionLogMessage(final Pair<IAbstractState<ACTION, VARDECL>, ACTION> succPair) {
		return new StringBuilder().append(INDENT).append(" Adding [").append(succPair.getFirst().hashCode())
				.append("]").append(" --[").append(succPair.getSecond().hashCode()).append("]->");
	}

	private Pair<IAbstractState<ACTION, VARDECL>, ACTION> createPair(IAbstractState<ACTION, VARDECL> newPostState,
			final ACTION successor) {
		return new Pair<IAbstractState<ACTION, VARDECL>, ACTION>(newPostState, successor);
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
}
