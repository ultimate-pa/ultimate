package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadCurrent;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class GuardedInterferenceApplier<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {
	private final ILogger mLogger;

	// TODO: Dont widen states which dont need it (dont group-widen)
	// TODO: since we now re initialize this class constantly, move cache somehwere else
	private final Map<InterferenceStatePair<STATE, ACTION, LOC>, STATE> mInterferenceCache = new HashMap<>();
	private final IAbstractPostOperator<STATE, ACTION> mUnderlyingPostOp;
	private final GuardedInterferenceDomain<STATE, ACTION, LOC> mGuardedInterferenceDomain;
	private final AbstractLocationMap<LOC> mAbstractLocationMap;
	private int mIterations;
	private final int mMaxItf;
	private final int mMaxParallelStates;
	public static int iterationsReached = 0;

	private final AbstractInterferenceState<STATE, ACTION, LOC> mInterferences;

	public GuardedInterferenceApplier(final ILogger logger, final IAbstractPostOperator<STATE, ACTION> postOp,
			final GuardedInterferenceDomain<STATE, ACTION, LOC> relationalInterferingDomain,
			final AbstractLocationMap<LOC> globalMap, final int maxItf, final int maxParallelStates,
			final AbstractInterferenceState<STATE, ACTION, LOC> interferences) {
		mLogger = logger;
		mUnderlyingPostOp = postOp;
		mGuardedInterferenceDomain = relationalInterferingDomain;
		mInterferences = interferences;
		mAbstractLocationMap = globalMap;
		mMaxItf = maxItf;
		mMaxParallelStates = maxParallelStates;
		iterationsReached = 0;
	}

	private record InterferenceStatePair<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>(
			Interference<STATE, ACTION, LOC> interf, STATE targetState) {
	}

	private record InterferenceWithParentThread<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>(
			Interference<STATE, ACTION, LOC> interf, String sourceThread) {
	}

	public AbstractInterferenceState<STATE, ACTION, LOC> getInterferences() {
		return mInterferences;
	}

	public Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> stateAfterInterferences(
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> oldstate, final String ownerThread) {
		initialize();
		final Set<String> possibleInterferenceSet = getThreadsThatCanInterfere(oldstate, ownerThread);
		if (possibleInterferenceSet.isEmpty()) {
			return Set.of(oldstate);
		}
		return interferenceFixpointFast(possibleInterferenceSet, oldstate, ownerThread);
	}

	private void initialize() {
		mIterations = 0;
	}

	private Set<String> getThreadsThatCanInterfere(final GuardedInterferenceDomainState<STATE, ACTION, LOC> oldstate,
			final String ownerThread) {
		final Set<String> threadNameSet = oldstate.threadCounter().getThreadNameSet();
		final Set<String> possibleInterferenceSet = new HashSet<>();
		final var procedureMap = oldstate.threadCounter().getThreadInstances();
		for (final String threadName : threadNameSet) {
			final int threadInstances = procedureMap.get(threadName);
			if (threadInstances >= 2 || threadName != ownerThread && threadInstances > 0) {
				possibleInterferenceSet.add(threadName);
			}
		}
		return possibleInterferenceSet;
	}

	private Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> interferenceFixpointFast(
			final Set<String> interferingThreads, final GuardedInterferenceDomainState<STATE, ACTION, LOC> state,
			final String ownerThread) {

		// Collect all starting, intermediate and final states as possibilities of all possible thread interleavings
		Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> newStates = new LinkedHashSet<>();
		newStates.add(state);
		final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> oldStates = new LinkedHashSet<>();
		oldStates.add(state);
		var allDisj = new DisjunctiveAbstractState<>(mMaxParallelStates, state);
		var newDisj = new DisjunctiveAbstractState<>(mMaxParallelStates, state);

		final var allInterferences = getValidInterferences(interferingThreads, ownerThread);

		while (true) {
			mIterations++;
			if (mIterations > iterationsReached) {
				iterationsReached = mIterations;
			}

			// state just to check if fixpoint reached after this iteration
			newStates = new HashSet<>();

			for (final GuardedInterferenceDomainState<STATE, ACTION, LOC> singleState : newDisj.getStates()) {
				for (final InterferenceWithParentThread<STATE, ACTION, LOC> interference : allInterferences) {
					final var postState = checkLocAndCacheThenApply(interference.interf(), singleState,
							interference.sourceThread(), ownerThread);
					if (postState == null) {
						continue;
					}
					// Interferences should not remove/add variables
					assert postState.getVariables().equals(singleState.getVariables());

					newStates.addAll(postState.getStates());
				}
			}
			oldStates.clear();
			newDisj = DisjunctiveAbstractState.createDisjunction(newStates, mMaxParallelStates);
			if (newDisj == null || allDisj == null) {
				continue;
			}
			final boolean changed = newDisj.isSubsetOf(allDisj) != SubsetResult.NONE ? false : true;
			if (mIterations <= mMaxItf) {
				allDisj = allDisj.union(newDisj);
			} else {
				var oldState = allDisj;
				var widenedState = allDisj.widen(mGuardedInterferenceDomain.getWideningOperator(), newDisj);

				int innerIterations = 0;
				while (!widenedState.isEqualTo(oldState)) {
					oldState = widenedState;
					widenedState = allDisj.widen(mGuardedInterferenceDomain.getWideningOperator(), oldState);
					innerIterations++;
					if (innerIterations > mMaxItf) {
						break;
					}
				}
				allDisj = widenedState;
			}
			if (mIterations > mMaxItf + 2) {
				break;
			}

			if (!changed) {
				break;
			}
			oldStates.addAll(newDisj.getStates());
			allDisj = allDisj.union(newDisj);
		}
		return allDisj.getStates();
	}

	private Set<InterferenceWithParentThread<STATE, ACTION, LOC>> getValidInterferences(
			final Set<String> interferingThreads, final String ownerThread) {
		final Set<InterferenceWithParentThread<STATE, ACTION, LOC>> allInterferences = new LinkedHashSet<>();

		for (final String interferenceThreadName : interferingThreads) {
			final var interferences = mInterferences.getInterferencesForThread(interferenceThreadName);
			if (interferences == null) {
				continue;
			}
			for (final Interference<STATE, ACTION, LOC> interference : interferences) {
				if (interference.disjState() == null) {
					continue;
				}
				if (GuardedStateTransformer.getThreadInstanceState(interference.disjState()).getThreadInstances()
						.get(ownerThread) == 0) {
					continue;
				}
				allInterferences.add(new InterferenceWithParentThread<>(interference, interferenceThreadName));
			}
		}
		return allInterferences;
	}

	private DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> checkLocAndCacheThenApply(
			final Interference<STATE, ACTION, LOC> interference,
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> newState, final String interferenceThreadName,
			final String ownerThread) {

		// 2. check abstract locations (is interfering thread in location where it matches the interference
		// action)
		if (!matchesLocation(newState, ownerThread, interferenceThreadName, interference)) {
			return null;
		}
		final var interferedStates = applyInterferenceToSTATE(interference, newState);
		var interferedState = DisjunctiveAbstractState.createDisjunction(interferedStates, mMaxParallelStates);

		// in case of interfering fork, update threadcounter and location
		if (interferedState != null && interference.action() instanceof final ForkThreadCurrent fork) {
			interferedState = GuardedStateTransformer.setThreadsActive(Set.of(fork.getNameOfForkedProcedure()),
					interferedState);
		}
		return interferedState;
	}

	private boolean matchesLocation(final GuardedInterferenceDomainState<STATE, ACTION, LOC> singleState,
			final String ownerThread, final String interferenceThreadName,
			final Interference<STATE, ACTION, LOC> interference) {
		final Set<Integer> possibleInterferingLocations = singleState.abstractLocationState().getTracker()
				.getLocationForThread(interferenceThreadName);
		final int interferenceLocation = mAbstractLocationMap.getAbstractLocation(interference.action().getSource());
		if ((!possibleInterferingLocations.contains(interferenceLocation)
				|| !(singleState.threadCounter().getThreadInstances().get(interferenceThreadName) > 0))
				&& !(ownerThread.equals(interferenceThreadName))
				&& !(singleState.threadCounter().getThreadInstances().get(interferenceThreadName) > 1)) {
			return false;
		}
		return true;
	}

	private Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> applyInterferenceToSTATE(
			final Interference<STATE, ACTION, LOC> interference,
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> singleState) {

		final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> statesAfterInterferenceFixpoint = new HashSet<>();
		for (final GuardedInterferenceDomainState<STATE, ACTION, LOC> singleInterferingState : interference.disjState()
				.getStates()) {
			final var unionState = applyInterferenceToSTATEsingle(singleInterferingState, interference.action(),
					singleState);
			var guardedState = new GuardedInterferenceDomainState<STATE, ACTION, LOC>(unionState,
					singleState.threadCounter(), singleState.abstractLocationState());
			guardedState = guardedState.movedTo(interference.action().getPrecedingProcedure(),
					mAbstractLocationMap.getAbstractLocation(interference.action().getTarget()));
			if (guardedState != null && guardedState.state() != null) {
				statesAfterInterferenceFixpoint.add(guardedState);
			}
		}
		return statesAfterInterferenceFixpoint;
	}

	private STATE applyInterferenceToSTATEsingle(
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> singleInterferingState, final ACTION action,
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> singleState) {

		// Add variables to both states to be able to intersect
		STATE interferingState = singleInterferingState.state();
		STATE stateState = singleState.state();
		final var missingLocals = DataStructureUtils.difference(stateState.getVariables(),
				interferingState.getVariables());
		final var missingLocals2 = DataStructureUtils.difference(interferingState.getVariables(),
				stateState.getVariables());
		if (stateState.isBottom() || interferingState.isBottom()) {
			return null;
		}
		if (!missingLocals2.isEmpty()) {
			stateState = stateState.addVariables(missingLocals2);
		}
		if (!missingLocals.isEmpty()) {
			interferingState = interferingState.addVariables(missingLocals);
		}
		final STATE intersectionState = stateState.intersect(interferingState);
		if (intersectionState.isBottom()) {
			return null;
		}
		// postop
		Collection<STATE> postState = mUnderlyingPostOp.apply(intersectionState, action);
		// TODO: sound?
		if (postState.isEmpty()) {
			return null;
		}
		if (!missingLocals2.isEmpty()) {
			postState = postState.stream().map(s -> s.removeVariables(missingLocals2)).collect(Collectors.toList());
		}
		STATE unionState = postState.iterator().next();
		for (final STATE state : postState) {
			if (state != unionState) {
				unionState = unionState.union(state);
			}
		}
		return unionState;
	}
}
