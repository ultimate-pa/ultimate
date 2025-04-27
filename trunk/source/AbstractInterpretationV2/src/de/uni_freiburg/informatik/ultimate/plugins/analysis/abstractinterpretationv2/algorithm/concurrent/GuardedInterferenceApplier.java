package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashSet;
import java.util.LinkedHashSet;
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

public class GuardedInterferenceApplier<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {
	private final ILogger mLogger;

	// TODO: Dont widen states which dont need it (dont group-widen)
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

	public record InterferenceWithParentThread<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>(
			Interference<STATE, ACTION, LOC> interf, String sourceThread) {
	}

	public Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> stateAfterInterferences(
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> oldstate, final String ownerThread) {
		initialize();
		final Set<String> possibleInterferenceSet = InterferenceUtils.getThreadsThatCanInterfere(oldstate, ownerThread);
		if (possibleInterferenceSet.isEmpty()) {
			return Set.of(oldstate);
		}
		return interferenceFixpointFast(possibleInterferenceSet, oldstate, ownerThread);
	}

	private void initialize() {
		mIterations = 0;
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

		while (true) {
			final var allInterferences = InterferenceUtils.getValidInterferences(interferingThreads, ownerThread,
					mInterferences, state);
			mIterations++;
			if (mIterations > iterationsReached) {
				iterationsReached = mIterations;
			}

			// state just to check if fixpoint reached after this iteration
			newStates = new HashSet<>();

			for (final GuardedInterferenceDomainState<STATE, ACTION, LOC> singleState : newDisj.getStates()) {
				for (final InterferenceWithParentThread<STATE, ACTION, LOC> interference : allInterferences) {
					if (InterferenceUtils.matchesLocation(singleState, ownerThread, interference.sourceThread(),
							interference.interf(), mAbstractLocationMap)) {
						final var postState = applyInterferenceToSTATE(interference.interf(), singleState);
						if (postState == null) {
							continue;
						}
						// Interferences should not remove/add variables
						assert postState.getVariables().equals(singleState.getVariables());

						newStates.addAll(postState.getStates());
					}
				}
			}
			final var moved = newStates.stream()
					.map(s -> new GuardedInterferenceDomainState<STATE, ACTION, LOC>(s.state(), s.threadCounter(),
							s.abstractLocationState().copyToNewState(state.abstractLocationState().getLoc())))
					.collect(Collectors.toSet());
			oldStates.clear();
			newDisj = DisjunctiveAbstractState.createDisjunction(moved, mMaxParallelStates);
			if (newDisj == null || allDisj == null) {
				continue;
			}
			if (mIterations > mMaxItf) {
//				final var oldState = allDisj;
				final var widenedState = allDisj.widen(mGuardedInterferenceDomain.getWideningOperator(), newDisj);

//				int innerIterations = 0;
//				while (!widenedState.isEqualTo(oldState)) {
//					oldState = widenedState;
//					widenedState = allDisj.widen(mGuardedInterferenceDomain.getWideningOperator(), oldState);
//					innerIterations++;
//					if (innerIterations > mMaxItf) {
//						break;
//					}
//				}
				allDisj = widenedState;
			}

			final boolean changed = newDisj.isSubsetOf(allDisj) != SubsetResult.NONE ? false : true;
			allDisj = allDisj.union(newDisj);
			if (!changed) {
				break;
			}
			oldStates.addAll(newDisj.getStates());
		}
		return allDisj.getStates();
	}

	private DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> applyInterferenceToSTATE(
			final Interference<STATE, ACTION, LOC> interference,
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> singleState) {

		final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> statesAfterInterferenceFixpoint = new HashSet<>();
		for (final GuardedInterferenceDomainState<STATE, ACTION, LOC> singleInterferingState : interference.disjState()
				.getStates()) {
			final var unionState = InterferenceApplier.applyInterferenceToSTATEsingle(singleInterferingState,
					interference.action(), singleState, mUnderlyingPostOp);
			var guardedState = new GuardedInterferenceDomainState<STATE, ACTION, LOC>(unionState,
					singleState.threadCounter(), singleState.abstractLocationState());
			guardedState = guardedState.movedTo(interference.action().getPrecedingProcedure(),
					mAbstractLocationMap.getAbstractLocation(interference.action().getTarget()));
			if (guardedState != null && guardedState.state() != null) {
				statesAfterInterferenceFixpoint.add(guardedState);
			}
		}
		var interferedState = DisjunctiveAbstractState.createDisjunction(statesAfterInterferenceFixpoint,
				mMaxParallelStates);

		// in case of interfering fork, update threadcounter and location
		if (interferedState != null && interference.action() instanceof final ForkThreadCurrent fork) {
			interferedState = GuardedStateTransformer.setThreadsActive(Set.of(fork.getNameOfForkedProcedure()),
					interferedState);
		}
		return interferedState;
	}
}