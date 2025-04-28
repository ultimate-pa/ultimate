package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadCurrent;

public class SimpleInterferenceApplier<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {
	private final IAbstractPostOperator<STATE, ACTION> mPostOp;
	private final AbstractLocationMap<LOC> mLocMap;
	private final Set<InterferenceWithParentThread<STATE, ACTION, LOC>> mAllInterfs;
	private final ILogger mLogger;
	private final int mMaxInterferences;
	private final GuardedInterferenceDomain<STATE, ACTION, LOC> mGuardedInterferenceDomain;

	public SimpleInterferenceApplier(final ILogger logger, final IAbstractPostOperator<STATE, ACTION> postOp,
			final AbstractLocationMap<LOC> locMap, final Set<InterferenceWithParentThread<STATE, ACTION, LOC>> interfs,
			final int maxItf, final GuardedInterferenceDomain<STATE, ACTION, LOC> relationalInterferingDomain) {
		mLogger = logger;
		mPostOp = postOp;
		mLocMap = locMap;
		mAllInterfs = interfs;
		mMaxInterferences = maxItf;
		mGuardedInterferenceDomain = relationalInterferingDomain;
	}

	public Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> applyFixpoint(
			final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> startStates, final String ownerThread) {
		final var startState = startStates.iterator().next();
		final LOC baseLoc = startState.abstractLocationState().getLoc();
		final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> result = new LinkedHashSet<>(startStates);
		final LinkedHashSet<GuardedInterferenceDomainState<STATE, ACTION, LOC>> worklist = new LinkedHashSet<>(
				startStates);

		int iteration = 1;
		while (!worklist.isEmpty()) {
			final var nextWorklist = new LinkedHashSet<GuardedInterferenceDomainState<STATE, ACTION, LOC>>();
			for (final var state : worklist) {
				for (final var interference : mAllInterfs) {
					if (!InterferenceUtils.matchesLocation(state, ownerThread, interference.sourceThread(),
							interference.interf, mLocMap)) {
						continue;
					}
					for (final var src : interference.interf.disjState().getStates()) {
						final var post = InterferenceApplier.applyInterferenceToSTATEsingle(src,
								interference.interf.action(), state, mPostOp);
						if (post == null) {
							continue;
						}

						final GuardedInterferenceDomainState<STATE, ACTION, LOC> moved = adjustState(state,
								interference, post, baseLoc);

						if (iteration <= mMaxInterferences) {
							addIfNew(result, nextWorklist, moved);
						} else {
							widenOrAdd(result, nextWorklist, moved);
						}
					}
				}
			}
			if (nextWorklist.isEmpty()) {
				break;
			}
			final var rebasedWork = new LinkedHashSet<GuardedInterferenceDomainState<STATE, ACTION, LOC>>();
			for (final var state : nextWorklist) {
				rebasedWork.add(new GuardedInterferenceDomainState<>(state.state(), state.threadCounter(),
						state.abstractLocationState().copyToNewState(baseLoc)));
			}
//			worklist = rebasedWork;
			worklist.addAll(rebasedWork);
			iteration++;
		}
		return result;
	}

	private GuardedInterferenceDomainState<STATE, ACTION, LOC> adjustState(
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> state,
			final InterferenceWithParentThread<STATE, ACTION, LOC> interference, final STATE post, final LOC baseLoc) {
		GuardedInterferenceDomainState<STATE, ACTION, LOC> moved;
		if (interference.interf.action() instanceof final ForkThreadCurrent fork) {
			moved = new GuardedInterferenceDomainState<STATE, ACTION, LOC>(post, state.threadCounter(),
					state.abstractLocationState())
					.movedTo(interference.interf.action().getPrecedingProcedure(),
							mLocMap.getAbstractLocation(interference.interf.action().getTarget()))
					.setThreadsActive(Set.of(fork.getNameOfForkedProcedure()));
		} else {
			moved = new GuardedInterferenceDomainState<STATE, ACTION, LOC>(post, state.threadCounter(),
					state.abstractLocationState()).movedTo(interference.interf.action().getPrecedingProcedure(),
							mLocMap.getAbstractLocation(interference.interf.action().getTarget()));
		}
		moved = new GuardedInterferenceDomainState<>(moved.state(), moved.threadCounter(),
				moved.abstractLocationState().copyToNewState(baseLoc));
		return moved;
	}

	private void addIfNew(final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> result,
			final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> nextWork,
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> moved) {
		final boolean exists = result.stream()
				.anyMatch(s -> moved.state().isSubsetOf(s.state()) != SubsetResult.NONE
						&& s.threadCounter().equals(moved.threadCounter())
						&& s.abstractLocationState().equals(moved.abstractLocationState()));
		if (!exists) {
			result.add(moved);
			nextWork.add(moved);
		}
	}

	private void widenOrAdd(final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> result,
			final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> nextWork,
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> moved) {
		final var widenOp = mGuardedInterferenceDomain.getUnderlyingDomain().getWideningOperator();
		for (final var existing : new LinkedHashSet<>(result)) {
			if (existing.threadCounter().equals(moved.threadCounter())
					&& existing.abstractLocationState().equals(moved.abstractLocationState())) {
				final var widened = widenOp.apply(existing.state(), moved.state());
				if (!widened.isEqualTo(existing.state())) {
					final var newState = new GuardedInterferenceDomainState<STATE, ACTION, LOC>(widened,
							existing.threadCounter(), existing.abstractLocationState());
					result.remove(existing);
					result.add(newState);
					nextWork.add(newState);
				}
				return;
			}
		}
		result.add(moved);
		nextWork.add(moved);
	}

	public record InterferenceWithParentThread<S extends IAbstractState<S>, A extends IIcfgTransition<L>, L extends IcfgLocation>(
			Interference<S, A, L> interf, String sourceThread) {
	}
}
