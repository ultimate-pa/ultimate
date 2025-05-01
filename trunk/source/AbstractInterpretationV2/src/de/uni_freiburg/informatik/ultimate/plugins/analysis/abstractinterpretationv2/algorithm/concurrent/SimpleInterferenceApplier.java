package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadCurrent;

public class SimpleInterferenceApplier<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {
	private final IAbstractPostOperator<GuardedInterferenceDomainState<STATE, ACTION, LOC>, ACTION> mPostOp;
	private final AbstractLocationMap<LOC> mLocMap;
	private final Set<InterferenceWithParentThread<STATE, ACTION, LOC>> mAllInterfs;
	private final ILogger mLogger;
	private final int mMaxItfIterations;
	private final GuardedInterferenceDomain<STATE, ACTION, LOC> mGuardedInterferenceDomain;
	private final int mMaxSize;

	public SimpleInterferenceApplier(final ILogger logger, final AbstractLocationMap<LOC> locMap,
			final Set<InterferenceWithParentThread<STATE, ACTION, LOC>> interfs, final int maxItf,
			final GuardedInterferenceDomain<STATE, ACTION, LOC> relationalInterferingDomain, final int maxSize) {
		mLogger = logger;
		mLocMap = locMap;
		mGuardedInterferenceDomain = relationalInterferingDomain;
		mPostOp = mGuardedInterferenceDomain.getPostOperator();
		mAllInterfs = interfs;
		mMaxItfIterations = maxItf;
		mMaxSize = maxSize;
	}

	public Set<DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>>> applyFixpoint(
			final Set<DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>>> startStates,
			final String ownerThread) {
		final var startState = startStates.iterator().next();
		final LOC baseLoc = startState.getStates().iterator().next().abstractLocationState().getLoc();
		final Set<DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>>> result = new LinkedHashSet<>(
				startStates);
		LinkedHashSet<DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>>> worklist = new LinkedHashSet<>(
				startStates);

		int iteration = 1;
		((GuardedInterferenceDomainPostOperator<STATE, ACTION, LOC>) mPostOp).disAbleInterferences();
		while (!worklist.isEmpty()) {
			final var nextWorklist = new LinkedHashSet<DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>>>();
			for (final var state : worklist) {
				for (final var interference : mAllInterfs) {
					final var statesThatCanBeInterferedbyItf = DisjunctiveAbstractState.createDisjunction(
							state.getStates().stream()
									.filter(s -> InterferenceUtils.matchesLocation(s, ownerThread,
											interference.sourceThread(), interference.interf, mLocMap))
									.toList(),
							mMaxSize);
					final var post = InterferenceApplier.applyInterferenceToSTATEsingle(interference.interf.disjState(),
							interference.interf.action(), statesThatCanBeInterferedbyItf, mPostOp);
					if (post == null) {
						continue;
					}

					final var moved = adjustState(interference, post, baseLoc);

					if (iteration <= mMaxItfIterations) {
						addIfNew(result, nextWorklist, moved);
					} else {
						widenOrAdd(result, nextWorklist, moved);
					}
				}
			}
			if (nextWorklist.isEmpty()) {
				break;
			}
			final var rebasedWork = new LinkedHashSet<DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>>>();
			for (final var state : nextWorklist) {
				rebasedWork.add(GuardedStateTransformer.copyToNewStateLocation(baseLoc, state));
			}
			worklist = rebasedWork;
//			worklist.addAll(rebasedWork);
			iteration++;
		}
		((GuardedInterferenceDomainPostOperator<STATE, ACTION, LOC>) mPostOp).disAbleInterferences();
		return result;
	}

	private DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> adjustState(
			final InterferenceWithParentThread<STATE, ACTION, LOC> interference,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> post,
			final LOC baseLoc) {
		DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> moved;
		moved = GuardedStateTransformer.movedTo(interference.interf.action().getPrecedingProcedure(),
				mLocMap.getAbstractLocation(interference.interf.action().getTarget()), post);
		if (interference.interf.action() instanceof final ForkThreadCurrent fork) {
			moved = GuardedStateTransformer.setThreadsActive(Set.of(fork.getNameOfForkedProcedure()), moved);
		}
		moved = GuardedStateTransformer.copyToNewStateLocation(baseLoc, moved);
		return moved;
	}

	private void addIfNew(
			final Set<DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>>> result,
			final LinkedHashSet<DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>>> nextWorklist,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> moved) {
		final boolean exists = result.stream().anyMatch(s -> moved.isSubsetOf(s) != SubsetResult.NONE);
		if (!exists) {
			result.add(moved);
			nextWorklist.add(moved);
		}
	}

	private void widenOrAdd(
			final Set<DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>>> result,
			final LinkedHashSet<DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>>> nextWorklist,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> moved) {
		final var widenOp = mGuardedInterferenceDomain.getWideningOperator();
		for (final var existing : result) {
			if (moved.isSubsetOf(existing) != SubsetResult.NONE) {
				return;
			}
		}
		for (final var existing : new LinkedHashSet<>(result)) {
			if (existing.isSubsetOf(moved) != SubsetResult.NONE) {
				final var widened = moved.widen(widenOp, existing);
				if (!widened.isEqualTo(existing)) {
					result.remove(existing);
					result.add(widened);
					nextWorklist.add(widened);
				}
				return;
			}
		}
		result.add(moved);
		nextWorklist.add(moved);
	}

	public record InterferenceWithParentThread<S extends IAbstractState<S>, A extends IIcfgTransition<L>, L extends IcfgLocation>(
			Interference<S, A, L> interf, String sourceThread) {
	}
}
