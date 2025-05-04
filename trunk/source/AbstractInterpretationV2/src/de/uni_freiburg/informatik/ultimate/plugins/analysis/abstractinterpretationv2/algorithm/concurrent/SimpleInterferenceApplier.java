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

	// TODO: maybe we want to reduce the potential size of the set we create here. we are not really
	// conforming to the maxSize setting, kind of avoiding it actually.
	public Set<DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>>> applyFixpoint(
			final Set<DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>>> startStates,
			final String ownerThread) {

		final var baseLoc = startStates.iterator().next().getStates().iterator().next().abstractLocationState()
				.getLoc();
		final var result = new LinkedHashSet<>(startStates);
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
					if (statesThatCanBeInterferedbyItf.getStates().isEmpty()) {
						continue;
					}
					final var post = InterferenceApplier.applyInterferenceToSTATEsingle(interference.interf.disjState(),
							interference.interf.action(), statesThatCanBeInterferedbyItf, mPostOp);
					if (post == null) {
						continue;
					}
					// TODO : we cant do this, but maybe after moved ? (we are throwing away interferences which might
					// be a subset in prestate terms, but will expand our state after application
//					if (post.isSubsetOf(statesThatCanBeInterferedbyItf) != SubsetResult.NONE) {
//						continue;
//					}
					final var moved = adjustState(interference, post, baseLoc);
					if (iteration <= mMaxItfIterations) {
						addIfNew(result, nextWorklist, moved);
					} else {
						widenAndAdd(result, nextWorklist, moved);
					}
				}
			}
			if (nextWorklist.isEmpty()) {
				break;
			}
			worklist = new LinkedHashSet<>();
			for (final var s : nextWorklist) {
				worklist.add(GuardedStateTransformer.copyToNewStateLocation(baseLoc, s));
			}
			iteration++;
			if (iteration > 1) {
				break;
			}
		}
		((GuardedInterferenceDomainPostOperator<STATE, ACTION, LOC>) mPostOp).enableInterferences();
		return result;
	}

	private DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> adjustState(
			final InterferenceWithParentThread<STATE, ACTION, LOC> interference,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> post,
			final LOC baseLoc) {
		DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> moved;
		moved = GuardedStateTransformer.movedTo(interference.interf.action().getPrecedingProcedure(),
				mLocMap.getAbstractLocation(interference.interf.action().getTarget()),
				interference.interf.action().getTarget(), post);
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

	private void widenAndAdd(
			final Set<DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>>> result,
			final Set<DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>>> nextWorklist,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> moved) {

		final var widenOp = mGuardedInterferenceDomain.getWideningOperator();
		for (final var existingSet = result.iterator(); existingSet.hasNext();) {
			final var existing = existingSet.next();
			final var widened = existing.widen(widenOp, moved);
			if (!widened.isEqualTo(existing)) {
				existingSet.remove();
				result.add(widened);
				nextWorklist.add(widened);
			}
			return;
		}

		result.add(moved);
		nextWorklist.add(moved);
	}

	public record InterferenceWithParentThread<S extends IAbstractState<S>, A extends IIcfgTransition<L>, L extends IcfgLocation>(
			Interference<S, A, L> interf, String sourceThread) {
	}

	public DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> applyFixpointFlat(
			final Set<DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>>> startStates,
			final String ownerThread) {

		DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> current = DisjunctiveAbstractState
				.createDisjunction(startStates.stream().flatMap(s -> s.getStates().stream()).toList(), mMaxSize);

		final LOC baseLoc = current.getStates().iterator().next().abstractLocationState().getLoc();

		int iteration = 1;
		((GuardedInterferenceDomainPostOperator<STATE, ACTION, LOC>) mPostOp).disAbleInterferences();

		boolean changed;
		do {
			changed = false;

			for (final InterferenceWithParentThread<STATE, ACTION, LOC> interference : mAllInterfs) {

				final var interferable = DisjunctiveAbstractState
						.createDisjunction(
								current.getStates().stream()
										.filter(s -> InterferenceUtils.matchesLocation(s, ownerThread,
												interference.sourceThread(), interference.interf, mLocMap))
										.toList(),
								mMaxSize);

				if (interferable.getStates().isEmpty()) {
					continue;
				}

				final var post = InterferenceApplier.applyInterferenceToSTATEsingle(interference.interf.disjState(),
						interference.interf.action(), interferable, mPostOp);

//				if (post == null || post.isSubsetOf(interferable) != SubsetResult.NONE) {
				if (post == null) {
					continue;
				}

				final var moved = adjustState(interference, post, baseLoc);

				DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> updated;
				if (iteration <= mMaxItfIterations) {
					updated = current.union(moved);
				} else {
					final var widenOp = mGuardedInterferenceDomain.getWideningOperator();
					updated = current.widen(widenOp, moved);
				}

				if (!updated.isEqualTo(current)) {
					current = updated;
					changed = true;
				}
			}
			iteration++;
		} while (changed);

		((GuardedInterferenceDomainPostOperator<STATE, ACTION, LOC>) mPostOp).enableInterferences();
		return current;
	}
}
