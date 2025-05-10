package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

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

	public DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> applyFixpointDisj(
			final Set<DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>>> startStates,
			final String ownerThread) {

		DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> current = DisjunctiveAbstractState
				.createDisjunction(startStates.stream().flatMap(s -> s.getStates().stream()).toList(), mMaxSize);
		final LOC baseLoc = current.getStates().iterator().next().abstractLocationState().getLoc();
		int iteration = 1;
		((GuardedInterferenceDomainPostOperator<STATE, ACTION, LOC>) mPostOp).disAbleInterferences();
		boolean changed;
		do {
//			mLogger.warn("iteration: " + iteration);
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
						interference.interf.action(), interferable, mPostOp, mMaxSize);
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
				updated = StateReducer.reduceToLocations(updated, mMaxSize);
			}
			iteration++;
		} while (changed);

		((GuardedInterferenceDomainPostOperator<STATE, ACTION, LOC>) mPostOp).enableInterferences();
		return current;
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

	private Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> adjustState(
			final InterferenceWithParentThread<STATE, ACTION, LOC> interference,
			final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> post, final LOC baseLoc) {
		Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> moved;
		moved = post.stream()
				.map(s -> s.movedTo(interference.interf.action().getPrecedingProcedure(),
						mLocMap.getAbstractLocation(interference.interf.action().getTarget()),
						interference.interf.action().getTarget()))
				.collect(Collectors.toSet());
		if (interference.interf.action() instanceof final ForkThreadCurrent fork) {
			moved = moved.stream().map(s -> s.setThreadsActive(Set.of(fork.getNameOfForkedProcedure())))
					.collect(Collectors.toSet());
		}
		moved = moved.stream().map(s -> s.copyToNewStateLocation(baseLoc)).collect(Collectors.toSet());
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

	private void addIfNew(final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> result,
			final LinkedHashSet<GuardedInterferenceDomainState<STATE, ACTION, LOC>> nextWorklist,
			final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> moved) {

		for (final GuardedInterferenceDomainState<STATE, ACTION, LOC> single : moved) {

			boolean subsumedByExisting = false;
			final Iterator<GuardedInterferenceDomainState<STATE, ACTION, LOC>> it = result.iterator();

			while (it.hasNext()) {
				final GuardedInterferenceDomainState<STATE, ACTION, LOC> existing = it.next();
				final SubsetResult subsetRes = single.isSubsetOf(existing);
				if (subsetRes == SubsetResult.EQUAL || subsetRes == SubsetResult.NON_STRICT || subsetRes == SubsetResult.STRICT) {
					subsumedByExisting = true;
					break;
				}

				final SubsetResult dir2 = existing.isSubsetOf(single);
				if (dir2 == SubsetResult.STRICT) {
					it.remove();
				}
			}

			if (!subsumedByExisting) {
				result.add(single);
				nextWorklist.add(single);
			}
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

	private void widenAndAdd(final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> result,
			final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> nextWorklist,
			final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> moved) {

		final var widenOp = mGuardedInterferenceDomain.getWideningOperator();

		for (final GuardedInterferenceDomainState<STATE, ACTION, LOC> cand0 : moved) {
			GuardedInterferenceDomainState<STATE, ACTION, LOC> cand = cand0;
			boolean changed;

			do {
				changed = false;
				for (final var it = result.iterator(); it.hasNext();) {
					final var existing = it.next();
					final var widened = widenOp.apply(existing, cand);
					if (!widened.isEqualTo(existing)) {
						it.remove();
						cand = widened;
						changed = true;
						break;
					}

					final SubsetResult subsetRes = cand.isSubsetOf(existing);
					if (subsetRes == SubsetResult.EQUAL || subsetRes == SubsetResult.NON_STRICT || subsetRes == SubsetResult.STRICT) {
						cand = null;
						break;
					}

					if (existing.isSubsetOf(cand) == SubsetResult.STRICT) {
						it.remove();
						changed = true;
					}
				}
			} while (changed && cand != null);

			if (cand != null) {
				result.add(cand);
				nextWorklist.add(cand);
			}
		}
	}

	public record InterferenceWithParentThread<S extends IAbstractState<S>, A extends IIcfgTransition<L>, L extends IcfgLocation>(
			Interference<S, A, L> interf, String sourceThread) {
	}

	public DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> applyFixpoint(
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
//			mLogger.warn("states: " + worklist.size());
			for (final var state : worklist) {
//				mLogger.warn("iteration: " + iteration);
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
							interference.interf.action(), statesThatCanBeInterferedbyItf, mPostOp, mMaxSize);
					if (post == null) {
						continue;
					}
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
			for (var s : nextWorklist) {
				s = StateReducer.reduceToLocations(s, mMaxSize);
				worklist.add(GuardedStateTransformer.copyToNewStateLocation(baseLoc, s));
			}
			iteration++;
		}
		((GuardedInterferenceDomainPostOperator<STATE, ACTION, LOC>) mPostOp).enableInterferences();
		final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> reduced = DisjunctiveAbstractState
				.createDisjunction(result.stream().flatMap(s -> s.getStates().stream()).toList(), mMaxSize);
		return StateReducer.reduceToLocations(reduced, mMaxSize);
	}

	public DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> applyFixpointSingle(
			final Set<DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>>> startStates,
			final String ownerThread) {

		final LOC baseLoc = startStates.iterator().next().getStates().iterator().next().abstractLocationState()
				.getLoc();
		final var result = new LinkedHashSet<>(startStates.stream().flatMap(s -> s.getStates().stream()).toList());
		LinkedHashSet<GuardedInterferenceDomainState<STATE, ACTION, LOC>> worklist = new LinkedHashSet<>(result);
		int iteration = 1;
		((GuardedInterferenceDomainPostOperator<STATE, ACTION, LOC>) mPostOp).disAbleInterferences();

		while (!worklist.isEmpty()) {

			final LinkedHashSet<GuardedInterferenceDomainState<STATE, ACTION, LOC>> nextWorklist = new LinkedHashSet<>();
			for (final var interference : mAllInterfs) {

				// todo: why less precise with just worklist stream ? If we hash it shouldnt matter though
//				final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> interferable = worklist.stream()
//						.filter(s -> InterferenceUtils.matchesLocation(s, ownerThread, interference.sourceThread(),
//								interference.interf, mLocMap))
//						.collect(Collectors.toSet());
				final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> interferable = Stream
						.concat(worklist.stream(), result.stream()).filter(s -> InterferenceUtils.matchesLocation(s,
								ownerThread, interference.sourceThread(), interference.interf, mLocMap))
						.collect(Collectors.toSet());

				if (interferable.isEmpty()) {
					continue;
				}
				final var disj = DisjunctiveAbstractState.createDisjunction(interferable, mMaxSize);
//				final var postSet = disj.getStates().stream()
//						.flatMap(s -> Optional
//								.ofNullable(InterferenceApplier.applyInterferenceToSTATEsingle(
//										interference.interf.disjState(), interference.interf.action(), s, mPostOp))
//								.stream().flatMap(Collection::stream))
//						.collect(Collectors.toSet());
//				final var post = DisjunctiveAbstractState.createDisjunction(postSet, mMaxSize);
				final var post = InterferenceApplier.applyInterferenceToSTATEsingle(interference.interf.disjState(),
						interference.interf.action(), disj, mPostOp, mMaxSize);
				if (post == null) {
					continue;
				}
				final var moved = adjustState(interference, post, baseLoc);
				if (iteration <= mMaxItfIterations) {
					addIfNew(result, nextWorklist, moved.getStates());
				} else {
					widenAndAdd(result, nextWorklist, moved.getStates());
				}
			}

			if (nextWorklist.isEmpty()) {
				break;
			}
			worklist = nextWorklist.stream().map(s -> s.copyToNewStateLocation(baseLoc))
					.collect(Collectors.toCollection(LinkedHashSet::new));

			iteration++;

			if (iteration > 8) {
				mLogger.warn(iteration);

			}
		}

		((GuardedInterferenceDomainPostOperator<STATE, ACTION, LOC>) mPostOp).enableInterferences();
//		result = StateReducer.reduceToLocationsSet(result, mMaxSize);
		final var reduced = DisjunctiveAbstractState.createDisjunction(result, mMaxSize);
//		return StateReducer.reduceToLocations(reduced, mMaxSize);
		return reduced;
	}
}
