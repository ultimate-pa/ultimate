package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashSet;
import java.util.Iterator;
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
	private final GuardedInterferenceDomain<STATE, ACTION, LOC> mGuardedInterferenceDomain;
	private final AbstractLocationMap<LOC> mAbstractLocationMap;
	private final int mMaxItf;
	private final int mMaxParallelStates;
	public static int iterationsReached = 0;

	private final AbstractInterferenceState<STATE, ACTION, LOC> mInterferences;
	private final InterferenceUtils<STATE, ACTION, LOC> mItfUtils;

	private IAbstractPostOperator<GuardedInterferenceDomainState<STATE, ACTION, LOC>, ACTION> mPostOp;
	private Set<InterferenceWithSourceThread<STATE, ACTION, LOC>> mAllInterfs;

	public GuardedInterferenceApplier(final ILogger logger, final IAbstractPostOperator<STATE, ACTION> postOp,
			final GuardedInterferenceDomain<STATE, ACTION, LOC> relationalInterferingDomain,
			final AbstractLocationMap<LOC> globalMap, final int maxItf, final int maxParallelStates,
			final AbstractInterferenceState<STATE, ACTION, LOC> interferences) {
		mLogger = logger;
		mGuardedInterferenceDomain = relationalInterferingDomain;
		mInterferences = interferences;
		mAbstractLocationMap = globalMap;
		mMaxItf = maxItf;
		mMaxParallelStates = maxParallelStates;
		iterationsReached = 0;
		mPostOp = mGuardedInterferenceDomain.getPostOperator();
		mAllInterfs = new HashSet<>();
		mItfUtils = new InterferenceUtils<>();
	}

	public DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> stateAfterInterferences(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> result,
			final String ownerThread) {
		if (result.getStates().isEmpty()) {
			return result;
		}
		final var validInterferenceThreadPairs = mItfUtils.createValidInterferenceThreadPairs(ownerThread,
				mInterferences, result);
		if (validInterferenceThreadPairs.isEmpty()) {
			return result;
		}
		mAllInterfs = validInterferenceThreadPairs;
		mPostOp = mGuardedInterferenceDomain.getPostOperator();
		return applyFixpointSingle(Set.of(result), ownerThread);
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
				GuardedInterferenceDomain.totalInnerInterferenceIterations++;
				final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> interferable;
				// todo: why less precise with just worklist stream ? If we hash it shouldnt matter though
				interferable = worklist
						.stream().filter(s -> mItfUtils.stateIsInterferableBy(s, ownerThread,
								interference.sourceThread(), interference.interf(), mAbstractLocationMap))
						.collect(Collectors.toSet());
				if (interferable.isEmpty()) {
					continue;
				}
				final var disj = DisjunctiveAbstractState.createDisjunction(interferable, mMaxParallelStates);
				final var post = InterferenceApplier.applyInterferenceToSTATEsingle(interference.interf().disjState(),
						interference.interf().action(), disj, mPostOp, mMaxParallelStates);
				if (post == null) {
					continue;
				}
				final var moved = adjustState(interference, post, baseLoc);
				if (iteration <= mMaxItf) {
					addIfNew(result, nextWorklist, moved.getStates());
				} else {
					widenAndAdd(result, nextWorklist, moved.getStates());
				}
			}
			if (nextWorklist.isEmpty()) {
				GuardedInterferenceDomain.maxStatesInOneItf = Math.max(GuardedInterferenceDomain.maxStatesInOneItf,
						result.size());
				break;
			}
			worklist = nextWorklist.stream().map(s -> s.copyToNewStateLocation(baseLoc))
					.collect(Collectors.toCollection(LinkedHashSet::new));
			iteration++;
			if (iteration % 10 == 0) {
				mLogger.warn("High interference-fixpoint iteration:" + iteration);
			}
		}
		((GuardedInterferenceDomainPostOperator<STATE, ACTION, LOC>) mPostOp).enableInterferences();
//		if (mReductionMethod.equals("Reduce per location")) {
//			result = StateReducer.reduceToLocationsSet(result, mMaxParallelStates);
//			final var reduced = DisjunctiveAbstractState.createDisjunction(result, mMaxParallelStates);
//			return StateReducer.reduceToLocations(reduced, mMaxParallelStates);
//
//		}
		final var reduced = DisjunctiveAbstractState.createDisjunction(result, mMaxParallelStates);
		return reduced;
	}

	private DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> adjustState(
			final InterferenceWithSourceThread<STATE, ACTION, LOC> interference,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> post,
			final LOC baseLoc) {
		DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> moved;
		moved = GuardedStateTransformer.movedTo(interference.interf().action().getPrecedingProcedure(),
				mAbstractLocationMap.getAbstractLocation(interference.interf().action().getTarget()),
				interference.interf().action().getTarget(), post);
		if (interference.interf().action() instanceof final ForkThreadCurrent fork) {
			moved = GuardedStateTransformer.setThreadsActive(Set.of(fork.getNameOfForkedProcedure()), moved);
		}
		moved = GuardedStateTransformer.copyToNewStateLocation(baseLoc, moved);
		return moved;
	}

	private void addIfNew(final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> result,
			final LinkedHashSet<GuardedInterferenceDomainState<STATE, ACTION, LOC>> nextWorklist,
			final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> moved) {

		for (final GuardedInterferenceDomainState<STATE, ACTION, LOC> potentialNewState : moved) {
			boolean subsumedByExisting = false;
			final Iterator<GuardedInterferenceDomainState<STATE, ACTION, LOC>> it = result.iterator();
			while (it.hasNext()) {
				final GuardedInterferenceDomainState<STATE, ACTION, LOC> existing = it.next();
				final SubsetResult subsetRes = potentialNewState.isSubsetOf(existing);
				if (!(subsetRes == SubsetResult.NONE)) {
					subsumedByExisting = true;
					break;
				}
				final SubsetResult dir2 = existing.isSubsetOf(potentialNewState);
				if (dir2 == SubsetResult.STRICT) {
					it.remove();
				}
			}
			if (!subsumedByExisting) {
				result.add(potentialNewState);
				nextWorklist.add(potentialNewState);
			}
		}
	}

	private void widenAndAdd(final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> result,
			final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> nextWorklist,
			final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> moved) {
		final var widenOp = mGuardedInterferenceDomain.getWideningOperator();
		for (GuardedInterferenceDomainState<STATE, ACTION, LOC> potentialNewState : moved) {
			boolean changed = true;

			while (changed && potentialNewState != null) {
				changed = false;
				for (final var it = result.iterator(); it.hasNext();) {
					final var existing = it.next();
					final var widened = widenOp.apply(existing, potentialNewState);
					if (!widened.isEqualTo(existing)) {
						it.remove();
						potentialNewState = widened;
						changed = true;
						break;
					}
					final SubsetResult subsetRes = potentialNewState.isSubsetOf(existing);
					// useless new state, throw away
					if (!(subsetRes == SubsetResult.NONE)) {
						potentialNewState = null;
						break;
					}
					if (existing.isSubsetOf(potentialNewState) == SubsetResult.STRICT) {
						it.remove();
						changed = true;
					}
				}
			}
			if (potentialNewState != null) {
				result.add(potentialNewState);
				nextWorklist.add(potentialNewState);
			}
		}
	}

}