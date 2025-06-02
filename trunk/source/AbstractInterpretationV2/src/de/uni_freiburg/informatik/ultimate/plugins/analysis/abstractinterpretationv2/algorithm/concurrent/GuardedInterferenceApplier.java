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
	private final GuardedInterferenceDomain<STATE, ACTION, LOC> mGuardedInterferenceDomain;
	private final AbstractLocationMap<LOC> mAbstractLocationMap;
	private final int mMaxItf;
	private final int mMaxParallelStates;
	private final AbstractInterferenceState<STATE, ACTION, LOC> mInterferences;
	private final InterferenceUtils<STATE, ACTION, LOC> mItfUtils;

	public static int iterationsReached = 0;
	private Set<InterferenceWithSourceThread<STATE, ACTION, LOC>> mAllInterfs;
	private IAbstractPostOperator<GuardedInterferenceDomainState<STATE, ACTION, LOC>, ACTION> mPostOp;

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
		// TODO: why needed
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

	private DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> applyFixpointSingle(
			final Set<DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>>> startStates,
			final String ownerThread) {
		final InterferenceApplier<STATE, ACTION, LOC> itfApplier = new InterferenceApplier<>();
		final var result = new LinkedHashSet<>(startStates.stream().flatMap(s -> s.getStates().stream()).toList());
		LinkedHashSet<GuardedInterferenceDomainState<STATE, ACTION, LOC>> worklist = new LinkedHashSet<>(result);
		int iteration = 1;
		((GuardedInterferenceDomainPostOperator<STATE, ACTION, LOC>) mPostOp).disAbleInterferences();
		while (!worklist.isEmpty()) {
			final LinkedHashSet<GuardedInterferenceDomainState<STATE, ACTION, LOC>> nextWorklist = new LinkedHashSet<>();
			for (final var interference : mAllInterfs) {
				GuardedInterferenceDomain.totalInnerInterferenceIterations++;
				final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> interferable;
				interferable = worklist
						.stream().filter(s -> mItfUtils.stateIsInterferableBy(s, ownerThread,
								interference.sourceThread(), interference.interf(), mAbstractLocationMap))
						.collect(Collectors.toSet());
				if (interferable.isEmpty()) {
					continue;
				}
				final var disj = DisjunctiveAbstractState.createDisjunction(interferable, mMaxParallelStates);

				final var post = itfApplier.applyInterferenceToDisjState(interference.interf().disjState(),
						interference.interf().action(), disj, mPostOp, mMaxParallelStates);
				if (post == null) {
					continue;
				}
				var moved = post;

				if (interference.interf().action() instanceof final ForkThreadCurrent fork) {
					moved = GuardedStateTransformer.setThreadsActive(Set.of(fork.getNameOfForkedProcedure()), post);
				}
				if (iteration <= mMaxItf) {
					addIfNew(result, nextWorklist, moved.getStates());
				} else {
					widenAndAddIfNew(result, nextWorklist, moved.getStates());
				}
			}
			if (nextWorklist.isEmpty()) {
				GuardedInterferenceDomain.maxStatesInOneItf = Math.max(GuardedInterferenceDomain.maxStatesInOneItf,
						result.size());
				break;
			}
			worklist = nextWorklist;
			iteration++;
			if (iteration % 10 == 0) {
				mLogger.warn("High interference-fixpoint iteration:" + iteration);
			}
		}
		((GuardedInterferenceDomainPostOperator<STATE, ACTION, LOC>) mPostOp).enableInterferences();
		final var resultDisj = DisjunctiveAbstractState.createDisjunction(result, mMaxParallelStates);
		return resultDisj;
	}

	private void addIfNew(final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> result,
			final LinkedHashSet<GuardedInterferenceDomainState<STATE, ACTION, LOC>> nextWorklist,
			final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> moved) {

		for (final var potentialNewState : moved) {
			boolean subsumedByExisting = false;
			final Iterator<GuardedInterferenceDomainState<STATE, ACTION, LOC>> it = result.iterator();
			while (it.hasNext()) {
				final var existing = it.next();
				final SubsetResult subsetRes = potentialNewState.isSubsetOf(existing);
				if (!(subsetRes == SubsetResult.NONE)) {
					subsumedByExisting = true;
					break;
				}
				final SubsetResult reverseSubsetRes = existing.isSubsetOf(potentialNewState);
				if (reverseSubsetRes == SubsetResult.STRICT) {
					it.remove();
				}
			}
			if (!subsumedByExisting) {
				result.add(potentialNewState);
				nextWorklist.add(potentialNewState);
			}
		}
	}

	private void widenAndAddIfNew(final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> result,
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
