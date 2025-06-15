package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
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
	private final Map<InterferenceWithSourceThread<STATE, ACTION, LOC>, Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>>> mSeenStatesMap;
	private final IIcfg<?> mCfg;

	public GuardedInterferenceApplier(final IIcfg<?> cfg, final ILogger logger,
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
		mSeenStatesMap = new HashMap<>();
		mCfg = cfg;
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
		mSeenStatesMap.clear();
		for (final var itf : validInterferenceThreadPairs) {
			if (mSeenStatesMap.get(itf) == null) {
				mSeenStatesMap.put(itf, new HashSet<>());
			}
		}
		mAllInterfs = validInterferenceThreadPairs;
		mPostOp = mGuardedInterferenceDomain.getPostOperator();
		return applyFixpointSingle(result, ownerThread);
	}

	private DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> applyFixpointSingle(
			DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> result,
			final String ownerThread) {
		final InterferenceApplier<STATE, ACTION, LOC> itfApplier = new InterferenceApplier<>();
		int iteration = 0;
		boolean changed = true;
		((GuardedInterferenceDomainPostOperator<STATE, ACTION, LOC>) mPostOp).disAbleInterferences();
		while (changed) {
			iteration++;
			if (iteration % 10 == 0) {
				mLogger.warn("High interference-fixpoint iteration:" + iteration);
			}
			final var oldResult = result;
			for (final var interference : mAllInterfs) {
				GuardedInterferenceDomain.totalInnerInterferenceIterations++;
				final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> interferable;
				interferable = result.getStates().stream().filter(s -> !mSeenStatesMap.get(interference).contains(s))
						.filter(s -> mItfUtils.stateIsInterferableBy(s, ownerThread, interference.sourceThread(),
								interference.interf(), mAbstractLocationMap))
						.collect(Collectors.toSet());
				mSeenStatesMap.get(interference).addAll(interferable);
				if (interferable.isEmpty()) {
					continue;
				}
				final var disj = DisjunctiveAbstractState.createDisjunction(interferable, mMaxParallelStates);

				final boolean isSelfInterference = ownerThread.equals(interference.sourceThread());
				final var post = itfApplier.applyInterferenceToDisjState(interference.interf().disjState(),
						interference.interf().action(), disj, mPostOp, mMaxParallelStates, isSelfInterference, mCfg);
				if (post == null) {
					continue;
				}
				var moved = post;

				if (interference.interf().action() instanceof final ForkThreadCurrent fork) {
					moved = GuardedStateTransformer.setThreadsActive(Set.of(fork.getNameOfForkedProcedure()), post);
				}
				if (iteration <= mMaxItf) {
					result = result.union(moved);
				} else {
					result = result.widen(mGuardedInterferenceDomain.getWideningOperator(), moved);
				}
			}
			if (result.isSubsetOf(oldResult).equals(SubsetResult.NONE)) {
				changed = true;
			} else {
				changed = false;
			}
			if (!changed) {
				GuardedInterferenceDomain.maxStatesInOneItf = Math.max(GuardedInterferenceDomain.maxStatesInOneItf,
						result.getStates().size());
				break;
			}
		}
		((GuardedInterferenceDomainPostOperator<STATE, ACTION, LOC>) mPostOp).enableInterferences();
		return result;
	}

}
