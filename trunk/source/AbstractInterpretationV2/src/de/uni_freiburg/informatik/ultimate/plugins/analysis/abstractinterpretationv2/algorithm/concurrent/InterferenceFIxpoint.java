package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class InterferenceFIxpoint<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {

	private final ILogger mLogger;
	private final InterferenceDomain<STATE, ACTION, LOC> mGuardedInterferenceDomain;
	private final StaticAbstractLocationMap<LOC> mAbstractLocationMap;
	private final int mMaxItf;
	private final int mMaxParallelStates;
	private final AbstractInterferenceState<STATE, ACTION, LOC> mInterferences;
	private final InterferenceUtils<STATE, ACTION, LOC> mItfUtils;

	private Set<InterferenceWithSourceThread<STATE, ACTION, LOC>> mAllInterfs;
	private InterferenceDomainPostOperator<STATE, ACTION, LOC> mPostOp;
	private final Map<InterferenceWithSourceThread<STATE, ACTION, LOC>, Set<InterferenceDomainState<STATE, ACTION, LOC>>> mSeenStatesMap;
	private final IIcfg<?> mCfg;

	public InterferenceFIxpoint(final IIcfg<?> cfg, final ILogger logger,
			final InterferenceDomain<STATE, ACTION, LOC> relationalInterferingDomain,
			final StaticAbstractLocationMap<LOC> globalMap, final int maxItf, final int maxParallelStates,
			final AbstractInterferenceState<STATE, ACTION, LOC> interferences) {
		mLogger = logger;
		mGuardedInterferenceDomain = relationalInterferingDomain;
		mInterferences = interferences;
		mAbstractLocationMap = globalMap;
		mMaxItf = maxItf;
		mMaxParallelStates = maxParallelStates;
		mPostOp = (InterferenceDomainPostOperator<STATE, ACTION, LOC>) mGuardedInterferenceDomain.getPostOperator();
		mAllInterfs = new HashSet<>();
		mItfUtils = new InterferenceUtils<>();
		mSeenStatesMap = new HashMap<>();
		mCfg = cfg;
	}

	public DisjunctiveAbstractState<InterferenceDomainState<STATE, ACTION, LOC>> computeInterferenceFixpoint(
			final DisjunctiveAbstractState<InterferenceDomainState<STATE, ACTION, LOC>> result,
			final String ownerThread, final InterferenceCache<STATE, ACTION, LOC> cache) {
		if (!prepareAndFilterItfs(result, ownerThread)) {
			return result;
		}

		return applyFixpoint(result, ownerThread, cache);
	}

	private boolean prepareAndFilterItfs(
			final DisjunctiveAbstractState<InterferenceDomainState<STATE, ACTION, LOC>> result,
			final String ownerThread) {
		if (result.getStates().isEmpty()) {
			return false;
		}
		final var validInterferenceThreadPairs = mItfUtils.createValidInterferenceThreadPairs(ownerThread,
				mInterferences, result);
		if (validInterferenceThreadPairs.isEmpty()) {
			return false;
		}
		mSeenStatesMap.clear();
		for (final var itf : validInterferenceThreadPairs) {
			if (mSeenStatesMap.get(itf) == null) {
				mSeenStatesMap.put(itf, new HashSet<>());
			}
		}
		mAllInterfs = validInterferenceThreadPairs;
		mPostOp = (InterferenceDomainPostOperator<STATE, ACTION, LOC>) mGuardedInterferenceDomain.getPostOperator();
		return true;
	}

	private DisjunctiveAbstractState<InterferenceDomainState<STATE, ACTION, LOC>> applyFixpoint(
			DisjunctiveAbstractState<InterferenceDomainState<STATE, ACTION, LOC>> result, final String ownerThread,
			final InterferenceCache<STATE, ACTION, LOC> cache) {
		final InterferenceApplier<STATE, ACTION, LOC> itfApplier = new InterferenceApplier<>(cache);
		int iteration = 0;
		boolean changed = true;
		while (changed) {
			iteration++;
			if (iteration % 10 == 0) {
				mLogger.warn("High interference-fixpoint iteration:" + iteration);
			}
			final var oldResult = result;
			for (final var interference : mAllInterfs) {
				InterferenceDomain.totalInnerInterferenceIterations++;
				final Set<InterferenceDomainState<STATE, ACTION, LOC>> interferable;
				interferable = result.getStates().stream().filter(s -> !mSeenStatesMap.get(interference).contains(s))
						.filter(s -> mItfUtils.stateIsInterferableBy(s, ownerThread, interference.sourceThread(),
								interference.interf(), mAbstractLocationMap))
						.collect(Collectors.toSet());
				mSeenStatesMap.get(interference).addAll(interferable);
				if (interferable.isEmpty()) {
					continue;
				}

				final boolean isSelfInterference = ownerThread.equals(interference.sourceThread());

				final Set<InterferenceDomainState<STATE, ACTION, LOC>> resultSet = new HashSet<>();
				for (final InterferenceDomainState<STATE, ACTION, LOC> single : interferable) {
					final var singlepost = itfApplier.applyInterferenceToState(interference.interf().preState(),
							interference.interf().action(), single, mPostOp, isSelfInterference, mCfg);
					resultSet.addAll(singlepost);
				}

				if (resultSet.isEmpty()) {
					continue;
				}
				final var post = DisjunctiveAbstractState.createDisjunction(resultSet, mMaxParallelStates);

				final var moved = post;

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
				InterferenceDomain.maxStatesInOneItf = Math.max(InterferenceDomain.maxStatesInOneItf,
						result.getStates().size());
				break;
			}
		}
		return result;
	}

}
