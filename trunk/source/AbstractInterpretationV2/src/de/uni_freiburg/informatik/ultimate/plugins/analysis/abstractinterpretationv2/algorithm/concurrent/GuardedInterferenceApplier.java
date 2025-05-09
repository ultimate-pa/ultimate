package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

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

	public DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> stateAfterInterferences(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> result,
			final String ownerThread) {
		final Set<String> possibleInterferenceSet = InterferenceUtils.getThreadsThatCanInterfere(result, ownerThread);
		if (possibleInterferenceSet.isEmpty()) {
			return result;
		}
		final var allInterferences = InterferenceUtils.getValidInterferences(possibleInterferenceSet, ownerThread,
				mInterferences, result);
		final var mSimple = new SimpleInterferenceApplier<>(mLogger, mAbstractLocationMap, allInterferences, mMaxItf,
				mGuardedInterferenceDomain, mMaxParallelStates);
		final int method = 0;
		return switch (method) {
		case 0 -> mSimple.applyFixpointSingle(Set.of(result), ownerThread);
		case 1 -> mSimple.applyFixpoint(Set.of(result), ownerThread);
		default -> mSimple.applyFixpointDisj(Set.of(result), ownerThread);
		};
	}

}