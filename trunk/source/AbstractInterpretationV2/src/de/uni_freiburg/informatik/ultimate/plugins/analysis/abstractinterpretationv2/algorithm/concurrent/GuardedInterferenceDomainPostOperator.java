package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadCurrent;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadOther;

public class GuardedInterferenceDomainPostOperator<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>
		implements IAbstractPostOperator<GuardedInterferenceDomainState<STATE, ACTION, LOC>, ACTION> {

	private final ILogger mLogger;

	private String mCurrentThreadName;
	private final IAbstractPostOperator<STATE, ACTION> mUnderlyingPostOp;
	private final GuardedInterferenceApplier<STATE, ACTION, LOC> mItfApplier;
	private final Set<IIcfgForkTransitionThreadCurrent<IcfgLocation>> mforksInLoop;

	private final int mMaxParallelStates;
	private boolean mApplyInterferences = true;
	private final GuardedInterferenceCache<STATE, ACTION, LOC> mCache;

	public GuardedInterferenceDomainPostOperator(final IIcfg<?> cfg, final ILogger logger,
			final IAbstractPostOperator<STATE, ACTION> postOp,
			final GuardedInterferenceDomain<STATE, ACTION, LOC> relationalInterferingDomain,
			final AbstractLocationMap<LOC> globalMap, final int maxItf, final int maxParallelStates,
			final AbstractInterferenceState<STATE, ACTION, LOC> interferences,
			final GuardedInterferenceCache<STATE, ACTION, LOC> cache) {
		mLogger = logger;
		mUnderlyingPostOp = postOp;
		mItfApplier = new GuardedInterferenceApplier<>(cfg, logger, relationalInterferingDomain, globalMap, maxItf,
				maxParallelStates, interferences, cache);
		mforksInLoop = IcfgUtils.getForksInLoop(cfg);
		mMaxParallelStates = maxParallelStates;
		mCache = cache;
	}

	public GuardedInterferenceApplier<STATE, ACTION, LOC> getItfApplier() {
		return mItfApplier;
	}

	public void disAbleInterferences() {
		mApplyInterferences = false;
	}

	public void enableInterferences() {
		mApplyInterferences = true;
	}

	@Override
	public Collection<GuardedInterferenceDomainState<STATE, ACTION, LOC>> apply(
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> oldstate, final ACTION transition) {
//		mLogger.warn("=====");
//		mLogger.warn("Postop:");
//		mLogger.warn("thread:" + transition.getPrecedingProcedure());
//		mLogger.warn("node:" + transition.getSource());
//		mLogger.warn("node:" + transition.getTransformula());
		if (oldstate.isStateBottom()) {
			return List.of(oldstate);
		}
		mCurrentThreadName = transition.getPrecedingProcedure();

		// handle fork differently
		final var newState = (transition instanceof ForkThreadCurrent || transition instanceof ForkThreadOther)
				? applyFork(oldstate, transition)
				: oldstate;

		// 1. normal poststate
//		mLogger.warn("calculating Postop:");
		final var states = mUnderlyingPostOp.apply(newState.state(), transition);
//		mLogger.warn("finished Postop:");

		// adjust abstract location according to new location
		final var guardedStates = states
				.stream().filter(s -> !s.isBottom()).map(
						s -> new GuardedInterferenceDomainState<STATE, ACTION, LOC>(s, newState.threadCounter(),
								newState.abstractLocationState().movedTo(mCurrentThreadName,
										oldstate.abstractLocationState().getLocationMap()
												.getAbstractLocation(transition.getTarget()))))
				.collect(Collectors.toSet());

		if (!mApplyInterferences) {
			return guardedStates;
		}
		// 2. apply interferences
//		mLogger.warn("Doing interferences inside Postop:");
		final var disj = DisjunctiveAbstractState.createDisjunction(guardedStates, mMaxParallelStates);
		final var afterItfs = mItfApplier.stateAfterInterferences(disj, mCurrentThreadName, mCache);
//		mLogger.warn("=====");
		return afterItfs.getStates();
	}

	public Collection<STATE> applyState(final STATE state, final ACTION transition) {
		return mUnderlyingPostOp.apply(state, transition);
	}

	public ThreadInstanceCounter applyThreadCounter(final ThreadInstanceCounter threadCounter,
			final ACTION transition) {
		var newCounter = threadCounter;
		if (transition instanceof final ForkThreadCurrent fork1) {
			final boolean circular = isCircular(fork1);
			final var forked = fork1.getNameOfForkedProcedure();
			newCounter = newCounter.setThreadsActive(List.of(forked));
		}
		return newCounter;
	}

	public AbstractLocationState<LOC> applyAbstractLocation(final AbstractLocationState<LOC> absLocState,
			final ACTION transition) {
		return absLocState.movedTo(transition.getPrecedingProcedure(),
				absLocState.getLocationMap().getAbstractLocation(transition.getTarget()));
	}

	private GuardedInterferenceDomainState<STATE, ACTION, LOC> applyFork(
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> oldstate, final ACTION transition) {

		var newState = oldstate;
		if (transition instanceof final ForkThreadCurrent fork1) {
			final boolean circular = isCircular(fork1);
			final var forked = fork1.getNameOfForkedProcedure();
			newState = newState.setThreadsActive(List.of(forked));
			if (circular || oldstate.threadCounter().getThreadInstances().get(forked) > 0) {
				newState = newState.setThreadsInf(List.of(forked));
			}
		} else {
			throw new IllegalArgumentException("Unsupported fork transition type");
		}
		return newState;
	}

	public boolean isCircular(final ForkThreadCurrent fork1) {
		return mforksInLoop.contains(fork1);
	}

	@Override
	public List<GuardedInterferenceDomainState<STATE, ACTION, LOC>> apply(
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> stateBeforeLeaving,
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> secondState, final ACTION transition) {
		throw new UnsupportedOperationException("Not implemented.");
	}

	@Override
	public EvalResult evaluate(final GuardedInterferenceDomainState<STATE, ACTION, LOC> state, final Term formula,
			final Script script) {
		throw new UnsupportedOperationException("Not implemented.");
	}
}
