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
//	private final static Map<Pair<IAbstractState<?>, IIcfgTransition<?>>, Collection<? extends IAbstractState<?>>> mCacheMap = new HashMap<>();

	private final int mMaxParallelStates;
	private boolean mApplyInterferences = true;

	public GuardedInterferenceDomainPostOperator(final IIcfg<?> cfg, final ILogger logger,
			final IAbstractPostOperator<STATE, ACTION> postOp,
			final GuardedInterferenceDomain<STATE, ACTION, LOC> relationalInterferingDomain,
			final AbstractLocationMap<LOC> globalMap, final int maxItf, final int maxParallelStates,
			final AbstractInterferenceState<STATE, ACTION, LOC> interferences) {
		mLogger = logger;
		mUnderlyingPostOp = postOp;
		mItfApplier = new GuardedInterferenceApplier<>(logger, postOp, relationalInterferingDomain, globalMap, maxItf,
				maxParallelStates, interferences);
		mforksInLoop = IcfgUtils.getForksInLoop(cfg);
		mMaxParallelStates = maxParallelStates;
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
		final var oldVariables = oldstate.getVariables();
		if (oldstate.isStateBottom()) {
			return List.of(oldstate);
		}
		mCurrentThreadName = transition.getPrecedingProcedure();

		// handle fork differently
		final var newState = (transition instanceof ForkThreadCurrent || transition instanceof ForkThreadOther)
				? applyFork(oldstate, transition)
				: oldstate;

		// 1. normal poststate
		final var states = mUnderlyingPostOp.apply(newState.state(), transition);
//		final var states = (Collection<STATE>) mCacheMap.computeIfAbsent(new Pair<>(newState.state(), transition),
//				x -> mUnderlyingPostOp.apply((STATE) x.getFirst(), (ACTION) x.getSecond()));
		final var intermediateVariables = states.stream().flatMap(s -> s.getVariables().stream())
				.collect(Collectors.toSet());

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
		final var afterItfs = mItfApplier.stateAfterInterferences(
				DisjunctiveAbstractState.createDisjunction(guardedStates, mMaxParallelStates), mCurrentThreadName);
		// TODO: should be moved during interferencecomputation?
		final var moved = GuardedStateTransformer.copyToNewStateLocation(transition.getTarget(), afterItfs);
		final var newVariables = moved.getVariables();
		if (!moved.isBottom() && !oldVariables.equals(intermediateVariables)) {
			throw new IllegalStateException("Post should not change variables");
		}
		if (!moved.isBottom() && !oldVariables.equals(newVariables)) {
			throw new IllegalStateException("Interferences should not change variables");
		}
		return moved.getStates();
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
