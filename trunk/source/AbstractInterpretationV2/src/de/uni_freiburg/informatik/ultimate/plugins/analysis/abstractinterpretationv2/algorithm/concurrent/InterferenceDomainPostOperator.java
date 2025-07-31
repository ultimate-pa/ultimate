package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.List;
import java.util.Map;
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
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadCurrent;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.JoinThreadCurrent;

public class InterferenceDomainPostOperator<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>
		implements IAbstractPostOperator<InterferenceDomainState<STATE, ACTION, LOC>, ACTION> {

	private final ILogger mLogger;

	private String mCurrentThreadName;
	private final IAbstractPostOperator<STATE, ACTION> mUnderlyingPostOp;
	private final InterferenceFIxpoint<STATE, ACTION, LOC> mItfApplier;
	private final Set<IIcfgForkTransitionThreadCurrent<IcfgLocation>> mforksInLoop;

	private final int mMaxParallelStates;
	private final InterferenceCache<STATE, ACTION, LOC> mCache;

	private final InterferenceDomain<STATE, ACTION, LOC> mRelInterferingDomain;

	private final IIcfg<?> mIcfg;

	public InterferenceDomainPostOperator(final IIcfg<?> cfg, final ILogger logger,
			final IAbstractPostOperator<STATE, ACTION> postOp,
			final InterferenceDomain<STATE, ACTION, LOC> relationalInterferingDomain,
			final StaticAbstractLocationMap<LOC> globalMap, final int maxItf, final int maxParallelStates,
			final AbstractInterferenceState<STATE, ACTION, LOC> interferences,
			final InterferenceCache<STATE, ACTION, LOC> cache) {
		mRelInterferingDomain = relationalInterferingDomain;
		mLogger = logger;
		mUnderlyingPostOp = postOp;
		mItfApplier = new InterferenceFIxpoint<>(cfg, logger, relationalInterferingDomain, globalMap, maxItf,
				maxParallelStates, interferences);
		mforksInLoop = IcfgUtils.getForksInLoop(cfg);
		mMaxParallelStates = maxParallelStates;
		mCache = cache;
		mIcfg = cfg;
	}

	public InterferenceFIxpoint<STATE, ACTION, LOC> getItfApplier() {
		return mItfApplier;
	}

	@Override
	public Collection<InterferenceDomainState<STATE, ACTION, LOC>> apply(
			final InterferenceDomainState<STATE, ACTION, LOC> oldstate, final ACTION transition) {
		if (oldstate.isStateBottom()) {
			return List.of(oldstate);
		}
		mCurrentThreadName = transition.getPrecedingProcedure();

		// handle fork and join differently
		// TODO: make deep copy of abstractlocaation like for counter
		final ThreadInstanceCounter<LOC> counter = new ThreadInstanceCounter<>(oldstate.threadCounter());
		final ThreadInstanceCounter<LOC> newCounter;
		if (transition instanceof final ForkThreadCurrent fork) {
			newCounter = applyFork(counter, fork);
		} else if (transition instanceof final JoinThreadCurrent join) {
			newCounter = applyJoin(counter, oldstate.abstractLocationState(), join);
		} else {
			newCounter = new ThreadInstanceCounter<>(oldstate.threadCounter());
		}
		if (newCounter == null) {
			return List.of();
		}

		final var threadCount = oldstate.threadCounter().getThreadInstances().get(transition.getPrecedingProcedure());
		final var isInfinite = threadCount.getUpper().isInfinity() || threadCount.getUpper().getValue().intValue() > 1;

		final var newLocation = applyAbstractLocation(oldstate.abstractLocationState(), transition, false, isInfinite);

		// 1. normal poststate
		final var states = mUnderlyingPostOp.apply(oldstate.state(), transition);

		// adjust abstract location according to new location
		final var guardedStates = states.stream().filter(s -> !s.isBottom())
				.map(s -> new InterferenceDomainState<STATE, ACTION, LOC>(s, newCounter, newLocation))
				.collect(Collectors.toSet());

		// 2. apply interferences
		final var disj = DisjunctiveAbstractState.createDisjunction(guardedStates, mMaxParallelStates);
		final var afterItfs = mItfApplier.computeInterferenceFixpoint(disj, mCurrentThreadName, mCache);
//		mLogger.warn("=====");
		return afterItfs.getStates();
	}

	public Collection<STATE> applyState(final STATE state, final ACTION transition) {
		return mUnderlyingPostOp.apply(state, transition);
	}

	public ThreadInstanceCounter<LOC> applyThreadCounter(final ThreadInstanceCounter<LOC> threadCounter,
			final AbstractLocationState<LOC> absLocState, final ACTION transition) {
		var newCounter = threadCounter;
		if (transition instanceof final ForkThreadCurrent fork) {
			newCounter = applyFork(threadCounter, fork);
		}
		if (transition instanceof final JoinThreadCurrent join) {
			newCounter = applyJoin(threadCounter, absLocState, join);
		}
		return newCounter;
	}

	public AbstractLocationState<LOC> applyAbstractLocation(final AbstractLocationState<LOC> absLocState,
			final ACTION transition, final boolean isSelfInterfering, final boolean isinfinite) {
		if (isinfinite || isSelfInterfering) {
			final var abstractEntryLoc = absLocState.getLocationMap()
					.getAbstractEntryLoc(transition.getPrecedingProcedure());
			return absLocState.movedToInf(transition.getPrecedingProcedure(),
					absLocState.getLocationMap().getAbstractLocation(transition.getSource()),
					absLocState.getLocationMap().getAbstractLocation(transition.getTarget()), abstractEntryLoc);
		}
		return absLocState.movedTo(transition.getPrecedingProcedure(),
				absLocState.getLocationMap().getAbstractLocation(transition.getSource()),
				absLocState.getLocationMap().getAbstractLocation(transition.getTarget()));
	}

	private ThreadInstanceCounter<LOC> applyFork(final ThreadInstanceCounter<LOC> counter,
			final ForkThreadCurrent forkTransition) {
		final boolean isInfinite = (counter.getThreadInstances().get(forkTransition.getPrecedingProcedure()).getUpper()
				.isInfinity());
		final boolean circular = isCircular(forkTransition) || isInfinite;
		final var forked = forkTransition.getNameOfForkedProcedure();
		final int forkId = forkTransition.getForkStatement().getThreadID().length;
		final var newCounter = counter.assignForkId(forked, forkId, (LOC) forkTransition.getSource(), circular);
		return newCounter;
	}

	private ThreadInstanceCounter<LOC> applyJoin(final ThreadInstanceCounter<LOC> counter,
			final AbstractLocationState<LOC> absLocState, final JoinThreadCurrent joinTransition) {
		final int joinId = joinTransition.getJoinStatement().getThreadID().length;
		// If multiple forked threads have the same ID, we cannot differentiate and know what we are joining
		// (atleast with this method). So we lose precision by not joining at all.
		final var matchingThreads = computeNameOfJoinedProcedure(counter, joinId);
		if (matchingThreads.size() == 1) {
			final var joinedThreadName = matchingThreads.getFirst();
			final var zeroVal = new IntervalDomainValue(0, 0);
			final var joinedCounter = counter.unassignForkId(joinedThreadName, joinId,
					(LOC) joinTransition.getSource());

			final var counterValueAfterFork = joinedCounter.getThreadInstances().get(joinedThreadName);
			final boolean threadWasShutdown = counterValueAfterFork.isLessOrEqual(zeroVal).equals(BooleanValue.TRUE)
					|| joinedCounter.getAllForkIds().get(joinedThreadName).isEmpty();

			final var statesLocations = absLocState.getTracker().getLocationForThread(joinedThreadName);
			final var threadsFinalLocation = absLocState.getLocationMap().getAbstractFinalLoc(joinedThreadName);
			final boolean stateIsInFinalLocation = statesLocations.contains(threadsFinalLocation);
			if (threadWasShutdown && !stateIsInFinalLocation) {
				return null;
			}
			return joinedCounter;
		} else if (matchingThreads.size() > 1) {
			return counter;
		} else {
			return null;
		}
	}

	private List<String> computeNameOfJoinedProcedure(final ThreadInstanceCounter<LOC> counter, final int forkId) {
		return counter.getAllForkIds().entrySet().stream().filter(entry -> entry.getValue().contains(forkId))
				.map(Map.Entry::getKey).toList();
	}

	public boolean isCircular(final ForkThreadCurrent fork1) {
		return mforksInLoop.contains(fork1);
	}

	@Override
	public List<InterferenceDomainState<STATE, ACTION, LOC>> apply(
			final InterferenceDomainState<STATE, ACTION, LOC> stateBeforeLeaving,
			final InterferenceDomainState<STATE, ACTION, LOC> secondState, final ACTION transition) {
		throw new UnsupportedOperationException(
				"Postop with stateBeforeLeaving not implemented for GuardedInterferenceDomain.");
	}

	@Override
	public EvalResult evaluate(final InterferenceDomainState<STATE, ACTION, LOC> state, final Term formula,
			final Script script) {
		throw new UnsupportedOperationException("Evaluate not implemented for GuardedInterferenceDomain.");
	}
}
