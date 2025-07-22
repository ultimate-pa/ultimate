package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Optional;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.JoinThreadCurrent;

public class GuardedInterferenceDomainPostOperator<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>
		implements IAbstractPostOperator<GuardedInterferenceDomainState<STATE, ACTION, LOC>, ACTION> {

	private final ILogger mLogger;

	private String mCurrentThreadName;
	private final IAbstractPostOperator<STATE, ACTION> mUnderlyingPostOp;
	private final GuardedInterferenceApplier<STATE, ACTION, LOC> mItfApplier;
	private final Set<IIcfgForkTransitionThreadCurrent<IcfgLocation>> mforksInLoop;

	private final int mMaxParallelStates;
	private final GuardedInterferenceCache<STATE, ACTION, LOC> mCache;

	private final GuardedInterferenceDomain<STATE, ACTION, LOC> mRelInterferingDomain;

	public GuardedInterferenceDomainPostOperator(final IIcfg<?> cfg, final ILogger logger,
			final IAbstractPostOperator<STATE, ACTION> postOp,
			final GuardedInterferenceDomain<STATE, ACTION, LOC> relationalInterferingDomain,
			final AbstractLocationMap<LOC> globalMap, final int maxItf, final int maxParallelStates,
			final AbstractInterferenceState<STATE, ACTION, LOC> interferences,
			final GuardedInterferenceCache<STATE, ACTION, LOC> cache) {
		mRelInterferingDomain = relationalInterferingDomain;
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

	@Override
	public Collection<GuardedInterferenceDomainState<STATE, ACTION, LOC>> apply(
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> oldstate, final ACTION transition) {
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
			var bottomState = mRelInterferingDomain.createBottomState().addVariables(oldstate.getVariables());
			bottomState = bottomState.initializeLocation(transition.getTarget(),
					oldstate.abstractLocationState().getLocationMap(), oldstate.threadCounter().getThreadNameSet());
			return List.of(bottomState);
		}
		final var newLocation = oldstate.abstractLocationState().movedTo(mCurrentThreadName,
				oldstate.abstractLocationState().getLocationMap().getAbstractLocation(transition.getTarget()));

		// 1. normal poststate
		final var states = mUnderlyingPostOp.apply(oldstate.state(), transition);

		// adjust abstract location according to new location
		final var guardedStates = states.stream().filter(s -> !s.isBottom())
				.map(s -> new GuardedInterferenceDomainState<STATE, ACTION, LOC>(s, newCounter, newLocation))
				.collect(Collectors.toSet());

		// 2. apply interferences
		final var disj = DisjunctiveAbstractState.createDisjunction(guardedStates, mMaxParallelStates);
		final var afterItfs = mItfApplier.stateAfterInterferences(disj, mCurrentThreadName, mCache);
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
			final ACTION transition) {
		return absLocState.movedTo(transition.getPrecedingProcedure(),
				absLocState.getLocationMap().getAbstractLocation(transition.getTarget()));
	}

	private ThreadInstanceCounter<LOC> applyFork(final ThreadInstanceCounter<LOC> counter,
			final ForkThreadCurrent forkTransition) {
		final boolean circular = isCircular(forkTransition)
				|| (counter.getThreadInstances().get(forkTransition.getPrecedingProcedure()) > 1);
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
		final var joinedThreadName = computeNameOfJoinedProcedure(counter, joinId);
		if (joinedThreadName.isPresent()) {

			final var forkedThreadCount = counter.getThreadInstances().get(joinedThreadName.get());
			final var joinedCounter = counter.unassignForkId(joinedThreadName.get(), joinId,
					(LOC) joinTransition.getSource());
			final var forkedThreadCountAfter = joinedCounter.getThreadInstances().get(joinedThreadName.get());
			final var threadsFinalLocations = absLocState.getLocationMap().getAbstractFinalLocs(joinedThreadName.get());
			final var statesLocations = absLocState.getTracker().getLocationForThread(joinedThreadName.get());

			final boolean threadWasShutdown = (forkedThreadCount > 0 && forkedThreadCountAfter == 0)
					|| joinedCounter.getAllForkIds().get(joinedThreadName.get()).isEmpty();
			final boolean stateIsInFinalLocation = threadsFinalLocations.containsAll(statesLocations);
			if (threadWasShutdown && !stateIsInFinalLocation) {
				return null;
			}
			return joinedCounter;
		}
		return counter;
	}

	private Optional<String> computeNameOfJoinedProcedure(final ThreadInstanceCounter<LOC> counter, final int forkId) {

		final List<String> matchingThreads = counter.getAllForkIds().entrySet().stream()
				.filter(entry -> entry.getValue().contains(forkId)).map(Map.Entry::getKey).toList();
		// if multiple threads or none contain that threadID as a forked thread, we dont do anything
		return matchingThreads.size() == 1 ? Optional.of(matchingThreads.get(0)) : Optional.empty();
	}

	public boolean isCircular(final ForkThreadCurrent fork1) {
		return mforksInLoop.contains(fork1);
	}

	@Override
	public List<GuardedInterferenceDomainState<STATE, ACTION, LOC>> apply(
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> stateBeforeLeaving,
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> secondState, final ACTION transition) {
		throw new UnsupportedOperationException(
				"Postop with stateBeforeLeaving not implemented for GuardedInterferenceDomain.");
	}

	@Override
	public EvalResult evaluate(final GuardedInterferenceDomainState<STATE, ACTION, LOC> state, final Term formula,
			final Script script) {
		throw new UnsupportedOperationException("Evaluate not implemented for GuardedInterferenceDomain.");
	}
}
