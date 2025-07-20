package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.Collections;
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
	private boolean mApplyInterferences = true;
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

		// handle fork and join differently
		final var forkedState = (transition instanceof final ForkThreadCurrent forkTransition)
				? applyFork(oldstate, forkTransition)
				: oldstate;

		final var joinedState = (transition instanceof final JoinThreadCurrent joinTransition)
				? applyJoin(forkedState, joinTransition)
				: forkedState;

		if (joinedState == null) {
			return Collections.emptyList();
		}

		// 1. normal poststate
//		mLogger.warn("calculating Postop:");
		final var states = mUnderlyingPostOp.apply(joinedState.state(), transition);
//		mLogger.warn("finished Postop:");

		// adjust abstract location according to new location
		final var guardedStates = states
				.stream().filter(s -> !s.isBottom()).map(
						s -> new GuardedInterferenceDomainState<STATE, ACTION, LOC>(s, joinedState.threadCounter(),
								joinedState.abstractLocationState().movedTo(mCurrentThreadName,
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

	public ThreadInstanceCounter<LOC> applyThreadCounter(final ThreadInstanceCounter<LOC> threadCounter,
			final ACTION transition) {
		var newCounter = threadCounter;
		if (transition instanceof final ForkThreadCurrent fork1) {
			final boolean circular = isCircular(fork1);
			final var forked = fork1.getNameOfForkedProcedure();
			final var forkID = fork1.getForkStatement().getThreadID().length;
			newCounter = newCounter.assignForkId(forked, forkID, (LOC) fork1.getSource(), circular);
		}
		return newCounter;
	}

	public AbstractLocationState<LOC> applyAbstractLocation(final AbstractLocationState<LOC> absLocState,
			final ACTION transition) {
		return absLocState.movedTo(transition.getPrecedingProcedure(),
				absLocState.getLocationMap().getAbstractLocation(transition.getTarget()));
	}

	private GuardedInterferenceDomainState<STATE, ACTION, LOC> applyFork(
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> oldstate, final ForkThreadCurrent forkTransition) {
		final boolean circular = isCircular(forkTransition);
		final var forked = forkTransition.getNameOfForkedProcedure();
		final int forkId = forkTransition.getForkStatement().getThreadID().length;
		final var newState = oldstate.assignForkId(forked, forkId, (LOC) forkTransition.getSource(), circular);
		final var x = newState.threadCounter().getAllForkIds();

		return newState;
	}

	private GuardedInterferenceDomainState<STATE, ACTION, LOC> applyJoin(
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> state, final JoinThreadCurrent joinTransition) {
		final int joinId = joinTransition.getJoinStatement().getThreadID().length;
		// If multiple forked threads have the same ID, we cannot differentiate and know what we are joining
		// (atleast with this method). So we lose precision by not joining at all.
		final var joinedThreadName = computeNameOfJoinedProcedure(state, joinId);
		if (joinedThreadName.isPresent()) {

			final var forkedThreadCount = state.threadCounter().getThreadInstances().get(joinedThreadName.get());
			final var joinedState = state.unassignForkId(joinedThreadName.get(), joinId,
					(LOC) joinTransition.getSource());
			final var forkedThreadCountAfter = joinedState.threadCounter().getThreadInstances()
					.get(joinedThreadName.get());
			final var threadsFinalLocations = joinedState.abstractLocationState().getLocationMap()
					.getAbstractFinalLocs(joinedThreadName.get());
			final var statesLocations = joinedState.abstractLocationState().getTracker()
					.getLocationForThread(joinedThreadName.get());

			final boolean threadWasShutdown = (forkedThreadCount > 0 && forkedThreadCountAfter == 0);
			final boolean stateIsInFinalLocation = threadsFinalLocations.containsAll(statesLocations);
			if (threadWasShutdown && !stateIsInFinalLocation) {
				return null;
			}
			return joinedState;
		}
		return state;
	}

	private Optional<String> computeNameOfJoinedProcedure(
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> state, final int forkId) {

		final List<String> matchingThreads = state.threadCounter().getAllForkIds().entrySet().stream()
				.filter(entry -> entry.getValue().contains(forkId)).map(Map.Entry::getKey).toList();
		// if multiple threads or none contain that threadID as a forked thread, we dont do anything
		if (matchingThreads.size() != 1) {
			final var x = state.threadCounter().getAllForkIds();
		}
		return matchingThreads.size() == 1 ? Optional.of(matchingThreads.get(0)) : Optional.empty();
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
