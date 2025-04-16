package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadCurrent;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class GuardedInterferenceApplier<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {
	private final ILogger mLogger;

	private AbstractInterferenceState<STATE, ACTION, LOC> mInterferences;
	private AbstractInterferenceState<STATE, ACTION, LOC> mNewInterferences;
	private final CfgSmtToolkit mToolkit;

	private final IAbstractDomain<STATE, ACTION> mUnderlyingDomain;
	private final IAbstractPostOperator<STATE, ACTION> mUnderlyingPostOp;
	private final GuardedInterferenceDomain<STATE, ACTION, LOC> mGuardedInterferenceDomain;
	private final Map<InterferenceStatePair<STATE, ACTION, LOC>, GuardedInterferenceDomainState<STATE, ACTION, LOC>> mInterferenceCache = new HashMap<>();
	private final AbstractLocationMap<LOC> mAbstractLocationMap;
	private int mIterations;
	private boolean mForked = false;
	private boolean mForkDone = false;
	private final int mMaxItf;
	private final int mMaxParallelStates;
	public static int iterationsReached = 0;

	public GuardedInterferenceApplier(final IIcfg<?> cfg, final ILogger logger,
			final IAbstractDomain<STATE, ACTION> underlying, final IAbstractPostOperator<STATE, ACTION> postOp,
			final GuardedInterferenceDomain<STATE, ACTION, LOC> relationalInterferingDomain,
			final AbstractInterferenceState<STATE, ACTION, LOC> interferenceState,
			final AbstractLocationMap<LOC> globalMap, final int maxItf, final int maxParallelStates) {
		mToolkit = cfg.getCfgSmtToolkit();
		mLogger = logger;
		mUnderlyingDomain = underlying;
		mUnderlyingPostOp = postOp;
		mGuardedInterferenceDomain = relationalInterferingDomain;
		mInterferences = interferenceState;
		mNewInterferences = new AbstractInterferenceState<>(cfg.getCfgSmtToolkit().getProcedures());
		mAbstractLocationMap = globalMap;
		mMaxItf = maxItf;
		mMaxParallelStates = maxParallelStates;
		iterationsReached = 0;
	}

	public AbstractInterferenceState<STATE, ACTION, LOC> getInterferences() {
		return mInterferences;
	}

	public void addItf(final String mCurrentThreadName, final ACTION transition,
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> oldstate) {
		mNewInterferences.addInterference(mCurrentThreadName, transition, oldstate.state(), oldstate.threadCounter());
	}

	public void setInterferences(final AbstractInterferenceState<STATE, ACTION, LOC> newState) {
		mInterferences = new AbstractInterferenceState<>(newState);
		mNewInterferences = new AbstractInterferenceState<>(mToolkit.getProcedures());
	}

	public void updateInterferences() {
		mInterferences = mInterferences.union(mNewInterferences);
		mNewInterferences = new AbstractInterferenceState<>(mToolkit.getProcedures());

	}

	public Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> stateAfterInterferences(
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> oldstate, final String ownerThread) {

		// compute which threads can interfere in this state
		final Set<String> threadNameSet = oldstate.threadCounter().getThreadNameSet();
		final Set<String> possibleInterferenceSet = new HashSet<>();
		final var procedureMap = oldstate.threadCounter().getThreadInstances();
		for (final String threadName : threadNameSet) {
			final int threadInstances = procedureMap.get(threadName);
			if (threadInstances >= 2 || threadName != ownerThread && threadInstances > 0) {
				possibleInterferenceSet.add(threadName);
			}
		}

		if (possibleInterferenceSet.isEmpty()) {
			return Set.of(oldstate);
		}

		return interferenceFixpoint(possibleInterferenceSet, oldstate, ownerThread);
	}

	private record InterferenceStatePair<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>(
			Interference<STATE, ACTION, LOC> interf, GuardedInterferenceDomainState<STATE, ACTION, LOC> targetState) {
	}

	private Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> interferenceFixpoint(
			final Set<String> interferingThreads, final GuardedInterferenceDomainState<STATE, ACTION, LOC> state,
			final String ownerThread) {
		mIterations = 0;
		mForked = false;
		final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> possibleGuardedInterferenceDomainStates = new LinkedHashSet<>();
		possibleGuardedInterferenceDomainStates.add(state);
		var newDisj = new DisjunctiveAbstractState<>(state);
		while (true) {
			mIterations++;
			if (mIterations > iterationsReached) {
				iterationsReached = mIterations;
				mLogger.warn(mIterations);
			}
			// state just to check if fixpoint reached after this iteration
			final var oldDisj = newDisj;

			for (final String interferenceThreadName : interferingThreads) {
				final var interferences = mInterferences.getInterferenceMapHashRelation().get(interferenceThreadName);
				if (mInterferences.getInterferencesForThread(interferenceThreadName) == null) {
					continue;
				}
//				newState = applyInterferences(newState, interferences, ownerThread, interferenceThreadName);

				for (final GuardedInterferenceDomainState<STATE, ACTION, LOC> singleState : newDisj.getStates()) {
					possibleGuardedInterferenceDomainStates.addAll(
							applyInterferences(singleState, interferences, ownerThread, interferenceThreadName));
				}
			}
			newDisj = DisjunctiveAbstractState.createDisjunction(possibleGuardedInterferenceDomainStates,
					mMaxParallelStates);
			if (mIterations < mMaxItf) {
				newDisj = newDisj.union(oldDisj);
			} else {
				newDisj = newDisj.widen(mGuardedInterferenceDomain.getWideningOperator(), oldDisj);
			}

			final boolean changed = newDisj.isSubsetOf(oldDisj) != SubsetResult.NONE ? false : true;
			if (!changed) {
				break;
			}
		}
		if (mForked && !mForkDone) {
			// TODO: we can solve this less costly probably (we just want to go again, with superset of interferenceset)
			// TODO: could mean insane overhead
			mForkDone = true;
			for (final GuardedInterferenceDomainState<STATE, ACTION, LOC> single : newDisj.getStates()) {
				DisjunctiveAbstractState.union(stateAfterInterferences(single, ownerThread));
			}
		}
		return newDisj.getStates();
	}

	private Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> applyInterferences(
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> newState,
			final Set<Interference<STATE, ACTION, LOC>> interferences, final String ownerThread,
			final String interferenceThreadName) {

		final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> allPossibleOutcomes = new LinkedHashSet<>();
		for (final Interference<STATE, ACTION, LOC> interference : interferences) {
			var blankState = newState;
			// 1. check threadcounter (is interfering thread alive in our state?)
			if (interference.threadcounter().getThreadInstances().get(ownerThread) == 0) {
				continue;
			}
			// in case of interfering fork, just update threadcounter and location
			if (interference.action() instanceof final ForkThreadCurrent fork) {
				blankState = handleFork(newState, fork);
				blankState = blankState.movedTo(interference.action().getPrecedingProcedure(),
						mAbstractLocationMap.getAbstractLocation(interference.action().getTarget()));
				continue;
			}
			final var postState = applyInterferenceToDisjunctiveState(interference, newState, interferenceThreadName,
					ownerThread);
			// TODO: why newstate null
			if (postState == null || postState.isEmpty() || postState.getVariables().isEmpty()) {
				continue;
			}

			// Interferences should not remove/add variables
			assert postState.getVariables().equals(blankState.getVariables());

			allPossibleOutcomes.add(postState);
		}
		return allPossibleOutcomes;
	}

	private GuardedInterferenceDomainState<STATE, ACTION, LOC> handleFork(
			GuardedInterferenceDomainState<STATE, ACTION, LOC> newState, final ForkThreadCurrent fork) {
		final int beforeFork = newState.threadCounter().getThreadInstances().get(fork.getNameOfForkedProcedure());
		newState = newState.setThreadsActive(Set.of(fork.getNameOfForkedProcedure()));
		final int afterFork = newState.threadCounter().getThreadInstances().get(fork.getNameOfForkedProcedure());
		if (beforeFork < afterFork) {
			mForked = true;
		}
		return newState;
	}

	private GuardedInterferenceDomainState<STATE, ACTION, LOC> applyInterferenceToDisjunctiveState(
			final Interference<STATE, ACTION, LOC> interference,
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> newState, final String interferenceThreadName,
			final String ownerThread) {

		GuardedInterferenceDomainState<STATE, ACTION, LOC> interferedState = null;
		// 2. check abstract locations (is interfering thread in location where it matches the interference
		// action)
		if (!matchesLocation(newState, ownerThread, interferenceThreadName, interference)) {
			return newState;
		}
		final var pair = new InterferenceStatePair<>(interference, newState);
		// if in cache, return state with cached underlying state without applying postOp
		if (mInterferenceCache.get(pair) != null) {
//			disjunction.add(mInterferenceCache.get(pair));
			interferedState = mInterferenceCache.get(pair);
		} else {
//			mLogger.warn("applying:" + interference);
//			mLogger.warn("to:" + newState);
			interferedState = applyInterferenceToSTATE(interference, newState);
//			mLogger.warn("result:" + interferedState);
//			mLogger.warn("---");
//			if (interferedState == null) {
//				continue;
//			}
			mInterferenceCache.put(pair, interferedState);
		}
		return interferedState;
	}

	private boolean matchesLocation(final GuardedInterferenceDomainState<STATE, ACTION, LOC> singleState,
			final String ownerThread, final String interferenceThreadName,
			final Interference<STATE, ACTION, LOC> interference) {
		final Set<Integer> possibleInterferingLocations = singleState.abstractLocationState().getTracker()
				.getLocationForThread(interferenceThreadName);
		final int interferenceLocation = mAbstractLocationMap.getAbstractLocation(interference.action().getSource());
		if ((!possibleInterferingLocations.contains(interferenceLocation)
				|| !(singleState.threadCounter().getThreadInstances().get(interferenceThreadName) > 0))
				&& !(ownerThread == interferenceThreadName)
				&& !(singleState.threadCounter().getThreadInstances().get(interferenceThreadName) > 1)) {
			return false;
		}
		return true;
	}

	private GuardedInterferenceDomainState<STATE, ACTION, LOC> applyInterferenceToSTATE(
			final Interference<STATE, ACTION, LOC> interference,
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> singleState) {
		// Add variables to both states to be able to intersect
		STATE interferingState = interference.state();
		STATE stateState = singleState.state();
		final var missingLocals = DataStructureUtils.difference(stateState.getVariables(),
				interferingState.getVariables());
		final var missingLocals2 = DataStructureUtils.difference(interferingState.getVariables(),
				stateState.getVariables());
		if (stateState.isBottom() || interferingState.isBottom()) {
			return null;
		}
		if (!missingLocals2.isEmpty()) {
			stateState = stateState.addVariables(missingLocals2);
		}
		if (!missingLocals.isEmpty()) {
			interferingState = interferingState.addVariables(missingLocals);
		}
		final STATE intersectionState = stateState.intersect(interferingState);
		if (intersectionState.isBottom()) {
			return null;
		}
		// postop
		Collection<STATE> postState = mUnderlyingPostOp.apply(intersectionState, interference.action());
		// TODO: sound?
		if (postState.isEmpty()) {
//			return singleState;
			return null;
		}
		if (!missingLocals2.isEmpty()) {
			postState = postState.stream().map(s -> s.removeVariables(missingLocals2)).collect(Collectors.toList());
		}
		STATE unionState = postState.iterator().next();
		for (final STATE state : postState) {
			if (state != unionState) {
				unionState = unionState.union(state);
			}
		}
		var guardedState = new GuardedInterferenceDomainState<STATE, ACTION, LOC>(unionState,
				singleState.threadCounter(), singleState.abstractLocationState());
		guardedState = guardedState.movedTo(interference.action().getPrecedingProcedure(),
				mAbstractLocationMap.getAbstractLocation(interference.action().getTarget()));
		return guardedState;
	}

}
