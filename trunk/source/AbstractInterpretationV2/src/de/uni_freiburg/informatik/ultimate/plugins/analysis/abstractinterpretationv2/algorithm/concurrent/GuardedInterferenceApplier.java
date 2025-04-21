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

	private final IAbstractPostOperator<STATE, ACTION> mUnderlyingPostOp;
	private final GuardedInterferenceDomain<STATE, ACTION, LOC> mGuardedInterferenceDomain;
	private final Map<InterferenceStatePair<STATE, ACTION, LOC>, STATE> mInterferenceCache = new HashMap<>();
	private final AbstractLocationMap<LOC> mAbstractLocationMap;
	private int mIterations;
	private final int mMaxItf;
	private final int mMaxParallelStates;

	public static int iterationsReached = 0;

	public GuardedInterferenceApplier(final IIcfg<?> cfg, final ILogger logger,
			final IAbstractPostOperator<STATE, ACTION> postOp,
			final GuardedInterferenceDomain<STATE, ACTION, LOC> relationalInterferingDomain,
			final AbstractInterferenceState<STATE, ACTION, LOC> interferenceState,
			final AbstractLocationMap<LOC> globalMap, final int maxItf, final int maxParallelStates) {
		mToolkit = cfg.getCfgSmtToolkit();
		mLogger = logger;
		mUnderlyingPostOp = postOp;
		mGuardedInterferenceDomain = relationalInterferingDomain;
		mInterferences = interferenceState;
		mNewInterferences = new AbstractInterferenceState<>(cfg.getCfgSmtToolkit().getProcedures());
		mAbstractLocationMap = globalMap;
		mMaxItf = maxItf;
		mMaxParallelStates = maxParallelStates;
		iterationsReached = 0;
	}

	private record InterferenceStatePair<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>(
			Interference<STATE, ACTION, LOC> interf, STATE targetState) {
	}

	private record InterferenceWithParentThread<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>(
			Interference<STATE, ACTION, LOC> interf, String sourceThread) {
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
		initialize();
		final Set<String> possibleInterferenceSet = getThreadsThatCanInterfere(oldstate, ownerThread);
		if (possibleInterferenceSet.isEmpty()) {
			return Set.of(oldstate);
		}
		return interferenceFixpointFast(possibleInterferenceSet, oldstate, ownerThread);
	}

	private void initialize() {
		mIterations = 0;
	}

	private Set<String> getThreadsThatCanInterfere(final GuardedInterferenceDomainState<STATE, ACTION, LOC> oldstate,
			final String ownerThread) {
		final Set<String> threadNameSet = oldstate.threadCounter().getThreadNameSet();
		final Set<String> possibleInterferenceSet = new HashSet<>();
		final var procedureMap = oldstate.threadCounter().getThreadInstances();
		for (final String threadName : threadNameSet) {
			final int threadInstances = procedureMap.get(threadName);
			if (threadInstances >= 2 || threadName != ownerThread && threadInstances > 0) {
				possibleInterferenceSet.add(threadName);
			}
		}
		return possibleInterferenceSet;
	}

	private Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> interferenceFixpointFast(
			final Set<String> interferingThreads, final GuardedInterferenceDomainState<STATE, ACTION, LOC> state,
			final String ownerThread) {

		// Collect all starting, intermediate and final states as possibilities of all possible thread interleavings
		Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> newStates = new LinkedHashSet<>();
		newStates.add(state);
		final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> oldStates = new LinkedHashSet<>();
		oldStates.add(state);
		var allDisj = new DisjunctiveAbstractState<>(mMaxParallelStates, state);
		var newDisj = new DisjunctiveAbstractState<>(mMaxParallelStates, state);

		final var allInterferences = getValidInterferences(interferingThreads, ownerThread);

		while (true) {
			mIterations++;
			if (mIterations > iterationsReached) {
				iterationsReached = mIterations;
			}

			// state just to check if fixpoint reached after this iteration
			newStates = new HashSet<>();

			for (final GuardedInterferenceDomainState<STATE, ACTION, LOC> singleState : newDisj.getStates()) {
				for (final InterferenceWithParentThread<STATE, ACTION, LOC> interference : allInterferences) {
					final var postState = checkLocAndCacheThenApply(interference.interf(), singleState,
							interference.sourceThread(), ownerThread);
					if (postState == null || postState.isEmpty() || postState.getVariables().isEmpty()) {
						continue;
					}
					// Interferences should not remove/add variables
					assert postState.getVariables().equals(singleState.getVariables());

					newStates.add(postState);
				}
			}
			oldStates.clear();
			newDisj = DisjunctiveAbstractState.createDisjunction(newStates, mMaxParallelStates);
			final boolean changed = newDisj.isSubsetOf(allDisj) != SubsetResult.NONE ? false : true;
			if (mIterations <= mMaxItf) {
				allDisj = allDisj.union(newDisj);
			} else {
				allDisj = allDisj.widen(mGuardedInterferenceDomain.getWideningOperator(), newDisj);
				if (mIterations > mMaxItf + 2) {
					break;
				}
			}

			if (!changed) {
				break;
			}
			oldStates.addAll(newDisj.getStates());
			allDisj = allDisj.union(newDisj);
		}
		return allDisj.getStates();
	}

	private Set<InterferenceWithParentThread<STATE, ACTION, LOC>> getValidInterferences(
			final Set<String> interferingThreads, final String ownerThread) {
		final Set<InterferenceWithParentThread<STATE, ACTION, LOC>> allInterferences = new LinkedHashSet<>();

		for (final String interferenceThreadName : interferingThreads) {
			final var interferences = mInterferences.getInterferenceMapHashRelation().get(interferenceThreadName);
			if (interferences == null) {
				continue;
			}
			for (final Interference<STATE, ACTION, LOC> interference : interferences) {
				if (interference.threadcounter().getThreadInstances().get(ownerThread) == 0) {
					continue;
				}
				allInterferences.add(new InterferenceWithParentThread<>(interference, interferenceThreadName));
			}
		}
		return allInterferences;
	}

	private GuardedInterferenceDomainState<STATE, ACTION, LOC> checkLocAndCacheThenApply(
			final Interference<STATE, ACTION, LOC> interference,
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> newState, final String interferenceThreadName,
			final String ownerThread) {

		GuardedInterferenceDomainState<STATE, ACTION, LOC> interferedState = null;
		// 2. check abstract locations (is interfering thread in location where it matches the interference
		// action)
		if (!matchesLocation(newState, ownerThread, interferenceThreadName, interference)) {
			return newState;
		}
		final var pair = new InterferenceStatePair<>(interference, newState.state());
		// if in cache, return state with cached underlying state without applying postOp
		if (mInterferenceCache.get(pair) != null) {
			final var interferedSingleState = mInterferenceCache.get(pair);
			interferedState = new GuardedInterferenceDomainState<>(interferedSingleState, newState.threadCounter(),
					newState.abstractLocationState());
			interferedState = interferedState.movedTo(interference.action().getPrecedingProcedure(),
					mAbstractLocationMap.getAbstractLocation(interference.action().getTarget()));
		} else {
			interferedState = applyInterferenceToSTATE(interference, newState);
			if (interferedState != null) {
				mInterferenceCache.put(pair, interferedState.state());
			}
		}

		// in case of interfering fork, update threadcounter and location
		if (interferedState != null && interference.action() instanceof final ForkThreadCurrent fork) {
			interferedState = interferedState.setThreadsActive(Set.of(fork.getNameOfForkedProcedure()));
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
				&& !(ownerThread.equals(interferenceThreadName))
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
