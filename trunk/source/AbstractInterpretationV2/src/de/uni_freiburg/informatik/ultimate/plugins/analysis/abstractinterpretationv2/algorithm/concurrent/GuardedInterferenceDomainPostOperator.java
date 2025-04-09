package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadCurrent;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadOther;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class GuardedInterferenceDomainPostOperator<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>
		implements IAbstractPostOperator<GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC>, ACTION> {
	private String mCurrentThreadName;

	private final ILogger mLogger;

	private AbstractInterferenceState<STATE, ACTION, LOC> mInterferences;
	private AbstractInterferenceState<STATE, ACTION, LOC> mNewInterferences;
	private final CfgSmtToolkit mToolkit;
	private final IAbstractDomain<STATE, ACTION> mUnderlyingDomain;
	private final IAbstractPostOperator<STATE, ACTION> mUnderlyingPostOp;
	private final GuardedInterferenceDomain<STATE, ACTION, LOC> mGuardedInterferenceDomain;
	private final Set<IProgramNonOldVar> mGlobalVariables;
	private final Map<InterferenceStatePair<STATE, ACTION, LOC>, GuardedInterferenceDomainState<STATE, ACTION, LOC>> mInterferenceCache = new HashMap<>();
	private final AbstractLocationMap<LOC> mAbstractLocationMap;

	private final int MAXITF = 9;
	private int mIterations;
	private boolean mForked = false;

	public GuardedInterferenceDomainPostOperator(final IIcfg<?> cfg, final ILogger logger,
			final IAbstractDomain<STATE, ACTION> underlying, final IAbstractPostOperator<STATE, ACTION> postOp,
			final GuardedInterferenceDomain<STATE, ACTION, LOC> relationalInterferingDomain,
			final AbstractInterferenceState<STATE, ACTION, LOC> interferenceState,
			final AbstractLocationMap<LOC> globalMap) {
		mLogger = logger;
		mToolkit = cfg.getCfgSmtToolkit();
		mUnderlyingDomain = underlying;
		mUnderlyingPostOp = postOp;
		mGuardedInterferenceDomain = relationalInterferingDomain;
		mGlobalVariables = mToolkit.getSymbolTable().getGlobals();
		mInterferences = interferenceState;
		mNewInterferences = new AbstractInterferenceState<>(cfg.getCfgSmtToolkit().getProcedures());
		mAbstractLocationMap = globalMap;
	}

	public AbstractInterferenceState<STATE, ACTION, LOC> getInterferences() {
		return mInterferences;
	}

	public void setInterferences(final AbstractInterferenceState<STATE, ACTION, LOC> newState) {
		mInterferences = new AbstractInterferenceState<>(newState);
		mNewInterferences = new AbstractInterferenceState<>(mToolkit.getProcedures());
	}

	public void updateInterferences() {
		mInterferences = mInterferences.union(mNewInterferences);
		mNewInterferences = new AbstractInterferenceState<>(mToolkit.getProcedures());

	}

	@Override
	public Collection<GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC>> apply(
			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> oldstate, final ACTION transition) {
		if (oldstate.isBottom()) {
			return List.of(oldstate);
		}
		mCurrentThreadName = transition.getPrecedingProcedure();

		// handle fork differently
		if (transition instanceof ForkThreadCurrent || transition instanceof ForkThreadOther) {
			return applyFork(oldstate, transition);
		}

		// 1. normal poststate
		// TODO: TODO: TODO: i think i need to respect abstract location here too, not just during interference
		GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> postRelationalState = oldstate.apply(mUnderlyingPostOp,
				transition);
//		mLogger.info("post(" + oldstate.toLogString() + ", " + transition + ") = " + postRelationalState);

		// 2. Add new interference to global map
		if (isInterferingTransition(transition)) {
			mNewInterferences.addInterference(mCurrentThreadName, transition, oldstate.getSingleState().state(),
					oldstate.getThreadInstanceState());
		}

		// 3. apply interferences
		if (!postRelationalState.isBottom()) {
			postRelationalState = stateAfterInterferences(postRelationalState, mCurrentThreadName);
		}

		return List.of(postRelationalState);
	}

	// with naive location abstraction we cannot skip any interferences, even if they are a "skip"
	private boolean isInterferingTransition(final ACTION transition) {
		return true;
//		if (!transition.getTransformula().getAssignedVars().stream()
//				.anyMatch(assignedVar -> mGlobalVariables.contains(assignedVar))) {
//			return false;
//		}
//		if (!(transition instanceof final StatementSequence statementSequence)) {
//			return true;
//		}
//		for (final Statement statement : statementSequence.getStatements()) {
//			if (!(statement instanceof AssumeStatement)) {
//				return true;
//			}
//		}
//		return false;
	}

	private Collection<GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC>> applyFork(
			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> oldstate, final ACTION transition) {

		var newState = new GuardedInterferenceDomainStateDisj<>(oldstate);
		if (transition instanceof final ForkThreadCurrent fork1) {
			final boolean circular = isCircular(fork1, fork1.getSource().getIncomingEdges(), 0);
			final var forked = fork1.getNameOfForkedProcedure();
			newState = newState.setThreadsActive(List.of(forked));
			if (circular || oldstate.getThreadInstanceState().getThreadInstances().get(forked) > 0) {
				newState = newState.setThreadsInf(List.of(forked));
			}
		} else {
			throw new IllegalArgumentException("Unsupported fork transition type");
		}
		newState = newState.apply(mUnderlyingPostOp, transition);
		// apply interferences
		newState = stateAfterInterferences(newState, mCurrentThreadName);
		mNewInterferences.addForkInterference(mCurrentThreadName, transition, oldstate.getSingleState().state(),
				oldstate.getThreadInstanceState());
		return List.of(newState);
	}

	public boolean isCircular(final IcfgEdge fork1, final List<IcfgEdge> edges, final int depth) {
		// TODO: replace by caching all statements seen, breaking when any seen again
		if (depth > 100) {
			return false;
		}
		if (edges.isEmpty()) {
			return false;
		}
		if (edges.contains(fork1)) {
			return true;
		}
		for (final IcfgEdge icfgEdge : edges) {
			if (isCircular(fork1, icfgEdge.getSource().getIncomingEdges(), depth + 1)) {
				return true;
			}
		}
		return false;
	}

	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> stateAfterInterferences(
			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> oldstate, final String ownerThread) {

		// this check might cost more time than it saves, if we don't encounter a lot of top-states
//		final var topstate = mUnderlyingDomain.createTopState();
//		if (topstate.addVariables(DataStructureUtils.difference(oldstate.getVariables(), topstate.getVariables()))
//				.isSubsetOf(oldstate.getUnderlyingState()) != SubsetResult.NONE) {
//			return oldstate;
//		}

		// compute which threads can interfere in this state
		final Set<String> threadNameSet = oldstate.getThreadInstanceState().getThreadNameSet();
		final Set<String> possibleInterferenceSet = new HashSet<>();
		final var procedureMap = oldstate.getThreadInstanceState().getThreadInstances();
		for (final String threadName : threadNameSet) {
			final int threadInstances = procedureMap.get(threadName);
			if (threadInstances >= 2 || threadName != ownerThread && threadInstances > 0) {
				possibleInterferenceSet.add(threadName);
			}
		}

		return oldstate.union(interferenceFixpoint(possibleInterferenceSet, oldstate, ownerThread));
	}

	private record InterferenceStatePair<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>(
			Interference<STATE, ACTION, LOC> interf, GuardedInterferenceDomainState<STATE, ACTION, LOC> targetState) {
	}

	private GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> interferenceFixpoint(
			final Set<String> interferingThreads, final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> state,
			final String ownerThread) {
		mIterations = 0;
		var newState = state;
		mForked = false;
		while (true) {
			mIterations++;
			// state just to check if fixpoint reached after this iteration
			final var beginLoopState = new GuardedInterferenceDomainStateDisj<>(newState);

			for (final String interferenceThreadName : interferingThreads) {
				final var interferences = mInterferences.getInterferenceMapHashRelation().get(interferenceThreadName);
				if (mInterferences.getInterferencesForThread(interferenceThreadName) == null) {
					continue;
				}
				newState = newState
						.union(applyInterferences(newState, interferences, ownerThread, interferenceThreadName));
			}
			final boolean changed = newState.isSubsetOf(beginLoopState) != SubsetResult.NONE ? false : true;
			if (!changed) {
				break;
			}
		}
//		mLogger.info("state after interferences: " + newState);
		if (mForked) {
			// TODO: we can solve this less costly probably (we just want to go again, with superset of interferenceset)
			return newState.union(stateAfterInterferences(newState, ownerThread));
		}
		return newState;
	}

	private GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> applyInterferences(
			GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> newState,
			final Set<Interference<STATE, ACTION, LOC>> interferences, final String ownerThread,
			final String interferenceThreadName) {
		for (final Interference<STATE, ACTION, LOC> interference : interferences) {
			// 1. check threadcounter (is interfering thread alive in our state?)
			if (interference.threadcounter().getThreadInstances().get(ownerThread) == 0) {
				continue;
			}
//			mLogger.warn("Applying interference: " + interference.toString());
//			mLogger.warn("to state: " + newState.getSingleState());
			if (interference.action() instanceof final ForkThreadCurrent fork) {
				newState = newState.union(handleFork(newState, fork));
				continue;
			}

			final var postState = applyInterferenceToDisjunctiveState(interference, newState, interferenceThreadName,
					ownerThread);
			// empty when we encountered bottomstate
			if (postState.isEmpty()) {
				continue;
			}

			if (mIterations < 10) {
				newState = newState.union(postState);
			} else {
				newState = mGuardedInterferenceDomain.getWideningOperator().apply(newState, postState);
				mLogger.error("DID POSTOPERATOR WIDENING: " + newState);
				return newState;
			}
			if (newState.isBottom()) {
				return newState;
			}
		}
		return newState;
	}

	private GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> handleFork(
			GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> newState, final ForkThreadCurrent fork) {
		final int beforeFork = newState.getThreadInstanceState().getThreadInstances()
				.get(fork.getNameOfForkedProcedure());
		newState = newState.union(newState.setThreadsActive(Set.of(fork.getNameOfForkedProcedure())));
		final int afterFork = newState.getThreadInstanceState().getThreadInstances()
				.get(fork.getNameOfForkedProcedure());
		if (beforeFork < afterFork) {
			mForked = true;
		}
		return newState;
	}

	private GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> applyInterferenceToDisjunctiveState(
			final Interference<STATE, ACTION, LOC> interference,
			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> newState, final String interferenceThreadName,
			final String ownerThread) {

//		final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> resultDisj = null;
		final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> disjunction = new HashSet<>();
		for (final GuardedInterferenceDomainState<STATE, ACTION, LOC> singleState : newState.getStates()) {
			// 2. check abstract locations (is interfering thread in location where it matches the interference
			// action)
			final Set<Integer> possibleInterferingLocations = singleState.abstractLocationState().getTracker()
					.getLocationForThread(interferenceThreadName);
			final int interferenceLocation = mAbstractLocationMap
					.getAbstractLocation(interference.action().getSource());
			if ((!possibleInterferingLocations.contains(interferenceLocation)
					|| !(singleState.threadCounter().getThreadInstances().get(interferenceThreadName) > 0))
					&& !(ownerThread == interferenceThreadName)) {
				continue;
			}
			final var pair = new InterferenceStatePair<>(interference, singleState);
			// if in cache, return state with cached underlying state without applying postOp
			if (mInterferenceCache.get(pair) != null) {
//				mLogger.error("Using cached state computation");
				disjunction.add(mInterferenceCache.get(pair));
			} else {
				final var interferedState = applyInterferenceToSTATE(interference, singleState);
				if (interferedState == null) {
					continue;
				}
				mInterferenceCache.put(pair, interferedState);
				disjunction.add(interferedState);
			}
		}
		return new GuardedInterferenceDomainStateDisj<>(mUnderlyingDomain, disjunction, MAXITF);
	}

	private GuardedInterferenceDomainState<STATE, ACTION, LOC> applyInterferenceToSTATE(
			final Interference<STATE, ACTION, LOC> interference,
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> singleState) {
		// add variables to both states to be able to intersect
		final STATE interferingState = interference.state();
		final STATE stateState = singleState.state();
		final var missingLocals = DataStructureUtils.difference(stateState.getVariables(),
				interferingState.getVariables());
		final var missingLocals2 = DataStructureUtils.difference(interferingState.getVariables(),
				stateState.getVariables());
		if (stateState.isBottom() || interferingState.isBottom()) {
//			return Collections.emptyList();
			return null;
		}
		final STATE intersectionState = stateState.addVariables(missingLocals2)
				.intersect(interferingState.addVariables(missingLocals));
		if (intersectionState.isBottom()) {
//			return Collections.emptyList();
			return null;
		}
		// postop
		Collection<STATE> postState = mUnderlyingPostOp.apply(intersectionState, interference.action());
		// TODO: sound?
		if (postState.isEmpty()) {
			return singleState;
		}
		postState = postState.stream().map(s -> s.removeVariables(missingLocals2)).collect(Collectors.toList());
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

	@Override
	public List<GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC>> apply(
			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> stateBeforeLeaving,
			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> secondState, final ACTION transition) {
		throw new UnsupportedOperationException("Not implemented.");
	}

	@Override
	public EvalResult evaluate(final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> state, final Term formula,
			final Script script) {
		throw new UnsupportedOperationException("Not implemented.");
	}
}
