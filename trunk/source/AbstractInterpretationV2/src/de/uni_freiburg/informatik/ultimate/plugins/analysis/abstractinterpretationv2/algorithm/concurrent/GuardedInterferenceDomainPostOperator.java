package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class GuardedInterferenceDomainPostOperator<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>
		implements IAbstractPostOperator<GuardedInterferenceDomainState<STATE, ACTION>, ACTION> {
	private String mCurrentThreadName;

	private final ILogger mLogger;

	private AbstractInterferenceState<STATE, ACTION> mInterferences;
	private AbstractInterferenceState<STATE, ACTION> mNewInterferences;
	private final CfgSmtToolkit mToolkit;
	private final IAbstractDomain<STATE, ACTION> mUnderlyingDomain;
	private final IAbstractPostOperator<STATE, ACTION> mUnderlyingPostOp;
	private final GuardedInterferenceDomain<STATE, ACTION, LOC> mGuardedInterferenceDomain;
	private final Set<IProgramNonOldVar> mGlobalVariables;
	private final Map<InterferenceStatePair<STATE, ACTION, LOC>, STATE> mInterferenceCache = new HashMap<>();

	private final int MAXITF = 9;
	private int mIterations;
	private boolean mForked = false;

	public GuardedInterferenceDomainPostOperator(final IIcfg<?> cfg, final ILogger logger,
			final IAbstractDomain<STATE, ACTION> underlying, final IAbstractPostOperator<STATE, ACTION> postOp,
			final GuardedInterferenceDomain<STATE, ACTION, LOC> relationalInterferingDomain,
			final AbstractInterferenceState<STATE, ACTION> interferenceState) {
		mLogger = logger;
		mToolkit = cfg.getCfgSmtToolkit();
		mUnderlyingDomain = underlying;
		mUnderlyingPostOp = postOp;
		mGuardedInterferenceDomain = relationalInterferingDomain;
		mGlobalVariables = mToolkit.getSymbolTable().getGlobals();
		mInterferences = interferenceState;
		mNewInterferences = new AbstractInterferenceState<>(cfg.getCfgSmtToolkit().getProcedures());
	}

	public AbstractInterferenceState<STATE, ACTION> getInterferences() {
		return mInterferences;
	}

	public void setInterferences(final AbstractInterferenceState<STATE, ACTION> newState) {
		mInterferences = newState;
	}

	public void updateInterferences() {
		mInterferences = new AbstractInterferenceState<>(mNewInterferences);
		mNewInterferences = new AbstractInterferenceState<>(mToolkit.getProcedures());
	}

	@Override
	public Collection<GuardedInterferenceDomainState<STATE, ACTION>> apply(
			final GuardedInterferenceDomainState<STATE, ACTION> oldstate, final ACTION transition) {
		if (oldstate.isBottom()) {
			return List.of(oldstate);
		}
		mCurrentThreadName = transition.getPrecedingProcedure();

		// handle fork differently
		if (transition instanceof ForkThreadCurrent || transition instanceof ForkThreadOther) {
			return applyFork(oldstate, transition);
		}

		// 1. normal poststate
		var postRelationalState = new GuardedInterferenceDomainState<>(mUnderlyingDomain,
				mUnderlyingPostOp.apply(oldstate.getUnderlyingState(), transition), oldstate.getThreadInstanceState());
		mLogger.info("post(" + oldstate.toLogString() + ", " + transition + ") = " + postRelationalState);

		// 2. Add new interference to global map
		if (isInterferingTransition(transition)) {
			mNewInterferences.addInterference(mCurrentThreadName, transition, oldstate.getUnderlyingState(),
					oldstate.getThreadInstanceState());
		}

		// 3. apply interferences
		postRelationalState = stateAfterInterferences(postRelationalState, mCurrentThreadName);

		return List.of(postRelationalState);
	}

	private boolean isInterferingTransition(final ACTION transition) {
		if (!transition.getTransformula().getAssignedVars().stream()
				.anyMatch(assignedVar -> mGlobalVariables.contains(assignedVar))) {
			return false;
		}
		if (!(transition instanceof final StatementSequence statementSequence)) {
			return true;
		}
		for (final Statement statement : statementSequence.getStatements()) {
			if (!(statement instanceof AssumeStatement)) {
				return true;
			}
		}
		return false;
	}

	private Collection<GuardedInterferenceDomainState<STATE, ACTION>> applyFork(
			final GuardedInterferenceDomainState<STATE, ACTION> oldstate, final ACTION transition) {

		var newState = new GuardedInterferenceDomainState<>(mUnderlyingDomain, oldstate.getUnderlyingState(),
				oldstate.getThreadInstanceState());
		if (transition instanceof final ForkThreadCurrent fork1) {
			final boolean circular = isCircular(fork1, fork1.getSource().getIncomingEdges(), 0);
			final var forked = fork1.getNameOfForkedProcedure();
			newState = newState.incrementThread(forked);
			if (circular || oldstate.getThreadInstanceState().getThreadInstances().get(forked) > 0) {
				newState = newState.setThreadsInf(List.of(forked));
			}
		} else {
			throw new IllegalArgumentException("Unsupported fork transition type");
		}
		// apply interferences
		newState = stateAfterInterferences(newState, mCurrentThreadName);
		mNewInterferences.addForkInterference(mCurrentThreadName, transition, oldstate.getUnderlyingState(),
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

	public GuardedInterferenceDomainState<STATE, ACTION> stateAfterInterferences(
			final GuardedInterferenceDomainState<STATE, ACTION> oldstate, final String ownerThread) {

		// this check might cost more time than it saves, if we don't encounter a lot of top-states
		final var topstate = mUnderlyingDomain.createTopState();
		if (topstate.addVariables(DataStructureUtils.difference(oldstate.getVariables(), topstate.getVariables()))
				.isSubsetOf(oldstate.getUnderlyingState()) != SubsetResult.NONE) {
			return oldstate;
		}

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
			Interference<STATE, ACTION> interf, STATE targetState) {
	}

	private GuardedInterferenceDomainState<STATE, ACTION> interferenceFixpoint(final Set<String> interferingThreads,
			final GuardedInterferenceDomainState<STATE, ACTION> state, final String ownerThread) {
		mIterations = 0;
		var newState = state;
		mForked = false;
		while (true) {
			mIterations++;
			// state just to check if fixpoint reached
			final var beginLoopState = new GuardedInterferenceDomainState<>(mUnderlyingDomain,
					newState.getUnderlyingState(), newState.getThreadInstanceState());

			for (final String interferenceThreadName : interferingThreads) {
				final var interferences = mInterferences.getInterferenceMapHashRelation().get(interferenceThreadName);
				if (mInterferences.getInterferencesForThread(interferenceThreadName) == null) {
					continue;
				}
				newState = newState.union(applyInterferences(newState, interferences, ownerThread));
			}
			final boolean changed = newState.isSubsetOf(beginLoopState) != SubsetResult.NONE ? false : true;
			if (!changed) {
				break;
			}
		}
		mLogger.info("state after interferences: " + newState);
		if (mForked) {
			// TODO: we can solve this less costly probably (we just want to go again, with superset of interferenceset)
			return newState.union(stateAfterInterferences(newState, ownerThread));
		}
		return newState;
	}

	private GuardedInterferenceDomainState<STATE, ACTION> applyInterferences(
			GuardedInterferenceDomainState<STATE, ACTION> newState,
			final Set<Interference<STATE, ACTION>> interferences, final String ownerThread) {
		for (final Interference<STATE, ACTION> interference : interferences) {
			if (interference.threadcounter().getThreadInstances().get(ownerThread) == 0) {
				continue;
			}
			mLogger.info("Applying interference: " + interference.toString() + "to state: " + newState.toLogString());
			if (interference.action() instanceof final ForkThreadCurrent fork) {
				newState = newState.union(handleFork(newState, fork));
				continue;
			}
			final var pair = new InterferenceStatePair<>(interference, newState.getUnderlyingState());

			final var postStateUnderlying = computeOrGetPoststate(interference, newState, pair);
			// empty when we encountered bottomstate
			if (postStateUnderlying.isEmpty()) {
				continue;
			}
			final var postState = new GuardedInterferenceDomainState<>(mUnderlyingDomain, postStateUnderlying,
					newState.getThreadInstanceState());

			if (mIterations < MAXITF) {
				newState = newState.union(postState);
				mLogger.info("result: " + newState);
			} else {
				newState = mGuardedInterferenceDomain.getWideningOperator().apply(newState, postState);
				mLogger.warn("DID POSTOPERATOR WIDENING: " + newState);
			}
			if (newState.isBottom()) {
				return newState;
			}
			mInterferenceCache.put(pair, newState.getUnderlyingState());
		}
		return newState;
	}

	private GuardedInterferenceDomainState<STATE, ACTION> handleFork(
			GuardedInterferenceDomainState<STATE, ACTION> newState, final ForkThreadCurrent fork) {
		final int beforeFork = newState.getThreadInstanceState().getThreadInstances()
				.get(fork.getNameOfForkedProcedure());
		newState = newState.union(newState.incrementThread(fork.getNameOfForkedProcedure()));
		final int afterFork = newState.getThreadInstanceState().getThreadInstances()
				.get(fork.getNameOfForkedProcedure());
		if (beforeFork < afterFork) {
			mForked = true;
		}
		return newState;
	}

	private Collection<STATE> computeOrGetPoststate(final Interference<STATE, ACTION> interference,
			final GuardedInterferenceDomainState<STATE, ACTION> newState,
			final InterferenceStatePair<STATE, ACTION, LOC> pair) {

		// if in cache, return state with cached underlying state without applying postOp
		if (mInterferenceCache.get(pair) != null) {
			mLogger.error("Using cached state computation");
			return List.of(mInterferenceCache.get(pair));
		}

		// add variables to both states to be able to intersect
		final STATE interferingState = interference.state();
		final var missingLocals = DataStructureUtils.difference(newState.getVariables(),
				interferingState.getVariables());
		final var missingLocals2 = DataStructureUtils.difference(interferingState.getVariables(),
				newState.getVariables());
		if (newState.getUnderlyingState().isBottom() || interferingState.isBottom()) {
			return Collections.emptyList();
		}
		final STATE intersectionState = newState.getUnderlyingState().addVariables(missingLocals2)
				.intersect(interferingState.addVariables(missingLocals));
		if (intersectionState.isBottom()) {
			return Collections.emptyList();
		}

		// apply underlying postOp
		Collection<STATE> postState = mUnderlyingPostOp.apply(intersectionState, interference.action());
		postState = postState.stream().map(s -> s.removeVariables(missingLocals2)).collect(Collectors.toList());
		return postState;
	}

	@Override
	public List<GuardedInterferenceDomainState<STATE, ACTION>> apply(
			final GuardedInterferenceDomainState<STATE, ACTION> stateBeforeLeaving,
			final GuardedInterferenceDomainState<STATE, ACTION> secondState, final ACTION transition) {
		throw new UnsupportedOperationException("Not implemented.");
	}

	@Override
	public EvalResult evaluate(final GuardedInterferenceDomainState<STATE, ACTION> state, final Term formula,
			final Script script) {
		throw new UnsupportedOperationException("Not implemented.");
	}
}
