package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadCurrent;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadOther;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;

public class RelationalInterferingPostOperator<STATE extends IAbstractState<STATE>, ACTION>
		implements IAbstractPostOperator<RelationalInterferingState<STATE, ACTION>, ACTION> {
	private String mCurrentThreadName;

	private final ILogger mLogger;

	private AbstractInterferenceState<STATE, ACTION> mInterferences;
	private AbstractInterferenceState<STATE, ACTION> mNewInterferences;
	private final CfgSmtToolkit mToolkit;
	private final IAbstractDomain<STATE, ACTION> mUnderlyingDomain;
	private final IAbstractPostOperator<STATE, ACTION> mUnderlyingPostOp;
	private final RelationalInterferingDomain<STATE, ACTION> mRelationalInterferingDomain;
	private final Set<IProgramNonOldVar> mGlobalVariables;

	public RelationalInterferingPostOperator(final IIcfg<?> cfg, final ILogger logger,
			final IAbstractDomain<STATE, ACTION> underlying, final IAbstractPostOperator<STATE, ACTION> postOp,
			final RelationalInterferingDomain<STATE, ACTION> relationalInterferingDomain,
			final AbstractInterferenceState<STATE, ACTION> interferenceState) {
		mLogger = logger;
		mToolkit = cfg.getCfgSmtToolkit();
		mUnderlyingDomain = underlying;
		mUnderlyingPostOp = postOp;
		mRelationalInterferingDomain = relationalInterferingDomain;
		mGlobalVariables = mToolkit.getSymbolTable().getGlobals();
		mInterferences = interferenceState;
		mNewInterferences = new AbstractInterferenceState<>(cfg.getCfgSmtToolkit().getProcedures());
	}

	@Override
	public Collection<RelationalInterferingState<STATE, ACTION>>
			apply(final RelationalInterferingState<STATE, ACTION> oldstate, final ACTION transition) {
		if (oldstate.isBottom()) {
			return List.of(oldstate);
		}
		mLogger.warn("START postOperator----------------");
		mLogger.warn("current Thread: " + ((IcfgEdge) transition).getPrecedingProcedure());
		mCurrentThreadName = ((IcfgEdge) transition).getPrecedingProcedure();

		if (transition instanceof ForkThreadCurrent || transition instanceof ForkThreadOther) {
			mLogger.warn("Fork transition, no postOp, no interference created");
			return applyFork(oldstate, transition);
		}
		mLogger.warn("Applying postoperator to ");
		mLogger.warn("state: " + oldstate.toLogString());
		mLogger.warn("transitionTerm: " + transition);
		mLogger.info("locals: " + mToolkit.getSymbolTable().getLocals(mCurrentThreadName));

		// 1. normal poststate
		var postRelationalState = new RelationalInterferingState<>(mUnderlyingDomain,
				mUnderlyingPostOp.apply(oldstate.getStateCopy(), transition), oldstate.getThreadInstanceState());
		mLogger.warn("state after: " + postRelationalState);

		// TODO: alpha it ?
		// alpha(state) (TODO: atm doesnt alpha thread/loc info)

		// 2. Add new interference to global map
		if (isInterferingTransition(transition)) {
			mNewInterferences.addInterference(mCurrentThreadName, transition, oldstate.getStateCopy(),
					oldstate.getThreadInstanceState());
			mLogger.warn("Interference created: " + oldstate.getStateCopy().toLogString() + " "
					+ ((IAction) transition).getTransformula().toStringDirect());
		}

		// 3. apply interferences
		// TODO: check if topstate/bot
		postRelationalState = stateAfterInterferences(postRelationalState, mCurrentThreadName);

		mLogger.warn("----------------END postOperator");
		return List.of(postRelationalState);
	}

	private boolean isInterferingTransition(final ACTION transition) {
		if (!((IAction) transition).getTransformula().getAssignedVars().stream()
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

	private Collection<RelationalInterferingState<STATE, ACTION>>
			applyFork(final RelationalInterferingState<STATE, ACTION> oldstate, final ACTION transition) {

		var newState = new RelationalInterferingState<>(mUnderlyingDomain, oldstate.getStateCopy(),
				oldstate.getThreadInstanceState());
		// increment threadcounter of forked thread and all threads who are forked, etc,
		// by forked
		// TODO: we can reduce logic now after changes, just check if more than 2 forks
		// exist, or circular
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
		mNewInterferences.addForkInterference(mCurrentThreadName, transition, oldstate.getStateCopy(),
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

	public RelationalInterferingState<STATE, ACTION> stateAfterInterferences(
			final RelationalInterferingState<STATE, ACTION> oldstate, final String ownerThread) {
		mLogger.warn("state before interferences: " + oldstate);
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

	private RelationalInterferingState<STATE, ACTION> interferenceFixpoint(final Set<String> interferenceSet,
			final RelationalInterferingState<STATE, ACTION> state, final String ownerThread) {
		int iterations = 0;
		var newState = state;
		boolean changed = true;
		boolean forked = false;
		final Set<Interference<STATE, ACTION>> appliedInterferenceSet = new HashSet<>();
		while (changed) {
			iterations++;
			// state just to check if fixpoint reached
			final var beginLoopState = new RelationalInterferingState<>(mUnderlyingDomain, newState.getStateCopy(),
					newState.getThreadInstanceState());

			for (final String interferenceThreadName : interferenceSet) {
				final var interferences = mInterferences.getInterferenceMapHashRelation().get(interferenceThreadName);
				if (mInterferences.getInterferencesForThread(interferenceThreadName) == null) {
					continue;
				}
				for (final Interference<STATE, ACTION> interference : interferences) {
					// We don't apply interferences which were created with a superset of threads active compared to the
					// current state.
					// if (!interference.threadcounter().isEqual(state.getThreadInstanceState())) {
					if (interference.threadcounter().getThreadInstances().get(ownerThread) == 0) {
						continue;
					}
					mLogger.warn("Applying interference: " + interference.toString());
					appliedInterferenceSet.add(interference);
					mLogger.warn("to state: " + newState.toLogString());

					if (interference.action() instanceof final ForkThreadCurrent fork1) {
						final int beforeFork = newState.getThreadInstanceState().getThreadInstances()
								.get(fork1.getNameOfForkedProcedure());
						newState = newState.union(newState.incrementThread(fork1.getNameOfForkedProcedure()));
						final int afterFork = newState.getThreadInstanceState().getThreadInstances()
								.get(fork1.getNameOfForkedProcedure());
						if (beforeFork < afterFork) {
							forked = true;
						}
						continue;
					}
					final STATE interferingState = interference.state();
					// TODO: datastructureutiles difference
					// DataStructureUtils.difference(null, null);
					final var locals =
							newState.getVariables().stream().filter(v -> !v.isGlobal()).collect(Collectors.toSet());
					final var otherLocals = interferingState.getVariables();
					final var missingLocals =
							locals.stream().filter(v -> !otherLocals.contains(v)).collect(Collectors.toSet());

					final var locals2 = interferingState.getVariables().stream().filter(v -> !v.isGlobal())
							.collect(Collectors.toSet());
					final var otherlocals2 = newState.getStateCopy().getVariables();
					final var missingLocals2 =
							locals2.stream().filter(v -> !otherlocals2.contains(v)).collect(Collectors.toSet());

					final var globalNewState = newState.getStateCopy().addVariables(missingLocals2);
					if (globalNewState.isBottom() || interferingState.isBottom()) {
						continue;
					}
					final STATE intersectionState =
							globalNewState.intersect(interferingState.addVariables(missingLocals));
					if (intersectionState.isBottom()) {
						continue;
					}
					var postState = new RelationalInterferingState<>(mUnderlyingDomain,
							mUnderlyingPostOp.apply(intersectionState, interference.action()),
							newState.getThreadInstanceState());
					postState = postState.removeVariables(missingLocals2);

					if (iterations < 2) {
						newState = newState.union(postState);
						mLogger.warn("result: " + newState);
					} else {
						newState = mRelationalInterferingDomain.getWideningOperator().apply(newState, postState);
						mLogger.error("DID POSTOP WIDENING");
						mLogger.warn("Widening result: " + newState);
					}
					if (newState.isBottom()) {
						mLogger.warn("aborting interferencefixpoint, state is bottom");
						return newState;
					}
				}
			}
			changed = newState.isSubsetOf(beginLoopState) != SubsetResult.NONE ? false : true;
		}
		mLogger.warn("used: " + appliedInterferenceSet);
		mLogger.warn("state after interferences: " + newState);
		if (forked) {
			// TODO: we can solve this less costly probably (we just want to go again, with superset of interferenceset)
			return newState.union(stateAfterInterferences(newState, ownerThread));
		}
		return newState;
	}

	@Override
	public List<RelationalInterferingState<STATE, ACTION>> apply(
			final RelationalInterferingState<STATE, ACTION> stateBeforeLeaving,
			final RelationalInterferingState<STATE, ACTION> secondState, final ACTION transition) {
		throw new UnsupportedOperationException("Not implemented.");
	}

	@Override
	public EvalResult evaluate(final RelationalInterferingState<STATE, ACTION> state, final Term formula,
			final Script script) {
		throw new UnsupportedOperationException("Not implemented.");
	}

	public void updateInterferences() {
		mInterferences = new AbstractInterferenceState<>(mNewInterferences);
		mNewInterferences = new AbstractInterferenceState<>(mToolkit.getProcedures());
	}

	public AbstractInterferenceState<STATE, ACTION> getInterferences() {
		return mInterferences;
	}
}
