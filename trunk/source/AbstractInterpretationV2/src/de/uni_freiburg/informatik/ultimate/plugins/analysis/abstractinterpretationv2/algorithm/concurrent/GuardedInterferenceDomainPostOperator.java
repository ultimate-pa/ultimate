package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
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

public class GuardedInterferenceDomainPostOperator<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>
		implements IAbstractPostOperator<GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC>, ACTION> {
	private String mCurrentThreadName;

	private final ILogger mLogger;
	private final Set<IProgramNonOldVar> mGlobalVariables;
	private final IAbstractPostOperator<STATE, ACTION> mUnderlyingPostOp;
	private final GuardedInterferenceApplier<STATE, ACTION, LOC> mItfApplier;

	public GuardedInterferenceDomainPostOperator(final IIcfg<?> cfg, final ILogger logger,
			final IAbstractDomain<STATE, ACTION> underlying, final IAbstractPostOperator<STATE, ACTION> postOp,
			final GuardedInterferenceDomain<STATE, ACTION, LOC> relationalInterferingDomain,
			final AbstractInterferenceState<STATE, ACTION, LOC> interferenceState,
			final AbstractLocationMap<LOC> globalMap, final int maxItf) {
		mLogger = logger;
		mGlobalVariables = cfg.getCfgSmtToolkit().getSymbolTable().getGlobals();
		mUnderlyingPostOp = postOp;
		mItfApplier = new GuardedInterferenceApplier<>(cfg, logger, underlying, postOp, relationalInterferingDomain,
				interferenceState, globalMap, maxItf);
	}

	public GuardedInterferenceApplier<STATE, ACTION, LOC> getItfApplier() {
		return mItfApplier;
	}

	@Override
	public Collection<GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC>> apply(
			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> oldstate, final ACTION transition) {
		if (oldstate.isStateBottom()) {
			return List.of(oldstate);
		}
		mCurrentThreadName = transition.getPrecedingProcedure();

		// handle fork differently
		if (transition instanceof ForkThreadCurrent || transition instanceof ForkThreadOther) {
			return applyFork(oldstate, transition);
		}

		// 1. normal poststate
		GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> postRelationalState = oldstate.apply(mUnderlyingPostOp,
				transition);

		// 2. Add new interference to global map
		if (isInterferingTransition(transition) || true) {
			mItfApplier.addItf(mCurrentThreadName, transition, oldstate);
		}

		// 3. apply interferences
		if (!postRelationalState.isBottom()) {
			postRelationalState = mItfApplier.stateAfterInterferences(postRelationalState, mCurrentThreadName);
		}

		return List.of(postRelationalState);
	}

	// with naive location abstraction we cannot skip any interferences, even if they are a "skip"
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
		newState = mItfApplier.stateAfterInterferences(newState, mCurrentThreadName);
		mItfApplier.addItf(mCurrentThreadName, transition, oldstate);
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
