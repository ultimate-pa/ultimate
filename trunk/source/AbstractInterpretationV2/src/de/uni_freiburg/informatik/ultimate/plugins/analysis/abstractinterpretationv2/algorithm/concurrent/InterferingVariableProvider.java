package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;

public class InterferingVariableProvider<STATE extends IAbstractState<STATE>, ACTION>
		implements IVariableProvider<STATE, ACTION> {
	private final IVariableProvider<STATE, ACTION> mUnderlying;
	private final DisjunctiveAbstractState<STATE> mInterferingState;

	public InterferingVariableProvider(final IVariableProvider<STATE, ACTION> underlying,
			final DisjunctiveAbstractState<STATE> interferingState) {
		mUnderlying = underlying;
		mInterferingState = interferingState;
	}

	@Override
	public DisjunctiveAbstractState<STATE> defineInitialVariables(final ACTION current,
			final DisjunctiveAbstractState<STATE> state) {
		return mUnderlying.defineInitialVariables(current, mInterferingState);
	}

	@Override
	public STATE defineVariablesAfter(final ACTION current, final STATE localPreState,
			final STATE hierachicalPreState) {
		return mUnderlying.defineVariablesAfter(current, localPreState, hierachicalPreState);
	}

	@Override
	public STATE createValidPostOpStateAfterLeaving(final ACTION act, final STATE origPreLinState,
			final STATE preHierState) {
		return mUnderlying.createValidPostOpStateAfterLeaving(act, origPreLinState, preHierState);
	}

	@Override
	public STATE createValidPostOpStateBeforeLeaving(final ACTION action, final STATE stateHier) {
		return mUnderlying.createValidPostOpStateBeforeLeaving(action, stateHier);
	}

	@Override
	public IVariableProvider<STATE, ACTION> createNewVariableProvider(final CfgSmtToolkit toolkit) {
		return mUnderlying.createNewVariableProvider(toolkit);
	}

	@Override
	public Set<IProgramVarOrConst> getRequiredVars(final ACTION act) {
		return mUnderlying.getRequiredVars(act);
	}

}
