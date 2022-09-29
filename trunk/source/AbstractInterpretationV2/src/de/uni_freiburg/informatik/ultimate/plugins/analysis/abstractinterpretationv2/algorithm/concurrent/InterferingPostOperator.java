package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class InterferingPostOperator<STATE extends IAbstractState<STATE>, ACTION, LOC>
		implements IAbstractPostOperator<STATE, ACTION> {
	private final ITransitionProvider<ACTION, LOC> mTransitionProvider;
	private final Map<LOC, DisjunctiveAbstractState<STATE>> mInterferences;
	private final IAbstractPostOperator<STATE, ACTION> mUnderlying;

	public InterferingPostOperator(final ITransitionProvider<ACTION, LOC> transitionProvider,
			final Map<LOC, DisjunctiveAbstractState<STATE>> interferences,
			final IAbstractPostOperator<STATE, ACTION> underlying) {
		mTransitionProvider = transitionProvider;
		mInterferences = interferences;
		mUnderlying = underlying;
	}

	@Override
	public Collection<STATE> apply(final STATE oldstate, final ACTION transition) {
		final DisjunctiveAbstractState<STATE> interferences =
				mInterferences.get(mTransitionProvider.getTarget(transition));
		return mUnderlying.apply(oldstate, transition).stream().map(x -> addInterferences(x, interferences))
				.collect(Collectors.toList());
	}

	private STATE addInterferences(final STATE state, final DisjunctiveAbstractState<STATE> interferences) {
		if (interferences == null) {
			return state;
		}
		final STATE interferingState = interferences.getSingleState(STATE::union);
		final Set<IProgramVarOrConst> sharedVars =
				DataStructureUtils.intersection(interferingState.getVariables(), state.getVariables());
		final STATE unionOnSharedVars =
				keepVariables(state, sharedVars).union(keepVariables(interferingState, sharedVars));
		return state.patch(unionOnSharedVars);
	}

	private static <STATE extends IAbstractState<STATE>> STATE keepVariables(final STATE state,
			final Set<IProgramVarOrConst> vars) {
		return state.removeVariables(DataStructureUtils.difference(state.getVariables(), vars));
	}

	@Override
	public List<STATE> apply(final STATE stateBeforeLeaving, final STATE secondState, final ACTION transition) {
		throw new UnsupportedOperationException(
				"Calls and returns are not supported in thread-modular abstract interpretation.");
	}

	@Override
	public EvalResult evaluate(final STATE state, final Term formula, final Script script) {
		return mUnderlying.evaluate(state, formula, script);
	}

}
