package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;

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
		final Collection<STATE> postStates = mUnderlying.apply(oldstate, transition);
		final DisjunctiveAbstractState<STATE> interfereringDisjunctiveState =
				mInterferences.get(mTransitionProvider.getTarget(transition));
		if (interfereringDisjunctiveState == null) {
			return postStates;
		}
		final Set<STATE> interferingStates = interfereringDisjunctiveState.getStates();
		final List<STATE> result = new ArrayList<>(postStates.size() * interferingStates.size());
		for (final STATE postState : postStates) {
			// Ignore interferences in bottom-states
			// TODO: Is this sound? Could we generalize this (e.g. check some state inclusion)?
			if (postState.isBottom()) {
				result.add(postState);
				continue;
			}
			interferingStates
					.forEach(s -> result.add(FixpointEngineConcurrentUtils.unionOnSharedVariables(postState, s)));
		}
		return result;
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
