/*
 * Copyright (C) 2022 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

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

/**
 * Wrapper for an {@code IAbstractPostOperator} that adds interferences to the post states.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
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
