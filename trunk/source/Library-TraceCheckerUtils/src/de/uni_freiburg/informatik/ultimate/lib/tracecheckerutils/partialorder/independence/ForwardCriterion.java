/*
 * Copyright (C) 2024 Marcel Ebbinghaus
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.PartialOrderReductionFacade.StateSplitter;

/**
 * Forward criterion which checks whether one of the letters commutes with any other letter in its successor state.
 * 
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 *            Letter type
 */
public class ForwardCriterion<L extends IIcfgTransition<?>> implements IConditionalCommutativityCriterion<L> {

	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mAbstraction;
	private final IIndependenceRelation<IPredicate, L> mIndependenceRelation;
	private StateSplitter<IPredicate> mStateSplitter;

	/**
	 * Constructor.
	 * 
	 * @param abstraction
	 *            Abstraction
	 * @param independenceRelation
	 *            The used independence relation
	 * @param splitter
	 *            Splitter to retrieve the predicate
	 */
	public ForwardCriterion(final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction,
			final IIndependenceRelation<IPredicate, L> independenceRelation, final StateSplitter<IPredicate> splitter) {
		mAbstraction = abstraction;
		mIndependenceRelation = independenceRelation;
		mStateSplitter = splitter;
	}

	@Override
	public boolean decide(IPredicate state, final L letter1, final L letter2) {
		IPredicate nextState;

		state = mStateSplitter.getOriginal(state);
		for (final OutgoingInternalTransition<L, IPredicate> transition : mAbstraction.internalSuccessors(state,
				letter1)) {
			nextState = transition.getSucc();
			for (final OutgoingInternalTransition<L, IPredicate> nextTransition : mAbstraction
					.internalSuccessors(nextState)) {
				if (mIndependenceRelation.isIndependent(state, nextTransition.getLetter(), letter2)
						.equals(Dependence.INDEPENDENT)) {
					return true;
				}
			}
		}
		for (final OutgoingInternalTransition<L, IPredicate> transition : mAbstraction.internalSuccessors(state,
				letter2)) {
			nextState = transition.getSucc();
			for (final OutgoingInternalTransition<L, IPredicate> nextTransition : mAbstraction
					.internalSuccessors(nextState)) {
				if (mIndependenceRelation.isIndependent(state, nextTransition.getLetter(), letter1)
						.equals(Dependence.INDEPENDENT)) {
					return true;
				}
			}
		}
		return false;
	}

	@Override
	public boolean decide(final IPredicate condition) {
		// no filtering based on condition
		return true;
	}

	@Override
	public void updateAbstraction(final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction) {
		mAbstraction = abstraction;
	}
}
