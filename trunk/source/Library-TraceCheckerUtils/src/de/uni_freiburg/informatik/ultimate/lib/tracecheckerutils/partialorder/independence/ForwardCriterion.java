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
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.LoopLockstepOrder.PredicateWithLastThread;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.SleepSetStateFactoryForRefinement.SleepPredicate;

public class ForwardCriterion<L extends IIcfgTransition<?>> implements IConditionalCommutativityCriterion<L> {

	private INwaOutgoingLetterAndTransitionProvider<L,IPredicate> mAbstraction;
	private IIndependenceRelation<IPredicate, L> mIndependenceRelation;

	public ForwardCriterion(final INwaOutgoingLetterAndTransitionProvider<L,IPredicate> abstraction,
			final IIndependenceRelation<IPredicate, L> independenceRelation){
		mAbstraction = abstraction;
		mIndependenceRelation = independenceRelation;
	}
	
	@Override
	public boolean decide(IPredicate state, L letter1, L letter2) {
			
		IPredicate nextState;
		state = ((SleepPredicate) state).getUnderlying();
		if (state instanceof PredicateWithLastThread) {
			state = ((PredicateWithLastThread) state).getUnderlying();
		}

		for (OutgoingInternalTransition<L, IPredicate> transition : mAbstraction.internalSuccessors(state, letter1)) {
			nextState = transition.getSucc();
			for (OutgoingInternalTransition<L, IPredicate> nextTransition : mAbstraction.internalSuccessors(nextState)) {
				if (mIndependenceRelation.isIndependent(state, nextTransition.getLetter(), letter2).equals(Dependence.INDEPENDENT)) {
					return true;
				}
			}
	
		}
		for (OutgoingInternalTransition<L, IPredicate> transition : mAbstraction.internalSuccessors(state, letter2)) {
			nextState = transition.getSucc();
			for (OutgoingInternalTransition<L, IPredicate> nextTransition : mAbstraction.internalSuccessors(nextState)) {
				if (mIndependenceRelation.isIndependent(state, nextTransition.getLetter(), letter1).equals(Dependence.INDEPENDENT)) {
					return true;
				}
			}
	
		}
		return false;
	}

	@Override
	public boolean decide(IPredicate condition) {
		// TODO Auto-generated method stub
		return true;
	}

	@Override
	public void updateAbstraction(INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction) {
		mAbstraction = abstraction;
		
	}

	@Override
	public void updateCriterion(IPredicate state, L letter1, L letter2) {
		// TODO Auto-generated method stub
		
	}

}
