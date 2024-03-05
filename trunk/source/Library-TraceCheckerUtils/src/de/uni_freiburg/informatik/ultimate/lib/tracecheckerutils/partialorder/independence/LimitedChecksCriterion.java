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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.AnnotatedMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.MLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.LoopLockstepOrder.PredicateWithLastThread;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.SleepSetStateFactoryForRefinement.SleepPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Criterion for conditional commutativity checking with limited checks.
 *
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 *            The type of letters.
 */
public class LimitedChecksCriterion<L> implements IConditionalCommutativityCriterion<L> {

	private Map<Pair<L,L>, List<IPredicate>> mAlreadyChecked;
	private List<IPredicate> mAlreadyProofenConditions;
	private Map<Pair<L, L>, Integer> mStatementMap;
	
	/**
	 * Constructor.
	 *
	 * @author Marcel Ebbinghaus
	 */
	public LimitedChecksCriterion() {
		mAlreadyChecked = new HashMap<>();
		mAlreadyProofenConditions = new ArrayList<>();
		mStatementMap = new HashMap<>();
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public boolean decide(final IPredicate state, final IRun<L, IPredicate> run, final L letter1, final L letter2) {
		Pair<L, L> pair = new Pair<>(letter1,letter2);
		IPredicate pred = ((SleepPredicate<L>) state).getUnderlying();
		
		if (pred instanceof PredicateWithLastThread) {
			pred = ((PredicateWithLastThread) pred).getUnderlying();
		}
		
		if ((pred instanceof MLPredicate)) {
			return true;
		}
		
		//ensures that each pair is checked at most two times (should later on be removed)
		if (!mStatementMap.containsKey(pair)) {
			mStatementMap.put(pair, 1);
		} else if (mStatementMap.get(pair) == 1) {
			mStatementMap.replace(pair, 2);
		}	else {
			return false;
		}

		IPredicate annotation = ((AnnotatedMLPredicate<IPredicate>) pred).getAnnotation();
		if (!mAlreadyChecked.containsKey(pair)) {
			ArrayList<IPredicate> list = new ArrayList<>();
			list.add(annotation);
			mAlreadyChecked.put(pair, list);
		} else {
			List<IPredicate> list = mAlreadyChecked.get(pair);
			for (IPredicate listPred : list) {
				if (listPred.getFormula().equals(annotation.getFormula())) {
					return false;
				}
			}
			list.add(annotation);
		}
		return true;
	}

	@Override
	public boolean decide(final IPredicate condition) {
				
		if (condition == null) {
			return false;
		}
		for (IPredicate con : mAlreadyProofenConditions) {
			if (con.getFormula().equals(condition.getFormula())) {
				return false;
			}
		}
		return true;
	}
	
	@Override
	public void updateCondition(final IPredicate condition) {
		mAlreadyProofenConditions.add(condition);
	}

}
