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

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * A wrapper which represents the conjunction of two given criteria.
 *
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 *            The type of letters.
 */
public class WrapperCriterion<L> implements IConditionalCommutativityCriterion<L> {
	
	private IConditionalCommutativityCriterion<L> mCriterion1;
	private IConditionalCommutativityCriterion<L> mCriterion2;

	/**
	 * Constructor.
	 *
	 * @author Marcel Ebbinghaus
	 * 
	 * @param criterion1
	 *     first criterion
	 * @param criterion2
	 *     second criterion
	 */
	WrapperCriterion(IConditionalCommutativityCriterion<L> criterion1,
			IConditionalCommutativityCriterion<L> criterion2) {
		mCriterion1 = criterion1;
		mCriterion2 = criterion2;
	}

	@Override
	public boolean decide(IPredicate state, IRun<L, IPredicate> run, L letter1, L letter2) {
		boolean result1 = mCriterion1.decide(state, run, letter1, letter2);
		boolean result2 = mCriterion2.decide(state, run, letter1, letter2);
		return (result1 && result2);
	}

	@Override
	public boolean decide(IPredicate condition) {
		boolean result1 = mCriterion1.decide(condition);
		boolean result2 = mCriterion2.decide(condition);
		return (result1 && result2);
	}

	@Override
	public void updateCriterion(IPredicate state, L letter1, L letter2) {
		mCriterion1.updateCriterion(state, letter1, letter2);
		mCriterion2.updateCriterion(state, letter1, letter2);
	}

	@Override
	public void updateCondition(IPredicate condition) {
		mCriterion1.updateCondition(condition);
		mCriterion2.updateCondition(condition);
	}

}
