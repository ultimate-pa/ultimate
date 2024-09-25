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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * A wrapper which represents the conjunction of two given criteria.
 *
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 *            The type of letters.
 */
// TODO Change the name to reflect what it does
public class CriterionConjunction<L> implements IConditionalCommutativityCriterion<L> {
	private final IConditionalCommutativityCriterion<L> mCriterion1;
	private final IConditionalCommutativityCriterion<L> mCriterion2;

	public CriterionConjunction(final IConditionalCommutativityCriterion<L> criterion1,
			final IConditionalCommutativityCriterion<L> criterion2) {
		mCriterion1 = criterion1;
		mCriterion2 = criterion2;
	}

	@Override
	public boolean decide(final IPredicate state, final L letter1, final L letter2) {
		final boolean result1 = mCriterion1.decide(state, letter1, letter2);
		if (!result1) {
			return false;
		}
		return mCriterion2.decide(state, letter1, letter2);
	}

	@Override
	public boolean decide(final IPredicate condition) {
		final boolean result1 = mCriterion1.decide(condition);
		if (!result1) {
			return false;
		}
		return mCriterion2.decide(condition);
	}

	@Override
	public void updateCriterion(final IPredicate state, final L letter1, final L letter2) {
		mCriterion1.updateCriterion(state, letter1, letter2);
		mCriterion2.updateCriterion(state, letter1, letter2);
	}

	@Override
	public void updateAbstraction(final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction) {
		mCriterion1.updateAbstraction(abstraction);
		mCriterion2.updateAbstraction(abstraction);
	}
}
