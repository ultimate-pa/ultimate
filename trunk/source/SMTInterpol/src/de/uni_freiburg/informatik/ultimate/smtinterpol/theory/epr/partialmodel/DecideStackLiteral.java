/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;

/**
 * Represents a literal on the DPLL decide stack of the EprTheory.
 * This special literal consists of a quantified literal together with a
 * data structure restricting the possible groundings of that literal.
 *
 * @author Alexander Nutz
 */
public abstract class DecideStackLiteral extends DecideStackEntry {

	/**
	 * The predicate this decision/propagation affects.
	 */
	protected final EprPredicate mPred;
	/**
	 * The previous state of the literal. This is used for backtracking and to check whether the conflict is older than
	 * this change. It is set on push and used on pop.
	 */
	protected DawgState<ApplicationTerm, EprTheory.TriBool> mOldDawg;
	/**
	 * The new literals propagated or decided.
	 */
	protected DawgState<ApplicationTerm, EprTheory.TriBool> mDawg;

	public DecideStackLiteral(final EprPredicate pred, DawgState<ApplicationTerm, EprTheory.TriBool> dawg) {
		mPred = pred;
		mDawg = dawg;
	}

	@Override
	public EprPredicate getEprPredicate() {
		return mPred;
	}

	public DawgState<ApplicationTerm, EprTheory.TriBool> getOldDawg() {
		return mOldDawg;
	}

	public DawgState<ApplicationTerm, EprTheory.TriBool> getDawg() {
		return mDawg;
	}

	@Override
	public void push(EprDecideStack stack) {
		final BiFunction<EprTheory.TriBool, EprTheory.TriBool, EprTheory.TriBool> combinator = (old, setLit) -> {
			return (setLit != EprTheory.TriBool.UNKNOWN ? setLit : old);
		};
		mOldDawg = mPred.getDawg();
		mPred.setDawg(mPred.getEprTheory().getDawgFactory().createProduct(mOldDawg, getDawg(), combinator));
	}

	@Override
	public void pop(EprDecideStack stack) {
		mPred.setDawg(mOldDawg);
	}
}
