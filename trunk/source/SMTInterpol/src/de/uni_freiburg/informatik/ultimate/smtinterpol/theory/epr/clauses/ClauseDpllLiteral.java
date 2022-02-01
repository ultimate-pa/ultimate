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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class ClauseDpllLiteral extends ClauseLiteral {
	Literal mLastState = null; // TODO isDirty is broken

	public ClauseDpllLiteral(final boolean polarity, final DPLLAtom atom, final EprClause clause, final EprTheory eprTheory) {
		super(polarity, atom, clause, eprTheory);
		assert !(atom instanceof EprPredicateAtom) : "use different ClauseLiteral";
		assert !(atom instanceof EprQuantifiedEqualityAtom) : "use different ClauseLiteral";
	}

	protected boolean isDirty() {
		return mLastState != mAtom.getDecideStatus();
	}

	/**
	 *
	 * @param decideStackBorder this parameter is irrelevant for dpll literals because they lie
	 *   "below" the epr decide stack anyway.
	 */
	@Override
	protected DawgState<ApplicationTerm, EprTheory.TriBool> getDawg() {
		mLastState = mAtom.getDecideStatus();
		if (mLastState == null) {
			// undecided
			return mDawgFactory.createConstantDawg(mEprClause.getVariables(), EprTheory.TriBool.UNKNOWN);
		} else if ((mLastState == mAtom) == mPolarity) {
			// decided with same polarity
			return mDawgFactory.createConstantDawg(mEprClause.getVariables(), EprTheory.TriBool.TRUE);
		} else {
			// decided with different polarity
			return mDawgFactory.createConstantDawg(mEprClause.getVariables(), EprTheory.TriBool.FALSE);
		}
	}
}
