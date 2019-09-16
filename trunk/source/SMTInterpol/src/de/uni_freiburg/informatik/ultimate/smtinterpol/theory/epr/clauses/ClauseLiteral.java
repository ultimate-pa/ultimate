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
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;

/**
 * Represents a literal that occurs in an EprClause.
 * This may be a ground literal or a quantified literal.
 *
 * In contrast to the Literal class DPLLEngine uses, a
 * ClauseLiteral has a decide state that also depends on the
 * EprStateManagers decide stack.
 *
 * A ClauseLiteral always only occurs in one clause.
 *
 * @author Alexander Nutz
 */
public abstract class ClauseLiteral {


	protected final Literal mEngineLiteral;
	protected final DPLLAtom mAtom;
	protected final boolean mPolarity;
	protected final EprTheory mEprTheory;

	/**
	 * The clause that this ClauseLiteral is part of
	 */
	protected EprClause mEprClause;
	protected final DawgFactory<ApplicationTerm, TermVariable> mDawgFactory;

	public ClauseLiteral(final boolean polarity, final DPLLAtom atom, final EprClause clause, final EprTheory eprTheory) {
		mAtom = atom;
		mEngineLiteral = polarity ? atom : atom.negate();
		mPolarity = polarity;
		mEprClause = clause;
		mEprTheory = eprTheory;
		mDawgFactory = eprTheory.getDawgFactory();
	}


	public boolean getPolarity() {
		return mPolarity;
	}

	public Literal getLiteral() {
		return mEngineLiteral;
	}

	protected abstract boolean isDirty();
	protected abstract DawgState<ApplicationTerm, EprTheory.TriBool> getDawg();

	/**
	 * For ground clause literals this has the usual meanings wrt. the current decide state:
	 *  - fulfilled: set to true
	 *  - fulfillable: undecided
	 *  - refuted: set to false
	 *
	 *  For quantified clause literals fulfilled/refuted means that it is true/false on all points.
	 *  Fulfillable means everything in between..
	 */
	enum ClauseLiteralState {
		Fulfilled, Fulfillable, Refuted;
	}

	public EprClause getClause() {
		return mEprClause;
	}

	@Override
	public String toString() {
		final String negate = mPolarity ? "" : "~";
		return negate + mAtom.toString();
	}
}
