/*
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ILiteral;

/**
 * Represents a quantified literal.
 * <p>
 * It stores the term, as well as the underlying atom and the negated literal. It also stores whether the literal lies
 * in the almost uninterpreted fragment, i.e., it is essentially uninterpreted or arithmetical, and whether it can be
 * used for DER. A quantified literal appearing in a QuantClause also knows its clause.
 *
 * @author Tanja Schindler
 *
 */
public abstract class QuantLiteral implements ILiteral {
	/**
	 * The term that this literal represents.
	 */
	private final Term mTerm;
	/**
	 * The clause this literal occurs in.
	 */
	protected QuantClause mClause;
	/**
	 * Flag to mark if the QuantLiteral is essentially uninterpreted (and hence almost uninterpreted). The default value
	 * is false.
	 */
	protected boolean mIsEssentiallyUninterpreted;
	/**
	 * Flag to mark if the QuantLiteral is arithmetical (and hence almost uninterpreted). The default value is false.
	 */
	protected boolean mIsArithmetical;
	/**
	 * Flag to mark if the QuantLiteral can be used for DER.
	 */
	protected boolean mIsDERUsable;
	/**
	 * The underlying atom.
	 */
	protected QuantLiteral mAtom;
	/**
	 * The negated literal. Equal to mAtom for negated literals.
	 */
	protected QuantLiteral mNegated;

	/**
	 * Create a new QuantLiteral from a term. This should only be called after checking that the literal contains
	 * quantified variables and is supported.
	 *
	 * @param term
	 *            the term corresponding to the literal.
	 */
	QuantLiteral(final Term term) {
		mTerm = term;
		mAtom = this;
		// Default values.
		mIsEssentiallyUninterpreted = mIsArithmetical = false;
		mIsDERUsable = false;
	}

	@Override
	public QuantLiteral negate() {
		return mNegated;
	}

	public Term getTerm() {
		return mTerm;
	}

	public QuantClause getClause() {
		return mClause;
	}

	@Override
	public QuantLiteral getAtom() {
		return mAtom;
	}

	public boolean isNegated() {
		return mAtom == mNegated;
	}

	@Override
	public boolean isGround() {
		return false;
	}

	public boolean isAlmostUninterpreted() {
		return isEssentiallyUninterpreted() || isArithmetical();
	}

	public boolean isEssentiallyUninterpreted() {
		return mIsEssentiallyUninterpreted;
	}

	public boolean isArithmetical() {
		return mIsArithmetical;
	}

	@Override
	public Term getSMTFormula(final Theory theory) {
		return mTerm;
	}

	/**
	 * Represents a negated QuantLiteral. Here, the atom and the negated literal are equal.
	 */
	static class NegQuantLiteral extends QuantLiteral {

		/**
		 * Create a new NegatedLiteral.
		 *
		 * @param lit
		 *            the atom which we want to create a negated literal for.
		 */
		NegQuantLiteral(final QuantLiteral lit) {
			super(lit.getTerm().getTheory().not(lit.getTerm()));
			mAtom = lit;
			mNegated = lit;
		}

		@Override
		public Term getSMTFormula(final Theory theory) {
			return theory.not(super.getAtom().getSMTFormula(theory));
		}
	}

	@Override
	public String toString() {
		return mTerm.toString();
	}
}
