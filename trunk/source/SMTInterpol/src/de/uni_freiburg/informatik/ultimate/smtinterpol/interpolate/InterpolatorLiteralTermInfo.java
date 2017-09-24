/*
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitNumber;

/**
 * This class is used to gather the information from a literal term which is relevant for the interpolator.
 *
 * @author Tanja Schindler
 */
public class InterpolatorLiteralTermInfo {
	/**
	 * The underlying atom of this literal
	 */
	private Term mAtom;
	private boolean mIsNegated;

	/**
	 * The type of this literal, true if it represents a CC equality
	 */
	private boolean mIsCCEquality;

	/**
	 * The type of this literal, true if it represents a LA equality
	 */
	private boolean mIsLAEquality;

	/**
	 * The type of this literal, true if it represents a Bound constraint
	 */
	private boolean mIsBoundConstraint;

	/**
	 * The linear variable of this LA literal
	 */
	private InterpolatorAffineTerm mLinVar;

	/**
	 * The bound of this bound constraint literal
	 */
	private Rational mBound;

	/**
	 * Epsilon is 1 for integer constraints, eps for rational constraints
	 */
	private InfinitNumber mEpsilon;

	private boolean mIsInt;

	public InterpolatorLiteralTermInfo() {
		mAtom = null;
		mIsNegated = false;
		mIsCCEquality = false;
		mIsLAEquality = false;
		mIsBoundConstraint = false;
		mLinVar = null;
		mBound = null;
		mEpsilon = null;
		mIsInt = false;
	}

	/**
	 * Collect information about this literal which is needed during interpolation
	 */
	public void computeLiteralTermInfo(final Term term) {
		Term literal = term;
		if (term instanceof AnnotatedTerm) {
			literal = ((AnnotatedTerm) term).getSubterm();
		}
		mAtom = computeAtom(literal);
		if (literal instanceof ApplicationTerm && ((ApplicationTerm) literal).getFunction().getName().equals("not")) {
			mIsNegated = true;
		}
		mIsCCEquality = isCCEquality(mAtom);
		mIsLAEquality = isLAEquality(mAtom);
		mIsBoundConstraint = isBoundConstraint(mAtom);

		if (mIsLAEquality || mIsBoundConstraint) {
			final InterpolatorAffineTerm lv = computeLinVarAndBound(mAtom);
			assert lv.getConstant().mEps == 0;
			mBound = lv.getConstant().negate().mA;
			mLinVar = lv.add(mBound);
			mIsInt = mLinVar.isInt();
			mEpsilon = computeEpsilon(mAtom);
		}
	}

	/**
	 * Get the underlying atomic term for an annotated or negated term
	 */
	private Term computeAtom(final Term term) {
		Term inner = term;
		if (isNegated(inner)) {
			inner = ((ApplicationTerm) inner).getParameters()[0];
		}
		if (inner instanceof AnnotatedTerm) {
			inner = ((AnnotatedTerm) inner).getSubterm();
		}
		return inner;
	}

	/**
	 * Check if this atom is a CC equality.
	 */
	private boolean isCCEquality(final Term atom) {
		if (atom instanceof ApplicationTerm && ((ApplicationTerm) atom).getFunction().isIntern()) {
			if (((ApplicationTerm) atom).getFunction().getName().equals("=")) {
				return !isLAEquality(atom);
			}
		}
		return false;
	}

	/**
	 * Check if this atom is a LA equality. Note that some CC equalities look like LA equalities, but in those cases,
	 * they are treated the same way.
	 */
	boolean isLAEquality(final Term atom) {
		if (atom instanceof ApplicationTerm) {
			if (((ApplicationTerm) atom).getFunction().getName().equals("=")) {
				final Term secondParam = ((ApplicationTerm) atom).getParameters()[1];
				if (secondParam instanceof ConstantTerm) {
					return SMTAffineTerm.create(secondParam).getConstant().equals(Rational.ZERO);
				}
			}
		}
		return false;
	}

	/**
	 * Check if this atom is a bound constraint
	 */
	private Boolean isBoundConstraint(final Term atom) {
		if (!(atom instanceof ApplicationTerm)) {
			return false;
		}
		final String func = ((ApplicationTerm) atom).getFunction().getName();
		return func.equals("<") || func.equals("<=");
	}

	/**
	 * For an LA equality or bound constraint, get the linear variable.
	 */
	private InterpolatorAffineTerm computeLinVarAndBound(final Term laTerm) {
		final Term laAtom = computeAtom(laTerm);
		final Term[] params = ((ApplicationTerm) laAtom).getParameters();
		final Term varTerm = params[0];

		assert params[1] instanceof ConstantTerm;
		assert SMTAffineTerm.create(params[1]).getConstant().equals(Rational.ZERO);
		return Interpolator.termToAffine(varTerm);
	}

	/**
	 * Get the epsilon for this bound constraint. This is 1 for integer constraints, and eps for rational constraints.
	 */
	private InfinitNumber computeEpsilon(final Term term) {
		return mLinVar.isInt() ? InfinitNumber.ONE : InfinitNumber.EPSILON;
	}

	/**
	 * Check if a term is negated
	 */
	private boolean isNegated(final Term term) {
		if (term instanceof ApplicationTerm) {
			return ((ApplicationTerm) term).getFunction().getName().equals("not");
		} else {
			return false;
		}
	}

	public Term getAtom() {
		return mAtom;
	}

	public boolean isNegated() {
		return mIsNegated;
	}

	public boolean isCCEquality() {
		return mIsCCEquality;
	}

	public boolean isLAEquality() {
		return mIsLAEquality;
	}

	public boolean isBoundConstraint() {
		return mIsBoundConstraint;
	}

	public InterpolatorAffineTerm getLinVar() {
		return mLinVar;
	}

	public Rational getBound() {
		return mBound;
	}

	public InfinitNumber getEpsilon() {
		return mEpsilon;
	}

	public boolean isInt() {
		return mIsInt;
	}
}
