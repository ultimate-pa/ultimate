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
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitesimalNumber;

/**
 * This class is used to gather the information from a literal term which is relevant for the interpolator.
 *
 * @author Tanja Schindler, Jochen Hoenicke
 */
public class InterpolatorAtomInfo {
	/**
	 * The type of this literal, true if it represents a CC equality
	 */
	private boolean mIsCCEquality;

	/**
	 * The type of this literal, true if it represents a LA equality
	 */
	private boolean mIsLAEquality;

	/**
	 * The type of this literal, true if it represents a bound constraint
	 */
	private boolean mIsBoundConstraint;

	/**
	 * If this literal is a CC equality, then this contains the ApplicationTerm (= lhs rhs)
	 */
	private ApplicationTerm mCCEquality;

	/**
	 * The affine term of this LA literal (with epsilon set if strict).
	 */
	private InterpolatorAffineTerm mAffineTerm;

	private boolean mIsInt;

	public InterpolatorAtomInfo(final Term atom) {
		mIsCCEquality = false;
		mIsLAEquality = false;
		mIsBoundConstraint = false;
		mAffineTerm = null;
		mIsInt = false;
		computeAtomInfo(atom);
	}

	/**
	 * Collect information about this literal which is needed during interpolation
	 */
	public void computeAtomInfo(final Term term) {
		final Term atom = term;
		String annot = null;
		// Store the underlying atom
		assert !(atom instanceof ApplicationTerm && ((ApplicationTerm) atom).getFunction().getName().equals("not"));
		// Annotations can be inside negations
		if (atom instanceof AnnotatedTerm) {
			final AnnotatedTerm quotedTerm = (AnnotatedTerm) atom;
			assert quotedTerm.getAnnotations().length == 1;
			annot = quotedTerm.getAnnotations()[0].getKey();
			final Term unquoted = quotedTerm.getSubterm();
			switch (annot) {
			case ":quotedCC":
				mIsCCEquality = true;
				mCCEquality = (ApplicationTerm) unquoted;
				assert mCCEquality.getFunction().getName() == "=";
				break;
			case ":quotedLA":
				computeLAInformation((ApplicationTerm) unquoted);
				break;
			default:
				assert annot == ":quoted";
				// We do nothing for auxiliary literal.
			}
		}
	}

	/**
	 * For an LA equality or bound constraint, get the linear variable.
	 */
	private void computeLAInformation(final ApplicationTerm laAtom) {
		boolean isStrict = false;
		switch (laAtom.getFunction().getName()) {
		case "<=":
			mIsBoundConstraint = true;
			break;
		case "<":
			mIsBoundConstraint = true;
			isStrict = true;
			break;
		case "=":
			mIsLAEquality = true;
			break;
		default:
			throw new AssertionError("Wrong :quotedLA term.");
		}
		final Term[] params = laAtom.getParameters();
		assert params[1] == Rational.ZERO.toTerm(params[1].getSort());
		mIsInt = params[1].getSort().getName().equals("Int");
		mAffineTerm = new InterpolatorAffineTerm(new SMTAffineTerm(params[0]));
		assert mAffineTerm.getConstant().mEps == 0;
		if (isStrict) {
			// < x 0 is the same as <= x+eps 0
			mAffineTerm.add(getEpsilon());
		}
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

	/**
	 * Get the equality term for a CC equality literal.
	 *
	 * @return the equality term.
	 */
	public ApplicationTerm getEquality() {
		return mCCEquality;
	}

	/**
	 * Get the affine term of the underlying atom. This is the left hand side of the LA literal {@code (<= lhs 0)} and
	 * contains epsilon for strict bounds. Note that this is the affine term for the atom. For a negated atom you still
	 * need to subtract getEpsilon() to get the constraint.
	 *
	 * @return the affine term.
	 */
	public InterpolatorAffineTerm getAffineTerm() {
		return mAffineTerm;
	}

	/**
	 * Get the epsilon for this bound constraint. This is 1 for integer constraints, and eps for rational constraints.
	 * It can be used to adapt for inverse bounds.
	 */
	public InfinitesimalNumber getEpsilon() {
		return isInt() ? InfinitesimalNumber.ONE : InfinitesimalNumber.EPSILON;
	}

	public boolean isInt() {
		return mIsInt;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("AtomInfo(");
		if (isCCEquality()) {
			sb.append("CC:").append(getEquality());
		} else if (isLAEquality()) {
			sb.append("LA:").append(getAffineTerm()).append(" == 0");
			if (!isInt()) {
				sb.append(".0");
			}
		} else if (isBoundConstraint()) {
			sb.append("LA:").append(getAffineTerm()).append(" <= 0");
			if (!isInt()) {
				sb.append(".0");
			}
		} else {
			sb.append("NOINFO");
		}
		sb.append(")");
		return sb.toString();
	}
}
