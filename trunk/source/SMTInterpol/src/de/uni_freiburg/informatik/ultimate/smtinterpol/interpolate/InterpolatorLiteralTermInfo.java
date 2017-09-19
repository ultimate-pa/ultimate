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

import java.util.Arrays;

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
	public void computeLiteralTermInfo(Term term) {
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
			mLinVar = computeLinVar(mAtom);
			mIsInt = mLinVar.isInt();
			mBound = computeBound(mAtom);
			mEpsilon = computeEpsilon(mAtom);
		}
	}
	
	/**
	 * Get the underlying atomic term for an annotated or negated term
	 */
	private Term computeAtom(Term term) {
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
	private boolean isCCEquality(Term atom) {
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
	boolean isLAEquality(Term atom) {
		if ((atom instanceof ApplicationTerm)) {
			if (((ApplicationTerm) atom).getFunction().getName().equals("=")) {
				final Term secondParam = ((ApplicationTerm) atom).getParameters()[1];
				if ((secondParam instanceof ConstantTerm)) {
					return SMTAffineTerm.create(secondParam).getConstant().equals(Rational.ZERO);
				}
			}
		}
		return false;
	}
	
	/**
	 * Check if this atom is a bound constraint
	 */
	private Boolean isBoundConstraint(Term atom) {
		if (!(atom instanceof ApplicationTerm)) {
			return false;
		}
		final String func = ((ApplicationTerm) atom).getFunction().getName();
		return (func.equals("<") || func.equals("<="));
	}
	
	/**
	 * For an LA equality or bound constraint, get the linear variable.
	 */
	private InterpolatorAffineTerm computeLinVar(Term laTerm) {
		final Term laAtom = computeAtom(laTerm);
		Term varTerm = ((ApplicationTerm) laAtom).getParameters()[0];
		if (varTerm instanceof ApplicationTerm && ((ApplicationTerm) varTerm).getFunction().isIntern()) {
			String function = ((ApplicationTerm) varTerm).getFunction().getName();
			if (function.equals("+")) {
				int length = ((ApplicationTerm) varTerm).getParameters().length;
				if (!computeBound(laAtom).equals(Rational.ZERO)) {
					length -= 1;
				}
				final Term[] varParams = Arrays.copyOf(((ApplicationTerm) varTerm).getParameters(), length);
				if (length == 1) {
					varTerm = varParams[0];
				} else {
					varTerm = varTerm.getTheory().term("+", varParams);
				}
			}
		}
		InterpolatorAffineTerm linVar = Interpolator.termToAffine(varTerm);
		return linVar;
	}
	
	/**
	 * Get the bound of a bound constraint. This can also be used to get the constant for LA equalities.
	 */
	private Rational computeBound(Term laTerm) {
		final ApplicationTerm varTerm = (ApplicationTerm) ((ApplicationTerm) laTerm).getParameters()[0];
		final Object[] params = varTerm.getParameters();
		ConstantTerm boundTerm = null;
		boolean isNeg = false;
		if (params.length == 0) {
			return Rational.ZERO;
		} else if (params[params.length - 1] instanceof ConstantTerm) {
			boundTerm = (ConstantTerm) params[params.length - 1];
		} else if (params[params.length - 1] instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = ((ApplicationTerm) params[params.length - 1]);
			if (appTerm.getFunction().getName().equals("-")) {
				if (appTerm.getParameters()[0] instanceof ConstantTerm) {
					boundTerm = (ConstantTerm) appTerm.getParameters()[0];
					isNeg = true;
				}
			}
		}
		if (boundTerm == null) {
			return Rational.ZERO;
		}
		Rational bound = SMTAffineTerm.create(boundTerm).getConstant();
		if (!isNeg) {
			bound = bound.negate();
		}
		return bound;
	}
	
	/**
	 * Get the epsilon for this bound constraint. This is 1 for integer constraints, and eps for rational constraints.
	 */
	private InfinitNumber computeEpsilon(Term term) {
		return mLinVar.isInt() ? InfinitNumber.ONE : InfinitNumber.EPSILON;
	}
	
	/**
	 * Check if a term is negated
	 */
	private boolean isNegated(Term term) {
		if ((term instanceof ApplicationTerm)) {
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
