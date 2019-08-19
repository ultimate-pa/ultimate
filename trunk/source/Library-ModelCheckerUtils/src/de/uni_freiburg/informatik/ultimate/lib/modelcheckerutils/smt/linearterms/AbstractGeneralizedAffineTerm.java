/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Common superclass of {@link AffineTerm} and {@link PolynomialTerm}. This class represents an affine term whose kinds
 * of variables are abstract objectsspecified by a type parameter. For a {@link PolynomialTerm} these abstract variables
 * are {@link Monomials} for an {@link AffineTerm} the instance of these abstract variables are already "the variables".
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 * @param <AVAR>
 *            type of the variables
 */
public abstract class AbstractGeneralizedAffineTerm<AVAR extends Term> extends Term implements IPolynomialTerm {

	/**
	 * Map from abstract variables to coeffcients. Coefficient zero is forbidden.
	 */
	protected final Map<AVAR, Rational> mAbstractVariable2Coefficient;
	/**
	 * Affine constant (the coefficient without variable).
	 */
	protected final Rational mConstant;
	/**
	 * Sort of this term. E.g, "Int" or "Real".
	 */
	protected final Sort mSort;

	/**
	 * Auxiliary {@link AbstractGeneralizedAffineTerm} term that represents an error during the translation process,
	 * e.g., if original term was not linear or not polynomial.
	 */
	public AbstractGeneralizedAffineTerm() {
		super(0);
		mAbstractVariable2Coefficient = null;
		mConstant = null;
		mSort = null;
	}

	/**
	 * Default constructor for non-error terms.
	 */
	protected AbstractGeneralizedAffineTerm(final Sort s, final Rational constant,
			final Map<AVAR, Rational> variables2coeffcient) {
		super(0);
		mSort = s;
		mConstant = constant;
		mAbstractVariable2Coefficient = variables2coeffcient;
	}

	/**
	 * True if this represents not an legal term of its kind but an error during the translation process, e.g., if
	 * original term was not linear or not polynomial.
	 */
	@Override
	public boolean isErrorTerm() {
		if (mAbstractVariable2Coefficient == null) {
			assert mConstant == null;
			assert mSort == null;
			return true;
		} else {
			assert mConstant != null;
			assert mSort != null;
			return false;
		}
	}

	/*
	 * check documentation of subclasses
	 */
	public abstract boolean isVariable(Term var);

	/**
	 * @return whether this {@link AbstractGeneralizedAffineTerm} is just a constant
	 */
	@Override
	public boolean isConstant() {
		return mAbstractVariable2Coefficient.isEmpty();
	}

	/**
	 * @return whether this {@link AbstractGeneralizedAffineTerm} is zero
	 */
	@Override
	public boolean isZero() {
		return mConstant.equals(Rational.ZERO) && mAbstractVariable2Coefficient.isEmpty();
	}

	/**
	 * Check whether every coefficient and every constant is of an integral value. Return true if thats the case.
	 */
	@Override
	public boolean isIntegral() {
		if (!getConstant().isIntegral()) {
			return false;
		}
		for (final Rational coefficient : getAbstractVariable2Coefficient().values()) {
			if (!coefficient.isIntegral()) {
				return false;
			}
		}
		return true;
	}

	/**
	 * @return the constant summand of this {@link AbstractGeneralizedAffineTerm}
	 */
	@Override
	public Rational getConstant() {
		return mConstant;
	}

	/**
	 * Check if term is of a type that may be a variable of an {@link AbstractGeneralizedAffineTerm}.
	 */
	public void checkIfTermIsLegalVariable(final Term term) {
		if (term instanceof TermVariable || term instanceof ApplicationTerm) {
			// term is ok
		} else {
			throw new IllegalArgumentException("Variable of AffineTerm has to be TermVariable or ApplicationTerm");
		}
	}

	@Override
	public String toString() {
		if (isErrorTerm()) {
			return "auxilliaryErrorTerm";
		}
		final StringBuilder sb = new StringBuilder();
		for (final Map.Entry<AVAR, Rational> entry : mAbstractVariable2Coefficient.entrySet()) {
			sb.append(entry.getValue().isNegative() ? " - " : " + ");
			sb.append(entry.getValue().abs() + "*" + entry.getKey());
		}
		if (!mConstant.equals(Rational.ZERO) || sb.length() == 0) {
			if (mConstant.isNegative() || sb.length() > 0) {
				sb.append(mConstant.isNegative() ? " - " : " + ");
			}
			sb.append(mConstant.abs());
		}
		String result = sb.toString();
		if (result.charAt(0) == ' ') {
			result = result.substring(1); // Drop first space
		}

		return result;
	}

	/**
	 * @return an SMT {@link Term} that represents an abstract variable that occurs in the map of this object
	 */
	protected abstract Term abstractVariableToTerm(Script script, AVAR abstractVariable);

	/**
	 * Transforms this {@link AbstractGeneralizedAffineTerm} into a Term that is supported by the solver.
	 *
	 * @param script
	 *            Script for that this term is constructed.
	 */
	@Override
	public Term toTerm(final Script script) {
		Term[] summands;
		if (mConstant.equals(Rational.ZERO)) {
			summands = new Term[mAbstractVariable2Coefficient.size()];
		} else {
			summands = new Term[mAbstractVariable2Coefficient.size() + 1];
		}
		int i = 0;
		for (final Map.Entry<AVAR, Rational> entry : mAbstractVariable2Coefficient.entrySet()) {
			assert !entry.getValue().equals(Rational.ZERO) : "zero is no legal coefficient in AffineTerm";
			if (entry.getValue().equals(Rational.ONE)) {
				summands[i] = abstractVariableToTerm(script, entry.getKey());
			} else {
				final Term coeff = SmtUtils.rational2Term(script, entry.getValue(), mSort);
				summands[i] = SmtUtils.mul(script, mSort, coeff, abstractVariableToTerm(script, entry.getKey()));
			}
			++i;
		}
		if (!mConstant.equals(Rational.ZERO)) {
			assert mConstant.isIntegral() || SmtSortUtils.isRealSort(mSort);
			summands[i] = SmtUtils.rational2Term(script, mConstant, mSort);
		}
		final Term result = SmtUtils.sum(script, mSort, summands);
		return result;
	}

	@Override
	public Sort getSort() {
		return mSort;
	}

	Map<AVAR, Rational> getAbstractVariable2Coefficient() {
		return Collections.unmodifiableMap(mAbstractVariable2Coefficient);
	}

	@Override
	public void toStringHelper(final ArrayDeque<Object> mTodo) {
		throw new UnsupportedOperationException("This is an auxilliary Term and not supported by the solver");
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + (mConstant == null ? 0 : mConstant.hashCode());
		result = prime * result + (mSort == null ? 0 : mSort.hashCode());
		result = prime * result
				+ (mAbstractVariable2Coefficient == null ? 0 : mAbstractVariable2Coefficient.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final AbstractGeneralizedAffineTerm other = (AbstractGeneralizedAffineTerm) obj;
		if (mConstant == null) {
			if (other.mConstant != null) {
				return false;
			}
		} else if (!mConstant.equals(other.mConstant)) {
			return false;
		}
		if (mSort == null) {
			if (other.mSort != null) {
				return false;
			}
		} else if (!mSort.equals(other.mSort)) {
			return false;
		}
		if (mAbstractVariable2Coefficient == null) {
			if (other.mAbstractVariable2Coefficient != null) {
				return false;
			}
		} else if (!mAbstractVariable2Coefficient.equals(other.mAbstractVariable2Coefficient)) {
			return false;
		}
		return true;
	}

}