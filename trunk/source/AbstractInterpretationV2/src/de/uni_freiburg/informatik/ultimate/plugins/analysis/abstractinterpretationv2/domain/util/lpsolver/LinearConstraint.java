/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.lpsolver;

import java.util.ArrayList;
import java.util.List;

/**
 * Class for a linear constraint of the form
 * <p>
 * lower &leq; a1*x1 + a2 * x2 + ... + an * xn &leq; upper,
 * </p>
 * where lower, upper are the bounds for the constraint, a1,...,an are coefficients, and x1,...,xn are variables.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 * @param <N>
 *            Any number type. This is the backing field type for all numerals in the linear expression.
 */
public class LinearConstraint<N extends Number> {

	/**
	 * The lower bound. If it is not set, the semantics of the lower bound is -infinity.
	 */
	private N mLower;

	/**
	 * The upper bound. If it is not set, the semantics of the upper bound is infinity.
	 */
	private N mUpper;

	/**
	 * Is <code>true</code> if and only if the {@link #setLower(Number)} function has been called, and therefore a lower
	 * bound has been set.
	 */
	private boolean mHasLower;

	/**
	 * Is <code>true</code> if and only if the {@link #setUpper(Number)} function has been called, and therefore an
	 * upper bound has been set.
	 */
	private boolean mHasUpper;

	/**
	 * The name for the {@link LinearConstraint}.
	 */
	private final String mName;

	/**
	 * Stores each variable name.
	 */
	private final List<String> mVariables;

	/**
	 * Stores for each variable its coefficient.
	 */
	private final List<N> mCoefficients;

	/**
	 * The default constructor which creates a new {@link LinearConstraint} instance with a name.
	 * 
	 * @param name
	 *            The name of the {@link LinearConstraint}.
	 */
	public LinearConstraint(String name) {
		mHasLower = false;
		mHasUpper = false;
		mVariables = new ArrayList<>();
		mCoefficients = new ArrayList<>();
		mName = name;
	}

	/**
	 * Sets the lower bound of the {@link LinearConstraint} to some value.
	 * 
	 * @param lower
	 *            The value to set the lower bound to.
	 */
	public void setLower(N lower) {
		mLower = lower;
		mHasLower = true;
	}

	/**
	 * @return The value for the lower bound if set, <code>null</code> otherwise.
	 */
	public N getLower() {
		if (mHasLower) {
			return mLower;
		} else {
			return null;
		}
	}

	/**
	 * Sets the upper bound of the {@link LinearConstraint} to some value.
	 * 
	 * @param upper
	 *            The value to set the upper bound to.
	 */
	public void setUpper(N upper) {
		mUpper = upper;
		mHasUpper = true;
	}

	/**
	 * @return The value for the upper bound, if set, <code>null</code> otherwise.
	 */
	public N getUpper() {
		if (mHasUpper) {
			return mUpper;
		} else {
			return null;
		}
	}

	/**
	 * @return <code>true</code> if and only if the lower bound is set, i.e. the {@link #setLower(Number)} function was
	 *         called before.
	 */
	public boolean isLowerBounded() {
		return mHasLower;
	}

	/**
	 * @return <code>true</code> if and only if the upper bound is set, i.e. the {@link #setUpper(Number)} function was
	 *         called before.
	 */
	public boolean isUpperBounded() {
		return mHasUpper;
	}

	/**
	 * Adds a coefficient to a variable of the {@link LinearConstraint}, identified by its index.
	 * 
	 * @param index
	 *            The index of the variable.
	 * @param coefficient
	 *            The coefficient to add.
	 */
	public void addCoefficient(String varName, N coefficient) {
		assert varName != null;
		assert coefficient != null;
		assert mVariables.size() == mCoefficients.size();
		mVariables.add(varName);
		mCoefficients.add(coefficient);
	}

	/**
	 * @return A list of Strings with all variable names.
	 */
	public List<String> getVariableNames() {
		return mVariables;
	}

	/**
	 * For a given variable name, returns the coefficient of that variable.
	 * 
	 * @param variableName
	 *            The variable name to get the coefficient for.
	 * @return The coefficient of the variable.
	 */
	public N getCoefficient(String variableName) {
		assert variableName != null;

		final Integer index = mVariables.indexOf(variableName);
		assert index != null;

		return mCoefficients.get(index);
	}

	public String toLogString() {
		final StringBuilder sb = new StringBuilder();

		sb.append(mName).append(": ");

		if (isLowerBounded()) {
			sb.append(mLower).append(" <= ");
		}

		for (int i = 0; i < mVariables.size(); i++) {
			if (i > 0) {
				sb.append(" + ");
			}
			final String varName = mVariables.get(i);
			if (varName == null) {
				continue;
			}
			final N coeff = mCoefficients.get(i);

			sb.append(coeff).append("*").append(varName);
		}

		if (isUpperBounded()) {
			sb.append(" <= ").append(mUpper);
		}

		return sb.toString();
	}

	public String getName() {
		return mName;
	}

	public int getVariableCount() {
		return mVariables.size();
	}

}
