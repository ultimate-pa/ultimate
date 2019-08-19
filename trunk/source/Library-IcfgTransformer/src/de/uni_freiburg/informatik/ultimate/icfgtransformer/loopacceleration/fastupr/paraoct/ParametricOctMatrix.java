/*
 * Copyright (C) 2017 Jill Enke (enkei@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctMatrix;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctValue;

/**
 * Parametric Octagons Parametric octagons can (compared to regular octagons) have variables on the right side, so they
 * have the form: +-x+-y <= a*k+b, +-2x <= a*k+b, +-y <= a*k+b
 *
 * @author Jill Enke (enkei@informatik.uni-freiburg.de)
 *
 */
public class ParametricOctMatrix {

	private ILogger mLogger;
	private OctMatrix mMatrix;
	private OctMatrix mSummands;
	private TermVariable mParametricVar;
	private boolean mParametric;
	private int mSize;
	private int mNextMaxValue;
	private final Map<TermVariable, Integer> mVariableMapping;
	private final Map<Integer, TermVariable> mReverseMapping;

	// ********************************
	// CONSTRUCTORS
	// ********************************

	public ParametricOctMatrix() {
		this(0);
	}

	public ParametricOctMatrix(final int size) {
		mNextMaxValue = 0;
		mVariableMapping = new HashMap<>();
		mReverseMapping = new HashMap<>();
		mSize = size;
		mParametric = false;
		mMatrix = new OctMatrix(size);
		mMatrix.fill(OctValue.INFINITY);
	}

	public ParametricOctMatrix(final OctMatrix matrix, final Map<TermVariable, Integer> mapping) {
		mNextMaxValue = 0;
		mSize = matrix.getSize();
		mMatrix = matrix.copy();
		mVariableMapping = mapping;
		mReverseMapping = new HashMap<>();
		reverseMapping();
		mParametric = false;
	}

	public ParametricOctMatrix(final OctMatrix matrix, final Map<TermVariable, Integer> mapping,
			final TermVariable var) {
		mNextMaxValue = 0;
		mSize = matrix.getSize();
		mMatrix = matrix.copy();
		mVariableMapping = mapping;
		mReverseMapping = new HashMap<>();
		reverseMapping();
		mParametric = true;
		mSummands = new OctMatrix(matrix.variables());
		mSummands.fill(OctValue.INFINITY);
		mParametricVar = var;
	}

	public ParametricOctMatrix(final OctMatrix matrix, final OctMatrix summands,
			final Map<TermVariable, Integer> mapping, final TermVariable var) {
		this(matrix, mapping, var);
		mSummands = summands.copy();
		mParametric = true;
	}

	/**
	 * TODO: REMOVE LATER
	 *
	 * @param logger
	 */
	public void setLogger(final ILogger logger) {
		mLogger = logger;
	}

	/**
	 * Calculates the sum of two ParametricOctMatrices
	 *
	 * @param summand
	 *            the second summand.
	 * @return
	 */

	// ********************************
	// CALCULATION FUNCTIONS
	// ********************************

	/**
	 * Adds another matrix..
	 *
	 * @param summand
	 *            the Matrix to be added.
	 * @return the sum as a new ParametricOctMatrix.
	 */
	public ParametricOctMatrix add(final ParametricOctMatrix summand) {
		if (!mappingMatch(summand)) {
			throw new IllegalArgumentException("Matrices need equal Mapping");
		}
		if (isParametric() || summand.isParametric()) {
			return parametricAdd(summand);
		}
		return new ParametricOctMatrix(mMatrix.add(summand.getMatrix()), mVariableMapping);
	}

	// TODO: addMatrices() for other
	private ParametricOctMatrix parametricAdd(final ParametricOctMatrix summand) {
		final ParametricOctMatrix result;
		if (mParametric && !summand.isParametric()) {
			result = new ParametricOctMatrix(getMatrix(), addMatrices(getSummands(), summand.getMatrix(), true),
					getMapping(), getParametricVar());
			debug("Set Summands of result");
		} else if (!mParametric && summand.isParametric()) {
			debug("Matrix is not parametric, summand is.");
			result = summand.copy();
			result.mSummands = mMatrix.add(summand.getSummands());
		} else {
			debug("Both are parametric.");
			if (!mParametricVar.equals(summand.getParametricVar())) {
				throw new IllegalArgumentException("Matrices need the same parametric variable");
			} else {
				result = copy();
				result.mSummands = mSummands.add(summand.getSummands());
				result.mMatrix = mMatrix.add(summand.getMatrix());
			}
		}
		return result;
	}

	/**
	 * Subtracts one (non-parametric) Matrix from another.
	 *
	 * @param matrix
	 *            the subtrahend.
	 * @return a new ParametricOctMatrix of the difference.
	 */
	public ParametricOctMatrix subtract(final ParametricOctMatrix matrix) {
		if (mParametric || matrix.isParametric()) {
			throw new UnsupportedOperationException("Matrix is parametric");
		}
		debug("Subtraction");

		final OctMatrix negated = negateOctMatrix(matrix.getMatrix());

		debug("negated");

		debug(mSize);
		debug(matrix.getSize());

		final ParametricOctMatrix result = new ParametricOctMatrix(mMatrix.add(negated), mVariableMapping);
		debug("...finished.");
		return result;
	}

	private static OctMatrix negateOctMatrix(final OctMatrix matrix) {
		final OctMatrix result = matrix.copy();
		for (int row = 0; row < 2 * matrix.variables(); ++row) {
			for (int col = 0; col < (row / 2 + 1) * 2; ++col) {
				result.set(row, col, matrix.get(row, col).negateIfNotInfinity());
			}
		}
		return result;
	}

	/**
	 * Compares this Matrix with another.
	 *
	 * @param other
	 *            ParametricOctMatrix to compare with
	 * @return true if all elements of the matrices are equal.
	 */
	public boolean isEqualTo(final ParametricOctMatrix other) {

		if (other == null) {
			return false;
		}

		if (!(this.getClass().equals(other.getClass()))) {
			return false;
		}

		final ParametricOctMatrix otherMatrix = other;
		if (isParametric() != otherMatrix.isParametric()) {
			return false;
		}
		if (!getMatrix().isEqualTo(otherMatrix.getMatrix())) {
			return false;
		}
		debug(isParametric());
		debug(getParametricVar() == null);
		if (isParametric() && otherMatrix.isParametric()) {
			if (!getParametricVar().equals(otherMatrix.getParametricVar())) {
				return false;
			}
			if (!getSummands().isEqualTo(otherMatrix.getSummands())) {
				return false;
			}
		}
		if (!mVariableMapping.equals(otherMatrix.getMapping())) {
			return false;
		}

		final Object j = new Object();
		j.hashCode();

		return true;

	}

	/**
	 *
	 * Multiplies the Matrix with a newly created variable.
	 *
	 * @param varname
	 *            the name of the new variable (will be altered so there are no conflicts).
	 * @param mManagedScript
	 *            the current Script.
	 * @return a new ParamametricOctMatrix, multiplied with the new variable.
	 */
	public ParametricOctMatrix multiplyVar(final String varname, final ManagedScript mManagedScript) {
		if (isParametric()) {
			throw new IllegalArgumentException("Octagon already parametric.");
		}
		final TermVariable var = mManagedScript.constructFreshTermVariable(varname,
				mManagedScript.getScript().sort(SmtSortUtils.INT_SORT));
		return multipyVar(var);

	}

	/**
	 *
	 * Multiplies the Matrix with an existing variable.
	 *
	 * @param var
	 *            the variable
	 * @param script
	 *            the current Script.
	 * @return a new ParamametricOctMatrix, multiplied with the new variable.
	 */
	public ParametricOctMatrix multipyVar(final TermVariable var) {
		return new ParametricOctMatrix(mMatrix, mVariableMapping, var);
	}

	public ParametricOctMatrix multiplyConstant(final BigDecimal bigDecimal) {
		final OctMatrix newMatrix = mMatrix.copy();
		for (int row = 0; row < 2 * mMatrix.variables(); ++row) {
			for (int col = 0; col < (row / 2 + 1) * 2; ++col) {
				final OctValue newValue = (mMatrix.get(row, col).isInfinity() ? OctValue.INFINITY
						: new OctValue(mMatrix.get(row, col).getValue().multiply(bigDecimal)));
				newMatrix.set(row, col, newValue);
			}
		}
		if (!mParametric) {
			return new ParametricOctMatrix(newMatrix, mVariableMapping);
		}
		final OctMatrix newSummands = mSummands.copy();
		for (int row = 0; row < 2 * mSummands.variables(); ++row) {
			for (int col = 0; col < (row / 2 + 1) * 2; ++col) {
				newSummands.set(row, col, mSummands.get(row, col).isInfinity() ? OctValue.INFINITY
						: new OctValue(mSummands.get(row, col).getValue().multiply(bigDecimal)));
			}
		}
		return new ParametricOctMatrix(newMatrix, newSummands, mVariableMapping, mParametricVar);
	}

	public static final BiFunction<OctValue, OctValue, OctValue> sAddIgnoreInf = (x, y) -> {
		if (x.isInfinity() && y.isInfinity()) {
			return OctValue.INFINITY;
		}
		final OctValue newX = x.isInfinity() ? OctValue.ZERO : x;
		final OctValue newY = y.isInfinity() ? OctValue.ZERO : y;
		return newX.add(newY);
	};

	private OctMatrix addMatrices(final OctMatrix first, final OctMatrix second, final boolean infAsZero) {
		if (!infAsZero) {
			return first.add(second);
		}
		return first.elementwiseOperation(second, sAddIgnoreInf);
	}

	// ********************************
	// CONSTRUCTION FUNCTIONS
	// ********************************

	/**
	 * Adds a new variable to the matrix and is stored in.
	 *
	 * @param var
	 *            the variable to be added.
	 * @return the position of the new variable.
	 */
	public int addVar(final TermVariable var) {
		debug("Adding " + var.toString() + " to Mapping");
		mVariableMapping.put(var, mNextMaxValue);
		reverseMapping(var);
		if (mSize < mVariableMapping.size()) {
			debug("Size too small. " + mSize + " " + mVariableMapping.size() * 2);
			mMatrix = mMatrix.addVariables(1);
			mSize = mVariableMapping.size();
			assert mSize == mMatrix.getSize() : "ERROR MATRIX SIZES DO NOT MATCH";
		}
		mNextMaxValue = mNextMaxValue + 2;
		return mVariableMapping.get(var);
	}

	/**
	 * Sets a value for OctagonTerms of the form (+/- 2x <= c)
	 *
	 * @param value
	 *            the constant c.
	 * @param var
	 *            the variable x.
	 * @param negative
	 *            true if the Variable x has a negative coefficient.
	 */
	public void setValue(final Object value, final TermVariable var, final boolean negative) {
		setValue(value, var, negative, var, negative);
	}

	/**
	 * Sets a value for OctagonTerms either of form (A) (+/- 2x <= c) or (B) (+/- x +/- y <= c). If firstVar ==
	 * secondVar the function assumes form (A), else form (B).
	 *
	 * @param value
	 *            the constant c.
	 * @param firstVar
	 *            the variable x.
	 * @param firstNegative
	 *            true if x has a negative coefficient.
	 * @param secondVar
	 *            the variable y.
	 * @param secondNegative
	 *            true if y has a negative coefficient.
	 */
	public void setValue(final Object value, final TermVariable firstVar, final boolean firstNegative,
			final TermVariable secondVar, final boolean secondNegative) {
		debug("Setting value: " + value.toString());
		debug("FirstVar: " + firstVar.toString());
		debug("SecondVar: " + secondVar.toString());
		int row;
		int column;
		if (mVariableMapping.containsKey(firstVar)) {
			row = mVariableMapping.get(firstVar);
			debug("Row already known: " + row);
		} else {
			row = addVar(firstVar);
			debug("Row new Variable: " + row);
		}
		if (firstVar.equals(secondVar)) {
			column = row;
		} else {
			if (mVariableMapping.containsKey(secondVar)) {
				column = mVariableMapping.get(secondVar);
				debug("Column already known: " + column);
			} else {
				column = addVar(secondVar);
				debug("Column new Variable: " + column);
			}
		}

		if (firstNegative) {
			row += 1;
		}
		if (!secondNegative) {
			column += 1;
		}

		debug("Setting [" + row + "," + column + "] = " + value.toString());

		setValue(row, column, (BigDecimal) value);

	}

	private void setValue(final int row, final int column, final BigDecimal value) {
		mMatrix.setMin(row, column, new OctValue(value));
	}

	private void reverseMapping() {
		for (final TermVariable t : mVariableMapping.keySet()) {
			mReverseMapping.put(mVariableMapping.get(t), t);
		}
	}

	private void reverseMapping(final TermVariable t) {
		mReverseMapping.put(mVariableMapping.get(t), t);
	}

	// ********************************
	// TRANSFORMATION FUNCTIONS
	// ********************************

	// TODO: FIX TO ROW - COLUMN

	/**
	 * Transform the matrix into an OctagonConcatination.
	 *
	 * @return OctagonConcatination equivalent to the ParametricOctMatrix
	 */
	public OctConjunction toOctConjunction() {
		return toOctConjunction(0);
	}

	/**
	 * Transform the matrix into an OctagonConcatination.
	 *
	 * @param i
	 *            return as (n+i)*c1 + c2
	 *
	 * @return OctagonConcatination equivalent to the ParametricOctMatrix
	 */
	public OctConjunction toOctConjunction(final int i) {
		debug("Converting to Octagon conjunction");
		final OctConjunction conjunct = new OctConjunction();
		final ArrayList<OctTerm> conjunctTerms = new ArrayList<>();
		for (int row = 0; row < 2 * varCount(); ++row) {

			for (int col = 0; col < (row / 2 + 1) * 2; ++col) {

				debug("Row, Col: " + row + ", " + col);
				final OctValue coefficient = mMatrix.get(row, col);
				debug(coefficient.toString());

				final OctValue summand = mParametric ? mSummands.get(row, col) : OctValue.INFINITY;

				if (coefficient.isInfinity() && summand.isInfinity()) {
					continue;
				} else if (coefficient.isInfinity()) {
					conjunctTerms.add(toNonParametricTerm(summand, row, col));
				} else if (mParametric) {
					conjunctTerms.add(toParametricTerm(coefficient, summand, row, col, i));
				} else if (summand.isInfinity()) {
					conjunctTerms.add(toNonParametricTerm(coefficient, row, col));
				}
			}

		}

		for (final OctTerm t : conjunctTerms) {
			conjunct.addTerm(t);
		}

		return conjunct;

	}

	private OctTerm toNonParametricTerm(final OctValue value, int row, int col) {

		final boolean firstNegative = (row % 2) != 0;
		final boolean secondNegative = (col % 2) == 0;
		if ((row & 1) != 0) {
			row--;
		}
		if ((col & 1) != 0) {
			col--;
		}
		return OctagonFactory.createTwoVarOctTerm(value.getValue(), mReverseMapping.get(row), firstNegative,
				mReverseMapping.get(col), secondNegative);
	}

	private OctTerm toParametricTerm(final OctValue coefficient, final OctValue summand, int row, int col,
			final int i) {

		final boolean firstNegative = (row % 2) != 0;
		final boolean secondNegative = (col % 2) == 0;
		if ((row & 1) != 0) {
			row--;
		}
		if ((col & 1) != 0) {
			col--;
		}

		final ParametricOctValue value = new ParametricOctValue(coefficient.getValue(),
				summand.isInfinity() ? BigDecimal.ZERO : summand.getValue(), mParametricVar, new BigDecimal(i));

		return OctagonFactory.createTwoVarOctTerm(value, mReverseMapping.get(row), firstNegative,
				mReverseMapping.get(col), secondNegative);
	}

	/**
	 * Get the matrix as a Term in the form of an octagon concatination.
	 *
	 * @param script
	 *            the current Script.
	 * @return Term equivalent to the ParametricOctMatrix
	 */
	public Term toTerm(final Script script) {
		return toOctConjunction().toTerm(script);
	}

	// ********************************
	// UTILITY FUNCTIONS
	// ********************************

	/**
	 *
	 * @return The Matrix of constants / coefficients.
	 */
	public OctMatrix getMatrix() {
		return mMatrix.copy();
	}

	/**
	 *
	 * @return the column and row count
	 */
	public int getSize() {
		return mSize;
	}

	/**
	 *
	 * @return the amount of different variables represented in the matrix.
	 */
	public int varCount() {
		if (mVariableMapping.size() != mSize / 2) {

		}

		return mVariableMapping.size();
	}

	/**
	 *
	 * @return true if the Object is parametric.
	 */
	public boolean isParametric() {
		return mParametric;
	}

	/**
	 *
	 * @return The variable k (parametric variable).
	 */
	public TermVariable getParametricVar() {
		if (!isParametric()) {
			return null;
		}
		return mParametricVar;
	}

	/**
	 *
	 * @return the matrix of summands.
	 */
	public OctMatrix getSummands() {
		if (!isParametric()) {
			return null;
		}
		return mSummands.copy();
	}

	/**
	 * Get the Value of a specified row and column
	 *
	 * @param row
	 *            row
	 * @param col
	 *            column
	 * @return ParametricOctValue if the Matrix is parametric, BigDecimal if not.
	 */
	public Object getValue(final int row, final int col) {
		if (mParametric) {
			final OctValue value1 = mMatrix.get(row, col);
			if (value1.equals(OctValue.INFINITY)) {
				return null;
			}
			final OctValue value2 = mSummands.get(row, col);
			if (value2.equals(OctValue.INFINITY)) {
				return new ParametricOctValue(value1.getValue(), BigDecimal.ZERO, mParametricVar);
			}
			return new ParametricOctValue(value1.getValue(), value2.getValue(), mParametricVar);
		}
		final OctValue value = mMatrix.get(row, col);
		if (value.equals(OctValue.INFINITY)) {
			return null;
		}
		return value.getValue();
	}

	/**
	 *
	 * @return Map from Variables to their location in the matrix.
	 */
	public Map<TermVariable, Integer> getMapping() {
		return mVariableMapping;
	}

	/**
	 *
	 * @return A fresh copy of the current Matrix
	 */
	public ParametricOctMatrix copy() {
		if (mParametric) {
			return new ParametricOctMatrix(mMatrix, mSummands, mVariableMapping, mParametricVar);
		}
		return new ParametricOctMatrix(mMatrix, mVariableMapping);
	}

	@Override
	public String toString() {
		String result = "ParametricOctMatrix";
		if (isParametric()) {
			result = result + " with parametric Variable " + mParametricVar.toString() + ":\n";
			result = result + "Coefficients: \n";
			result = result + mMatrix.toString();
			result = result + "\n";
			result = result + "Summands: \n";
			result = result + mSummands.toString();
		} else {
			result = result + ":\n";
			result = result + mMatrix.toString();
		}
		result = result + "\n VariableMapping: " + mVariableMapping.toString();
		return result;
	}

	private boolean mappingMatch(final ParametricOctMatrix summand) {
		return summand.getMapping().equals(mVariableMapping);
	}

	private void debug(final Object obj) {
		if (mLogger != null) {
			mLogger.debug(obj);
		}
	}

}
