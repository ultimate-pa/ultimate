/*
 * Copyright (C) 2009-2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar;

import java.math.BigInteger;
import java.util.Collection;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;


/**
 * The Cut creator generates cuts using the Cuts from Proofs algorithm.
 * It starts by collecting the non-basic variables and building a matrix
 * mAColumns, where the rows are the current non-basic variables (the ones
 * defining the current vertex) and the columns the variables of the formula.
 * This matrix is then brought to hermite normal form, where the inverse
 * transformation matrix is stored in mURows.
 *
 * The matrix U and A are always kept in sync, such that A*U stays constant.
 * Initially x = A*U*v where U is identity matrix .  Finally, x = A'*U'*v,
 * where A' is in Hermite Normal Form and U' is unimodular. Since U' is
 * unimodular, it is invertible in Z^n*n and v is integer if and only
 * if U'*v is integer.  Lets define v' = U'*v.  Then v' are the cut variables
 * on which we branch.
 *
 * Why does this work better then branching directly on v?
 * In a certain sense the cut variables v' form a new basis and every integer
 * solution for these new variables leads to an integer solution of the original
 * problem. Now the constraint system A'*v' is much nicer, as it is in
 * Hermite normal form.  If one of the variables in v' is set to integer, it
 * cannot force later variables to go to a fraction as long as the constraint
 * system remains to be dominated by the constraints for x.  As long as no
 * constraint other than our initial constraints and the generated branches
 * become a non-basic, the matrix U' stays the same, thus we will eventually
 * get an integer solution.
 *
 * Also by the way we choose the sign in the Hermite normal form we will even
 * force the new cut variables to lead to real cuts.  They will replace the
 * non-basic variable that they represent in the tableaux in the next pivot
 * step (only guaranteed when using Bland's rule though).
 *
 * When comparing this algorithm to the original Cuts from Proofs paper, note
 * that H^{-1}A is U', since H is A' and A'U' = AU = A.   H^-1b is only
 * computed indirectly by determining the current value of v'.
 *
 * In the LIRA case some variables are real-valued.  In the matrix we make sure
 * that we keep the integer variables in U*v.  This is achieved by never adding
 * a real row in U to an integer row.  This means we may never add a column
 * for a integer in A to a column for a real. Thus we cannot get a strict
 * Hermite form anymore as the "real columns" in A are not reduced by "integer
 * columns".  Still the new cuts will replace their corresponding non-basics and
 * in the end the tableaux will have as many integer non-basics as there are
 * integer variables.  At that point we will have a Hermite form again.
 *
 * @author Jochen Hoenicke
 */
public class CutCreator {

	/**
	 * Class to represent a column of a sparse matrix.  This is used for
	 * the A matrix, which is stored as an array of columns.
	 *
	 * The rows of this matrix are LinVars, more exactly the current
	 * non-basic variables that define the current vertex.  The columns
	 * are the v' variables that become the cuts.
	 */
	public class Column {
		LinVar[] mIndices;
		BigInteger[] mCoeffs;

		public Column(final LinVar[] indices, final BigInteger[] coeffs) {
			mIndices = indices;
			mCoeffs = coeffs;
		}

		/**
		 * Negates the column, i.e., the coefficients.
		 */
		public void negate() {
			for (int i = 0; i < mCoeffs.length; i++) {
				mCoeffs[i] = mCoeffs[i].negate();
			}
		}

		/**
		 * Adds another column multiplied with factor to this column.
		 * @param other  the other column.
		 * @param factor the factor.
		 */
		public void addmul(final Column other, final BigInteger factor) {
			final LinVar[] newIndices = new LinVar[mIndices.length + other.mIndices.length];
			final BigInteger[] newCoeffs = new BigInteger[newIndices.length];
			int idx = 0, oidx = 0, newidx = 0;
			while (idx < mIndices.length && oidx < other.mIndices.length) {
				if (mIndices[idx] == other.mIndices[oidx]) {
					final BigInteger newcoeff =
						mCoeffs[idx].add(other.mCoeffs[oidx].multiply(factor));
					if (newcoeff.signum() != 0) {
						newIndices[newidx] = mIndices[idx];
						newCoeffs[newidx] = newcoeff;
						newidx++;
					}
					idx++;
					oidx++;
				} else if (compare(mIndices[idx], other.mIndices[oidx]) < 0) {
					newIndices[newidx] = mIndices[idx];
					newCoeffs[newidx] = mCoeffs[idx];
					newidx++;
					idx++;
				} else {
					newIndices[newidx] = other.mIndices[oidx];
					newCoeffs[newidx] = other.mCoeffs[oidx].multiply(factor);
					newidx++;
					oidx++;
				}
			}
			while (idx < mIndices.length) {
				newIndices[newidx] = mIndices[idx];
				newCoeffs[newidx] = mCoeffs[idx];
				newidx++;
				idx++;
			}
			while (oidx < other.mIndices.length) {
				newIndices[newidx] = other.mIndices[oidx];
				newCoeffs[newidx] = other.mCoeffs[oidx].multiply(factor);
				newidx++;
				oidx++;
			}
			assert newidx > 0;
			if (newidx < newCoeffs.length) {
				mIndices = new LinVar[newidx];
				mCoeffs = new BigInteger[newidx];
				System.arraycopy(newIndices, 0, mIndices, 0, newidx);
				System.arraycopy(newCoeffs, 0, mCoeffs, 0, newidx);
			} else {
				mIndices = newIndices;
				mCoeffs = newCoeffs;
			}
		}

		@Override
		public String toString() {
			final StringBuilder sb = new StringBuilder();
			String plus = "";
			for (int i = 0; i < mIndices.length; i++) {
				sb.append(plus).append(mIndices[i].mMatrixpos)
					.append(": ").append(mCoeffs[i]);
				plus = ", ";
			}
			return sb.toString();
		}
	}

	/**
	 * Class to represent a row of a sparse matrix.  This is used for
	 * the U matrix, which is stored as an array of rows.
	 *
	 * The rows are the v' variables that become the cuts.  The columns
	 * are the original variables of the formula and have to be integral.
	 *
	 * Some rows stem from the real variables of the original formula.  For
	 * these we do not track the U matrix at all as they are never involved
	 * in a cut.  We will just use the isInt flag to detect them.
	 */
	public class Row {
		LinVar[] mIndices;
		BigInteger[] mCoeffs;
		/** This flag is set for integer variables. */
		boolean mIsInt;
		/** This flag is set if a bound can be computed (a cut). */
		boolean mTight;
		/** This flag is set if the variable is fixed to a value by
		 * the non-basics.
		 */
		boolean mFixed;
		Rational mCurval;
		Rational mEpsilons;

		public Row(final LinVar nonbasic) {
			assert !nonbasic.isInitiallyBasic();
			mIsInt = nonbasic.mIsInt;
			if (mIsInt) {
				mIndices = new LinVar[] { nonbasic };
				mCoeffs = new BigInteger[] { BigInteger.ONE };
			} else {
				// Do not compute anything for real rows.
				mIndices = new LinVar[0];
				mCoeffs = new BigInteger[0];
			}
		}

		public boolean isInt() {
			return mIsInt;
		}

		/**
		 * Negates the row, i.e., the coefficients.
		 */
		public void negate() {
			for (int i = 0; i < mCoeffs.length; i++) {
				mCoeffs[i] = mCoeffs[i].negate();
			}
		}

		/**
		 * Adds another row multiplied with a factor to this row.
		 * @param other the other row.
		 * @param factor the factor.
		 */
		public void addmul(final Row other, final BigInteger factor) {
			// Do not compute real rows; they do not lead to cuts anyway.
			if (!isInt()) {
				return;
			}
			assert other.isInt();
			final LinVar[] newIndices = new LinVar[mIndices.length + other.mIndices.length];
			final BigInteger[] newCoeffs = new BigInteger[newIndices.length];
			int idx = 0, oidx = 0, newidx = 0;
			while (idx < mIndices.length && oidx < other.mIndices.length) {
				if (mIndices[idx] == other.mIndices[oidx]) {
					final BigInteger newcoeff =
						mCoeffs[idx].add(other.mCoeffs[oidx].multiply(factor));
					if (newcoeff.signum() != 0) {
						newIndices[newidx] = mIndices[idx];
						newCoeffs[newidx] = newcoeff;
						newidx++;
					}
					idx++;
					oidx++;
				} else if (compare(mIndices[idx], other.mIndices[oidx]) < 0) {
					newIndices[newidx] = mIndices[idx];
					newCoeffs[newidx] = mCoeffs[idx];
					newidx++;
					idx++;
				} else {
					newIndices[newidx] = other.mIndices[oidx];
					newCoeffs[newidx] = other.mCoeffs[oidx].multiply(factor);
					newidx++;
					oidx++;
				}
			}
			while (idx < mIndices.length) {
				newIndices[newidx] = mIndices[idx];
				newCoeffs[newidx] = mCoeffs[idx];
				newidx++;
				idx++;
			}
			while (oidx < other.mIndices.length) {
				newIndices[newidx] = other.mIndices[oidx];
				newCoeffs[newidx] = other.mCoeffs[oidx].multiply(factor);
				newidx++;
				oidx++;
			}
			assert newidx > 0;
			if (newidx < newCoeffs.length) {
				mIndices = new LinVar[newidx];
				mCoeffs = new BigInteger[newidx];
				System.arraycopy(newIndices, 0, mIndices, 0, newidx);
				System.arraycopy(newCoeffs, 0, mCoeffs, 0, newidx);
			} else {
				mIndices = newIndices;
				mCoeffs = newCoeffs;
			}
		}

		public String getVar() {
			final StringBuilder sb = new StringBuilder();
			String plus = "";
			for (int i = 0; i < mIndices.length; i++) {
				sb.append(plus).append(mCoeffs[i])
					.append(" * (").append(mIndices[i]).append(')');
				plus = " + ";
			}
			return sb.toString();
		}

		@Override
		public String toString() {
			final StringBuilder sb = new StringBuilder();
			sb.append(getVar());
			sb.append(" == ").append(mCurval);
			sb.append(" + ").append(mEpsilons).append(" eps");
			return sb.toString();
		}

		/**
		 * Create a constraints that branches on the current row.
		 * @return the literal representing variable <= rounded current value.
		 */
		public Literal createConstraint() {
			assert mIsInt;
			final MutableAffinTerm mat = new MutableAffinTerm();
			for (int i = 0; i < mIndices.length; i++) {
				mat.add(Rational.valueOf(mCoeffs[i], BigInteger.ONE), mIndices[i]);
			}
			mat.add(new InfinitNumber(mCurval, mEpsilons.signum()).floor().negate());
			return mSolver.generateConstraint(mat, false);
		}

		public void computeValue() {
			mCurval = Rational.ZERO;
			mEpsilons = Rational.ZERO;
			for (int i = 0; i < mIndices.length; i++) {
				final LinVar var = mIndices[i];
				final Rational coeff = Rational.valueOf(mCoeffs[i], BigInteger.ONE);
				mCurval = mCurval.addmul(coeff, var.getValue().mA);
				mEpsilons = mEpsilons.addmul(coeff, var.computeEpsilon());
			}
		}

		public boolean isBad() {
			if (!mIsInt) {
				return true;
			}
			return mCurval.isIntegral() && mEpsilons.signum() == 0;
		}

		public void divide(final BigInteger denom) {
			assert(!mIsInt);
			// Do not compute real rows; they do not lead to cuts anyway.
		}
	}

	LinArSolve mSolver;
	/**
	 * The unimodular transformation matrix stored as rows.
	 * A unimodular matrix has determinant +/-1.
	 */
	Row[] mURows;
	/**
	 * The matrix A.  This is transformed into Hermite normal
	 * form.  The class maintains the invariant A * U = origA.
	 */
	Column[] mAColumns;

	private int compare(final LinVar v1, final LinVar v2) {
		return v1.mMatrixpos - v2.mMatrixpos;
	}

	/**
	 * Creates the A matrix for the given solver state and initializes
	 * the U matrix to the unit matrix.  The rows of the A matrix are
	 * the current non-basic variables (that define the current vertex)
	 * and the columns are the initial non-basic variables.
	 * @param solver  The linear arithmetic solver.
	 */
	public void computeMatrix(final LinArSolve solver) {
		final class LinVarBigInt implements Comparable<LinVarBigInt> {
			LinVar mRow;
			BigInteger mCoeff;
			public LinVarBigInt(final LinVar r, final BigInteger c) {
				mRow = r;
				mCoeff = c;
			}

			void addToMap(final Map<LinVar, Collection<LinVarBigInt>> map, final LinVar lv) {
				Collection<LinVarBigInt> column = map.get(lv);
				if (column == null) {
					column = new TreeSet<LinVarBigInt>();
					map.put(lv, column);
				}
				column.add(this);
			}

			@Override
			public int compareTo(final LinVarBigInt o) {
				return compare(mRow, o.mRow);
			}

			@Override
			public String toString() {
				return mCoeff.toString() + "*" + mRow;
			}
		}
		final Map<LinVar, Collection<LinVarBigInt>> colmap =
			new TreeMap<LinVar, Collection<LinVarBigInt>>();
		for (final LinVar lv : solver.mLinvars) {
			if (lv.mBasic) {
				continue;
			}
			boolean negated = false;
			if (lv.getValue().lesseq(lv.getLowerBound())) {
				negated = true;
			}
			if (lv.isInitiallyBasic()) {
				for (final Map.Entry<LinVar, BigInteger> entry
					: lv.getLinTerm().entrySet()) {
					BigInteger value = entry.getValue();
					if (negated) {
						value = value.negate();
					}
					new LinVarBigInt(lv, value)
						.addToMap(colmap, entry.getKey());
				}
			} else {
				new LinVarBigInt(lv, BigInteger.valueOf(negated ?  -1 : 1))
					.addToMap(colmap, lv);
			}
		}
		mAColumns = new Column[colmap.size()];
		mURows = new Row[colmap.size()];
		int i = 0;
		for (final Map.Entry<LinVar, Collection<LinVarBigInt>> e : colmap.entrySet()) {
			final Collection<LinVarBigInt> list = e.getValue();
			final LinVar[] indices = new LinVar[list.size()];
			final BigInteger[] coeffs = new BigInteger[list.size()];
			int j = 0;
			for (final LinVarBigInt ib : list) {
				indices[j] = ib.mRow;
				coeffs[j] = ib.mCoeff;
				assert (j == 0 || compare(indices[j - 1], indices[j]) < 0);
				j++;
			}
			mAColumns[i] = new Column(indices, coeffs);
			// Note that e.getKey() is a initially non-basic variable.
			// Thus, this creates basically an identity matrix.
			mURows[i] = new Row(e.getKey());
			i++;
		}
	}

	/**
	 * Computes the nr-th row of the Hermite Normal Form, by applying the
	 * mgcd algorithm on the columns from nr upwards.  This ensures that
	 * the nr-th column contains the gcd at that row and the later columns
	 * are zero.  Afterward the nr-th column is subtracted from column 0
	 * to nr-1 to make the coefficients as small as possible.
	 *
	 * This assumes that the columns smaller than nr has been normalized
	 * before.
	 * @param nr the row of U resp. column of A to normalize.
	 */
	private void mgcdColumn(final int nr) {
		/* find row to work on. */
		LinVar row = mAColumns[nr].mIndices[0];
		for (int i = nr + 1; i < mAColumns.length; i++) {
			if (compare(mAColumns[i].mIndices[0], row) < 0) {
				row = mAColumns[i].mIndices[0];
			}
		}

		boolean isTight = isTight(row);
		boolean isFixed = isFixed(row);

		/* reorder columns: put zero columns at end,
		 * put column with smallest absolute coeff to the front.
		 * If there is a real non-zero column put that to the front.
		 */
		int end = mAColumns.length;
		while (end > nr + 1) {
			while (mAColumns[end - 1].mIndices[0] != row) {
				end--;
			}
			assert(end > nr);
			for (int i = nr; i < end; i++) {
				assert mAColumns[end - 1].mIndices[0] == row;
				if (mAColumns[i].mIndices[0] != row) {
					// move to end
					final Column tc = mAColumns[i];
					mAColumns[i] = mAColumns[--end];
					mAColumns[end] = tc;

					final Row tr = mURows[i];
					mURows[i] = mURows[end];
					mURows[end] = tr;
				}
				while (mAColumns[end - 1].mIndices[0] != row) {
					end--;
				}
				assert mAColumns[nr].mIndices[0] == row;
				assert mAColumns[i].mIndices[0] == row;
				// there is already a real column at front --> no reorder
				if (!mURows[nr].isInt()) {
					continue;
				}
				if (!mURows[i].isInt()
					|| mAColumns[nr].mCoeffs[0].abs().compareTo(
						mAColumns[i].mCoeffs[0].abs()) > 0) {
					// move to front
					final Column tc = mAColumns[i];
					mAColumns[i] = mAColumns[nr];
					mAColumns[nr] = tc;

					final Row tr = mURows[i];
					mURows[i] = mURows[nr];
					mURows[nr] = tr;
				}
			}
			// make positive
			if (mAColumns[nr].mCoeffs[0].signum() < 0) {
				mAColumns[nr].negate();
				mURows[nr].negate();
			}

			// make one if real
			BigInteger coeffNr = mAColumns[nr].mCoeffs[0];
			if (!mURows[nr].isInt()
				&& !coeffNr.equals(BigInteger.ONE)) {
				mURows[nr].divide(coeffNr);
				for (int i = 0; i < mAColumns[nr].mCoeffs.length; i++) {
					final BigInteger gcd = mAColumns[nr].mCoeffs[i].gcd(coeffNr);
					final BigInteger factor = coeffNr.divide(gcd);
					multiplyARow(mAColumns[nr].mIndices[i], factor);
					mAColumns[nr].mCoeffs[i] = mAColumns[nr].mCoeffs[i].divide(coeffNr);
				}
				coeffNr = BigInteger.ONE;
			}

			// now reduce all other columns with column[nr].
			final BigInteger coeffNr2 = coeffNr.shiftRight(1);
			for (int i = nr + 1; i < end; i++) {
				assert(mAColumns[i].mIndices[0] == row);
				BigInteger coeffI = mAColumns[i].mCoeffs[0];
				if (coeffI.signum() < 0) {
					coeffI = coeffI.subtract(coeffNr2);
				} else {
					coeffI = coeffI.add(coeffNr2);
				}
				final BigInteger div = coeffI.divide(coeffNr);
				mAColumns[i].addmul(mAColumns[nr], div.negate());
				assert(mAColumns[i].mIndices[0] != row
						|| mAColumns[i].mCoeffs[0].abs().compareTo(
								coeffNr2.abs()) <= 0);
				mURows[nr].addmul(mURows[i], div);
			}
		}

		// make positive
		if (mAColumns[nr].mCoeffs[0].signum() < 0) {
			mAColumns[nr].negate();
			mURows[nr].negate();
		}
		final BigInteger coeffNr = mAColumns[nr].mCoeffs[0];

		// Finally reduce the non-real columns left of this column.
		// Reduce all columns if this is real.
		if (coeffNr.equals(BigInteger.ONE)) {
			// common fast case
			for (int i = 0; i < nr; i++) {
				if (!mURows[i].isInt() && mURows[nr].isInt()) {
					continue;
				}
				int j = 0;
				while (j < mAColumns[i].mIndices.length
						&& compare(mAColumns[i].mIndices[j], row) < 0) {
					j++;
				}
				if (j == mAColumns[i].mIndices.length
					|| mAColumns[i].mIndices[j] != row) {
					continue;
				}
				assert(mAColumns[i].mIndices[j] == row);
				final BigInteger div = mAColumns[i].mCoeffs[j];
				mAColumns[i].addmul(mAColumns[nr], div.negate());
				mURows[nr].addmul(mURows[i], div);
			}
		} else {
			final BigInteger limitHalf = coeffNr.shiftRight(1);
			final BigInteger limitSmall = coeffNr.shiftRight(5); // NOCHECKSTYLE
			for (int i = 0; i < nr; i++) {
				int j = 0;
				while (j < mAColumns[i].mIndices.length
						&& compare(mAColumns[i].mIndices[j], row) < 0) {
					j++;
				}
				if (j == mAColumns[i].mIndices.length
					|| mAColumns[i].mIndices[j] != row) {
					continue;
				}
				assert(mAColumns[i].mIndices[j] == row);
				if (!mURows[i].isInt() && mURows[nr].isInt()) {
					// this integer can only be fixed if the dependent real
					// constraint is fixed.
					isFixed &= mURows[i].mFixed;
					continue;
				}
				final BigInteger coeffI = mAColumns[i].mCoeffs[j];
				final BigInteger[] quorem = coeffI.divideAndRemainder(coeffNr);
				BigInteger quo = quorem[0];
				BigInteger rem = quorem[1];
				if (rem.signum() != 0) {
					int adjust = 0;
					// there is a remainder, check if the constraint is fixed.
					isFixed &= mURows[i].mFixed;
					// make remainder positive (stupid java division)
					if (rem.signum() < 0) {
						rem = rem.add(coeffNr);
						adjust = -1;
					}
					BigInteger limit;
					if (mURows[i].mFixed || !isTight
						|| !mURows[i].mTight) {
						/* This is an equality constraint, or we cannot
						 * create a cut anymore.
						 * make remainder small, i.e rem.abs() <= coeffNr2
						 */
						limit = limitHalf;
					} else {
						/*
						 * Make remainder negative.  This will ensure that tight
						 * columns are cuts. But avoid large constants
						 * even if it destroys a cut.
						 */
						limit = limitSmall;
					}
					if (rem.compareTo(limit) >= 0) {
						rem = rem.subtract(coeffNr);
						adjust++;
					}
					if (adjust != 0) {
						quo = quo.add(BigInteger.valueOf(adjust));
					}
					if (!mURows[i].mTight) {
						isTight = false;
					} else if (rem.signum() > 0) {
						isTight &= mURows[i].mFixed;
					}
				}
				if (quo.signum() != 0) {
					mAColumns[i].addmul(mAColumns[nr], quo.negate());
					mURows[nr].addmul(mURows[i], quo);
				}
			}
		}
		mURows[nr].mFixed = isFixed;
		mURows[nr].mTight = isTight;
		mURows[nr].computeValue();
		assert(nr + 1 == mAColumns.length
				|| mAColumns[nr + 1].mIndices[0] != row);
	}

	private void multiplyARow(final LinVar linVar, final BigInteger factor) {
		for (int i = 0; i < mAColumns.length; i++) {
			for (int j = 0; j < mAColumns[i].mIndices.length; j++) {
				if (mAColumns[i].mIndices[j] == linVar) {
					mAColumns[i].mCoeffs[j] =
							mAColumns[i].mCoeffs[j].multiply(factor);
				}
			}
		}
	}

	private boolean isTight(final LinVar linVar) {
		return linVar.getValue().lesseq(linVar.getLowerBound())
			|| linVar.getUpperBound().lesseq(linVar.getValue());
	}

	private boolean isFixed(final LinVar linVar) {
		return linVar.getLowerBound().equals(linVar.getUpperBound());
	}

	/**
	 * Compute which cuts are bad, because they do not help in the current
	 * tableaux.  These are cuts that are already integer and cuts that
	 * depend on another non-bad cut.
	 * @return
	 */
	private boolean[] computeBadness() {
		final boolean[] isBad = new boolean[mAColumns.length];
		for (int i = 0; i < mAColumns.length; i++) {
			if (mURows[i].isBad()) {
				isBad[i] = true;
			} else {
				int k = i + 1;
				for (int j = 1; j < mAColumns[i].mIndices.length; j++) {
					while (k < mAColumns.length
							&& compare(mAColumns[k].mIndices[0],
								mAColumns[i].mIndices[j]) < 0) {
						k++;
					}
					if (k < mAColumns.length
						&& mAColumns[k].mIndices[0] == mAColumns[i].mIndices[j]) {
						isBad[k] = true;
					}
				}
			}
		}
		return isBad;
	}

	public void generateCut(final int row, final boolean isTight) {
		assert mURows[row].mIndices[0].mIsInt;

		final Literal cut = mURows[row].createConstraint();
		if (mSolver.mEngine.getLogger().isDebugEnabled()) {
			mSolver.mEngine.getLogger().debug(
					(isTight ? "cut on " : "branch on ") + cut);
		}
		// suggest branch
		mSolver.mSuggestions.add(cut);
		if (isTight) {
			// cut should be propagated automatically
			mSolver.mNumCuts++;
		} else {
			mSolver.mNumBranches++;
		}
	}

	public CutCreator(final LinArSolve solver) {
		mSolver = solver;
		computeMatrix(solver);
	}

	public void generateCuts() {
		for (int i = 0; i < mAColumns.length; i++) {
			mgcdColumn(i);
		}
		if (mSolver.mEngine.getLogger().isDebugEnabled()) {
			mSolver.mEngine.getLogger().debug("Cuts From Proofs");
			mSolver.mEngine.getLogger().debug("cols");
			for (int i = 0; i < mAColumns.length; i++) {
				if (mAColumns[i].mCoeffs.length != 1
						|| !mAColumns[i].mCoeffs[0].equals(BigInteger.ONE)) {
					mSolver.mEngine.getLogger().debug("[" + i + "] " + mAColumns[i]);
				}
			}
			mSolver.mEngine.getLogger().debug("rows");
			for (int i = 0; i < mURows.length; i++) {
				mSolver.mEngine.getLogger().debug("[" + i + "] " + mURows[i]);
			}
		}

		final boolean[] isBad = computeBadness();
		int best = -1;
		int bestlen = Integer.MAX_VALUE;
		int bestsize = Integer.MAX_VALUE;
		for (int i = 0; i < mURows.length; i++) {
			if (isBad[i]) {
				continue;
			}
			/* prefer cuts over branches */
			if (!mURows[i].mTight && (best >= 0 && mURows[best].mTight)) {
				continue;
			}
			/* prefer short cuts */
			if (mURows[i].mCoeffs.length > bestlen
					&& mURows[best].mTight == mURows[i].mTight) {
				continue;
			}
			/* prefer small cuts */
			int max = 0;
			for (final BigInteger coeff : mURows[i].mCoeffs) {
				max = Math.max(max, coeff.bitLength());
			}
			if (max >= bestsize
				&& mURows[i].mCoeffs.length == bestlen
				&& mURows[best].mTight == mURows[i].mTight) {
				continue;
			}

			best = i;
			bestsize = max;
			bestlen = mURows[i].mCoeffs.length;
		}
		generateCut(best, mURows[best].mTight);
	}
}
