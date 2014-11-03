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
 * mAColumns, where the rows are the non-basic variables and the columns
 * the integer variables.  This matrix is then brought to hermite normal
 * form, where the inverse transformation matrix is stored in mURows.
 *
 * The matrix U and A are always kept in sync, such that A*U stays constant.
 * Initially x = A*U*v where U is identity matrix .  Finally, x = A'*U'*v,
 * where A' is in Hermite Normal Form and U' is unimodular. Since U' is
 * unimodular, it is invertible in Z^n*n and v is integer if and only
 * if U'*v is integer.  Lets define v' = U'*v.  Then v' are the cut variables
 * on which we branch.
 *
 * Why does this work better then branching directly on v?  The reason is that
 * the constraint system A'*v' is much nicer, as it is in Hermite normal form.
 * If one of the variables in v' is set to integer, it cannot force later 
 * variables to go to a fraction as long as the constraint system remains to be
 * dominated by the constraints for x.  As long as no constraint other than our
 * initial constraints and the generated branches become a non-basic, the 
 * matrix U' stays the same, thus we will eventually get an integer solution.
 *
 * When comparing this algorithm to the original Cuts from Proofs paper, note
 * that H^{-1}A is U', since H is A' and A'U' = AU = A.   H^-1b is only 
 * computed indirectly by determining the current value of v'.
 *
 * In the LIRA case some variables are real-valued.  We are only interested in
 * the integer valued variables we want
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
		
		public Column(LinVar[] indices, BigInteger[] coeffs) {
			mIndices = indices;
			mCoeffs = coeffs;
		}

		/**
		 * Negates the column, i.e., the coefficients.
		 */
		public void negate() {
			for (int i = 0; i < mCoeffs.length; i++)
				mCoeffs[i] = mCoeffs[i].negate();
		}

		/**
		 * Adds another column multiplied with factor to this column.
		 * @param other  the other column.
		 * @param factor the factor.
		 */
		public void addmul(Column other, BigInteger factor) {
			LinVar[] newIndices = new LinVar[mIndices.length + other.mIndices.length];
			BigInteger[] newCoeffs = new BigInteger[newIndices.length];
			int idx = 0, oidx = 0, newidx = 0;
			while (idx < mIndices.length && oidx < other.mIndices.length) {
				if (mIndices[idx] == other.mIndices[oidx]) {
					BigInteger newcoeff = 
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
		
		public String toString() {
			StringBuilder sb = new StringBuilder();
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
	 * are the original non-basic variables, that have to be integral.
	 */
	public class Row {
		LinVar[] mIndices;
		BigInteger[] mCoeffs;
		InfinitNumber mCurval;
		
		public Row(LinVar nonbasic) {
			if (nonbasic.isInitiallyBasic()) {
				Map<LinVar, BigInteger> linterm = nonbasic.getLinTerm();
				mIndices = new LinVar[linterm.size()];
				mCoeffs = new BigInteger[linterm.size()];
				int i = 0;
				for (Map.Entry<LinVar, BigInteger> entry
					: linterm.entrySet()) {
					mIndices[i] = entry.getKey();
					mCoeffs[i] = entry.getValue();
					i++;
				}
			} else {
				mIndices = new LinVar[] { nonbasic };
				mCoeffs = new BigInteger[] { BigInteger.ONE };
			}
			assert (mIndices.length > 0);
			mCurval = nonbasic.mCurval;
		}
		
		/**
		 * Negates the row, i.e., the coefficients.
		 */
		public void negate() {
			for (int i = 0; i < mCoeffs.length; i++)
				mCoeffs[i] = mCoeffs[i].negate();
			mCurval = mCurval.negate();
		}

		/**
		 * Adds another row multiplied with a factor to this row.
		 * @param other the other row.
		 * @param factor the factor.
		 */
		public void addmul(Row other, BigInteger factor) {
			LinVar[] newIndices = new LinVar[mIndices.length + other.mIndices.length];
			BigInteger[] newCoeffs = new BigInteger[newIndices.length];
			int idx = 0, oidx = 0, newidx = 0;
			while (idx < mIndices.length && oidx < other.mIndices.length) {
				if (mIndices[idx] == other.mIndices[oidx]) {
					BigInteger newcoeff = 
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
			Rational fac = Rational.valueOf(factor, BigInteger.ONE);
			mCurval = mCurval.addmul(other.mCurval, fac);
		}
		
		public String getVar() {
			StringBuilder sb = new StringBuilder();
			String plus = "";
			for (int i = 0; i < mIndices.length; i++) {
				sb.append(plus).append(mCoeffs[i])
					.append(" * (").append(mIndices[i]).append(')');
				plus = " + ";
			}
			return sb.toString();
		}
		
		public String toString() {
			StringBuilder sb = new StringBuilder();
			sb.append(getVar());
			sb.append(" == ").append(mCurval);
			return sb.toString();
		}

		/**
		 * Create a constraints that branches on the current row.
		 * @return the literal representing variable <= rounded current value.
		 */
		public Literal createConstraint() {
			MutableAffinTerm mat = new MutableAffinTerm();
			int maxlevel = 0;
			for (int i = 0; i < mIndices.length; i++) {
				if (maxlevel < mIndices[i].mAssertionstacklevel)
					maxlevel = mIndices[i].mAssertionstacklevel;
				mat.add(Rational.valueOf(mCoeffs[i], BigInteger.ONE), mIndices[i]);
			}
			mat.add(mCurval.floor().negate());
			return mSolver.generateConstraint(mat, false, maxlevel);
		}
	}

	LinArSolve mSolver;
	/**
	 * The unimodular transformation matrix stored as rows.
	 * A unimodular matrix has determinant +/-1.
	 * The matrix always satisfies U^t = U^{-1}.
	 */
	Row[] mURows;
	/**
	 * The matrix A.  This is transformed into Hermite normal
	 * form.  The class maintains the invariant A = U * origA.
	 */
	Column[] mAColumns;
	
	private int compare(LinVar v1, LinVar v2) {
		if (v1.mIsInt != v2.mIsInt)
			return v1.mIsInt ? 1 : -1;
		return v1.mMatrixpos - v2.mMatrixpos;
	}
	
	/**
	 * Creates the A matrix for the given solver state and initializes
	 * the U matrix to the unit matrix.  The rows of the A matrix are
	 * the current non-basic variables (that define the current vertex)
	 * and the columns are the initial non-basic variables.
	 * @param solver  The linear arithmetic solver.
	 */
	public void computeMatrix(LinArSolve solver) {
		final class LinVarBigInt implements Comparable<LinVarBigInt> {
			LinVar mRow;
			BigInteger mCoeff;
			public LinVarBigInt(LinVar r, BigInteger c) {
				mRow = r;
				mCoeff = c;
			}
			
			void addToMap(Map<LinVar, Collection<LinVarBigInt>> map, LinVar lv) {
				Collection<LinVarBigInt> column = map.get(lv);
				if (column == null) {
					column = new TreeSet<LinVarBigInt>();
					map.put(lv, column);
				}
				column.add(this);
			}

			@Override
			public int compareTo(LinVarBigInt o) {
				return compare(this.mRow, o.mRow);
			}
			
		}
		Map<LinVar, Collection<LinVarBigInt>> colmap = 
			new TreeMap<LinVar, Collection<LinVarBigInt>>();
		for (LinVar lv : solver.mLinvars) {
			if (lv.mBasic)
				continue;
			boolean negated = false;
			if (lv.mCurval.lesseq(lv.getLowerBound()))
				negated = true;
			if (lv.isInitiallyBasic()) {
				for (Map.Entry<LinVar, BigInteger> entry
					: lv.getLinTerm().entrySet()) {
					if (entry.getKey().isInt()) {
						BigInteger value = entry.getValue();
						if (negated)
							value = value.negate();
						new LinVarBigInt(lv, value)
							.addToMap(colmap, entry.getKey());
					}
				}
			} else if (lv.isInt()) {
				new LinVarBigInt(lv, BigInteger.valueOf(negated ?  -1 : 1))
					.addToMap(colmap, lv);
			}
		}
		mAColumns = new Column[colmap.size()];
		mURows = new Row[colmap.size()];
		int i = 0;
		for (Map.Entry<LinVar, Collection<LinVarBigInt>> e : colmap.entrySet()) {
			Collection<LinVarBigInt> list = e.getValue();
			LinVar[] indices = new LinVar[list.size()];
			BigInteger[] coeffs = new BigInteger[list.size()];
			int j = 0;
			for (LinVarBigInt ib : list) {
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
	 * are zero.  Afterward the nr-th column is substracted from column 0
	 * to nr-1 to make the coefficients as small as possible.
	 * 
	 * This assumes that the columns smaller than nr has been normalized
	 * before.
	 * @param nr the row of U resp. column of A to normalize.
	 */
	private void mgcdColumn(int nr) {
		/* find row to work on. */
		LinVar row = mAColumns[nr].mIndices[0];
		for (int i = nr + 1; i < mAColumns.length; i++) {
			if (compare(mAColumns[i].mIndices[0], row) < 0)
				row = mAColumns[i].mIndices[0];
		}
		
		/* reorder columns: put zero columns at end,
		 * put column with smallest absolute coeff at front.
		 */
		int end = mAColumns.length;
		while (end > nr + 1) {
			while (mAColumns[end - 1].mIndices[0] != row)
				end--;
			assert(end > nr);
			for (int i = nr; i < end; i++) {
				assert mAColumns[end - 1].mIndices[0] == row;
				if (mAColumns[i].mIndices[0] != row) {
					// move to end
					Column tc = mAColumns[i];
					mAColumns[i] = mAColumns[--end];
					mAColumns[end] = tc;
					
					Row tr = mURows[i];
					mURows[i] = mURows[end];
					mURows[end] = tr;
				}
				while (mAColumns[end - 1].mIndices[0] != row)
					end--;
				assert mAColumns[nr].mIndices[0] == row;
				assert mAColumns[i].mIndices[0] == row;
				if (mAColumns[nr].mCoeffs[0].abs().compareTo(
						mAColumns[i].mCoeffs[0].abs()) > 0) {
					// move to front
					Column tc = mAColumns[i];
					mAColumns[i] = mAColumns[nr];
					mAColumns[nr] = tc;

					Row tr = mURows[i];
					mURows[i] = mURows[nr];
					mURows[nr] = tr;
				}
			}
			// make positive
			if (mAColumns[nr].mCoeffs[0].signum() < 0) {
				mAColumns[nr].negate();
				mURows[nr].negate();
			}
			
			// now reduce all other rows with row[nr].
			BigInteger coeffNr = mAColumns[nr].mCoeffs[0];
			BigInteger coeffNr2 = coeffNr.shiftRight(1);
			for (int i = nr + 1; i < end; i++) {
				assert(mAColumns[i].mIndices[0] == row);
				BigInteger coeffI = mAColumns[i].mCoeffs[0];
				if (coeffI.signum() < 0) {
					coeffI = coeffI.subtract(coeffNr2);
				} else {
					coeffI = coeffI.add(coeffNr2);
				}
				BigInteger div = coeffI.divide(coeffNr);
				assert (div.signum() != 0);
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
		
		// Finally reduce the rows left of this column.
		BigInteger coeffNr = mAColumns[nr].mCoeffs[0];
		BigInteger coeffNrM1 = coeffNr.subtract(BigInteger.ONE);
		BigInteger coeffNr2 = coeffNr.shiftRight(1);
		BigInteger coeffNr32 = coeffNr.shiftRight(5);// NOCHECKSTYLE
		for (int i = 0; i < nr; i++) {
			int j = 0;
			while (j < mAColumns[i].mIndices.length
					&& compare(mAColumns[i].mIndices[j], row) < 0)
				j++;
			if (j == mAColumns[i].mIndices.length
				|| mAColumns[i].mIndices[j] != row)
				continue;
			assert(mAColumns[i].mIndices[j] == row);
			BigInteger coeffI = mAColumns[i].mCoeffs[j];
			if (mAColumns[i].mIndices[0].getUpperBound()
				.equals(mAColumns[i].mIndices[0].getLowerBound())) {
				/* This is an equality constraint 
				 * make remainder small, i.e rem.abs() <= coeffNr2
				 */
				if (coeffI.signum() < 0) {
					coeffI = coeffI.subtract(coeffNr2);
				} else {
					coeffI = coeffI.add(coeffNr2);
				}
			} else {
				/* This is an lessequal constraint 
				 * make remainder negative
				 */
				if (coeffI.signum() > 0) {
					coeffI = coeffI.add(coeffNrM1);
				}
				coeffI = coeffI.subtract(coeffNr32);
			}
			BigInteger div = coeffI.divide(coeffNr);
			if (div.signum() != 0) {
				mAColumns[i].addmul(mAColumns[nr], div.negate());
				mURows[nr].addmul(mURows[i], div);
			}
		}
		assert(nr + 1 == mAColumns.length
				|| mAColumns[nr + 1].mIndices[0] != row);
	}

	private boolean isTight(LinVar linVar) {
		return linVar.mCurval.lesseq(linVar.getLowerBound())
			|| linVar.getUpperBound().lesseq(linVar.mCurval);
	}

	private boolean[] computeTightness() {
		boolean[] tight = new boolean[mAColumns.length];
		for (int i = 0; i < mAColumns.length; i++)
			tight[i] = true;
		for (int i = 0; i < mAColumns.length; i++) {
			if (!isTight(mAColumns[i].mIndices[0]))
				tight[i] = false;
			if (!tight[i]) {
				int k = i + 1;
				for (int j = 1; j < mAColumns[i].mIndices.length; j++) {
					while (k < mAColumns.length 
							&& compare(mAColumns[k].mIndices[0], 
									mAColumns[i].mIndices[j]) < 0)
						k++;
					if (k < mAColumns.length 
						&& mAColumns[k].mIndices[0] == mAColumns[i].mIndices[j])
						tight[k] = false;
				}
			}
		}
		return tight;
	}

	private boolean[] computeBadness() {
		boolean[] isBad = new boolean[mAColumns.length];
		for (int i = 0; i < mAColumns.length; i++) {
			if (mURows[i].mCurval.isIntegral()) {
				isBad[i] = true;
			} else {
				int k = i + 1;
				for (int j = 1; j < mAColumns[i].mIndices.length; j++) {
					while (k < mAColumns.length 
							&& compare(mAColumns[k].mIndices[0], 
								mAColumns[i].mIndices[j]) < 0)
						k++;
					if (k < mAColumns.length 
						&& mAColumns[k].mIndices[0] == mAColumns[i].mIndices[j])
						isBad[k] = true;
				}
			}
		}
		return isBad;
	}

	public void generateCut(int row, boolean isTight) {
		assert mURows[row].mIndices[0].mIsInt;
		assert !mURows[row].mCurval.isIntegral();
		BoundConstraint cut = (BoundConstraint)
				mURows[row].createConstraint().getAtom();
		LinVar cutVar = cut.getVar();
		if (cutVar.mCurval.less(cutVar.getLowerBound())) {
//			m_solver.mengine.getLogger().debug("cut: " + cut.negate());
			mSolver.mOob.add(cutVar);
			mSolver.mProplist.add(cut.negate());
			mSolver.mNumCuts++;
		} else if (cutVar.getUpperBound().less(cutVar.mCurval)) {
//			m_solver.mengine.getLogger().debug("cut: " + cut);
			mSolver.mOob.add(cutVar);
			mSolver.mProplist.add(cut);
			mSolver.mNumCuts++;
		} else {
			mSolver.mEngine.getLogger().debug("branch on " + cut);
			assert(!mSolver.mOob.isEmpty() || cut.getAtom().getDecideStatus() == null);
			mSolver.mSuggestions.add(cut);
			mSolver.mNumBranches++;
		}
	}

	public CutCreator(LinArSolve solver) {
		mSolver = solver;
		solver.calculateSimpVals();
		computeMatrix(solver);
	}
	
	public void generateCuts() {
		for (int i = 0; i < mAColumns.length; i++)
			mgcdColumn(i);
		if (mSolver.mEngine.getLogger().isDebugEnabled()) {
			mSolver.mEngine.getLogger().debug("Cuts From Proofs");
			mSolver.mEngine.getLogger().debug("cols");
			for (int i = 0; i < mAColumns.length; i++) {
				if (mAColumns[i].mCoeffs.length != 1
						|| !mAColumns[i].mCoeffs[0].equals(BigInteger.ONE))
					mSolver.mEngine.getLogger().debug("[" + i + "] " + mAColumns[i]);
			}
			mSolver.mEngine.getLogger().debug("rows");
			for (int i = 0; i < mURows.length; i++) {
				mSolver.mEngine.getLogger().debug("[" + i + "] " + mURows[i]);
			}
		}
		
		boolean[] tight = computeTightness();
		boolean[] isBad = computeBadness();
		int best = -1;
		int bestlen = Integer.MAX_VALUE;
		int bestsize = Integer.MAX_VALUE;
		for (int i = 0; i < mURows.length; i++) {
			if (isBad[i])
				continue;
			/* prefer cuts over branches */
			if (!tight[i] && (best >= 0 && tight[best]))
				continue;
			/* prefer short cuts */
			if (mURows[i].mCoeffs.length > bestlen && tight[best] == tight[i])
				continue;
			/* prefer small cuts */
			int max = 0;
			for (BigInteger coeff : mURows[i].mCoeffs)
				max = Math.max(max, coeff.bitLength());
			if (max >= bestsize 
				&& mURows[i].mCoeffs.length == bestlen 
				&& tight[best] == tight[i])
				continue;
			
			best = i;
			bestsize = max;
			bestlen = mURows[i].mCoeffs.length;
		}
		if (best != -1)
			generateCut(best, tight[best]);
	}
}
