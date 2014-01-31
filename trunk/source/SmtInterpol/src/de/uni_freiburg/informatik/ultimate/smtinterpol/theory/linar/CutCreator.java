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


public class CutCreator {

	public class Column {
		LinVar[] mIndices;
		BigInteger[] mCoeffs;
		
		public Column(LinVar[] indices, BigInteger[] coeffs) {
			mIndices = indices;
			mCoeffs = coeffs;
		}

		public void negate() {
			for (int i = 0; i < mCoeffs.length; i++)
				mCoeffs[i] = mCoeffs[i].negate();
		}

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
		
		public void negate() {
			for (int i = 0; i < mCoeffs.length; i++)
				mCoeffs[i] = mCoeffs[i].negate();
			mCurval = mCurval.negate();
		}

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
	Row[] mRows;
	Column[] mColumns;
	
	private int compare(LinVar v1, LinVar v2) {
		if (v1.mIsInt != v2.mIsInt)
			return v1.mIsInt ? 1 : -1;
		return v1.mMatrixpos - v2.mMatrixpos;
	}
	
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
		mColumns = new Column[colmap.size()];
		mRows = new Row[colmap.size()];
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
			mColumns[i] = new Column(indices, coeffs);
			mRows[i] = new Row(e.getKey());
			i++;
		}
	}
	
	private void mgcdColumn(int nr) {
		/* find row to work on. */
		LinVar row = mColumns[nr].mIndices[0];
		for (int i = nr + 1; i < mColumns.length; i++) {
			if (compare(mColumns[i].mIndices[0], row) < 0)
				row = mColumns[i].mIndices[0];
		}
		
		/* reorder columns: put zero columns at end,
		 * put column with smallest absolute coeff at front.
		 */
		int end = mColumns.length;
		while (end > nr + 1) {
			while (mColumns[end - 1].mIndices[0] != row)
				end--;
			assert(end > nr);
			for (int i = nr; i < end; i++) {
				assert mColumns[end - 1].mIndices[0] == row;
				if (mColumns[i].mIndices[0] != row) {
					// move to end
					Column tc = mColumns[i];
					mColumns[i] = mColumns[--end];
					mColumns[end] = tc;
					
					Row tr = mRows[i];
					mRows[i] = mRows[end];
					mRows[end] = tr;
				}
				while (mColumns[end - 1].mIndices[0] != row)
					end--;
				assert mColumns[nr].mIndices[0] == row;
				assert mColumns[i].mIndices[0] == row;
				if (mColumns[nr].mCoeffs[0].abs().compareTo(
						mColumns[i].mCoeffs[0].abs()) > 0) {
					// move to front
					Column tc = mColumns[i];
					mColumns[i] = mColumns[nr];
					mColumns[nr] = tc;

					Row tr = mRows[i];
					mRows[i] = mRows[nr];
					mRows[nr] = tr;
				}
			}
			// make positive
			if (mColumns[nr].mCoeffs[0].signum() < 0) {
				mColumns[nr].negate();
				mRows[nr].negate();
			}
			
			// now reduce all other rows with row[nr].
			BigInteger coeffNr = mColumns[nr].mCoeffs[0];
			BigInteger coeffNr2 = coeffNr.shiftRight(1);
			for (int i = nr + 1; i < end; i++) {
				assert(mColumns[i].mIndices[0] == row);
				BigInteger coeffI = mColumns[i].mCoeffs[0];
				if (coeffI.signum() < 0) {
					coeffI = coeffI.subtract(coeffNr2);
				} else {
					coeffI = coeffI.add(coeffNr2);
				}
				BigInteger div = coeffI.divide(coeffNr);
				assert (div.signum() != 0);
				mColumns[i].addmul(mColumns[nr], div.negate());
				assert(mColumns[i].mIndices[0] != row
						|| mColumns[i].mCoeffs[0].abs().compareTo(
								coeffNr2.abs()) <= 0);
				mRows[nr].addmul(mRows[i], div);
			}
		}
		
		// make positive
		if (mColumns[nr].mCoeffs[0].signum() < 0) {
			mColumns[nr].negate();
			mRows[nr].negate();
		}
		
		// Finally reduce the rows left of this column.
		BigInteger coeffNr = mColumns[nr].mCoeffs[0];
		BigInteger coeffNrM1 = coeffNr.subtract(BigInteger.ONE);
		BigInteger coeffNr2 = coeffNr.shiftRight(1);
		BigInteger coeffNr32 = coeffNr.shiftRight(5);// NOCHECKSTYLE
		for (int i = 0; i < nr; i++) {
			int j = 0;
			while (j < mColumns[i].mIndices.length
					&& compare(mColumns[i].mIndices[j], row) < 0)
				j++;
			if (j == mColumns[i].mIndices.length
				|| mColumns[i].mIndices[j] != row)
				continue;
			assert(mColumns[i].mIndices[j] == row);
			BigInteger coeffI = mColumns[i].mCoeffs[j];
			if (mColumns[i].mIndices[0].getUpperBound()
				.equals(mColumns[i].mIndices[0].getLowerBound())) {
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
				mColumns[i].addmul(mColumns[nr], div.negate());
				mRows[nr].addmul(mRows[i], div);
			}
		}
		assert(nr + 1 == mColumns.length
				|| mColumns[nr + 1].mIndices[0] != row);
	}

	private boolean isTight(LinVar linVar) {
		return linVar.mCurval.lesseq(linVar.getLowerBound())
			|| linVar.getUpperBound().lesseq(linVar.mCurval);
	}

	private boolean[] computeTightness() {
		boolean[] tight = new boolean[mColumns.length];
		for (int i = 0; i < mColumns.length; i++)
			tight[i] = true;
		for (int i = 0; i < mColumns.length; i++) {
			if (!isTight(mColumns[i].mIndices[0]))
				tight[i] = false;
			if (!tight[i]) {
				int k = i + 1;
				for (int j = 1; j < mColumns[i].mIndices.length; j++) {
					while (k < mColumns.length 
							&& compare(mColumns[k].mIndices[0], 
									mColumns[i].mIndices[j]) < 0)
						k++;
					if (k < mColumns.length 
						&& mColumns[k].mIndices[0] == mColumns[i].mIndices[j])
						tight[k] = false;
				}
			}
		}
		return tight;
	}

	private boolean[] computeBadness() {
		boolean[] isBad = new boolean[mColumns.length];
		for (int i = 0; i < mColumns.length; i++) {
			if (mRows[i].mCurval.isIntegral()) {
				isBad[i] = true;
			} else {
				int k = i + 1;
				for (int j = 1; j < mColumns[i].mIndices.length; j++) {
					while (k < mColumns.length 
							&& compare(mColumns[k].mIndices[0], 
								mColumns[i].mIndices[j]) < 0)
						k++;
					if (k < mColumns.length 
						&& mColumns[k].mIndices[0] == mColumns[i].mIndices[j])
						isBad[k] = true;
				}
			}
		}
		return isBad;
	}

	public void generateCut(int row, boolean isTight) {
		assert mRows[row].mIndices[0].mIsInt;
		assert !mRows[row].mCurval.isIntegral();
		BoundConstraint cut = (BoundConstraint)
				mRows[row].createConstraint().getAtom();
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
		for (int i = 0; i < mColumns.length; i++)
			mgcdColumn(i);
		if (mSolver.mEngine.getLogger().isDebugEnabled()) {
			mSolver.mEngine.getLogger().debug("Cuts From Proofs");
			mSolver.mEngine.getLogger().debug("cols");
			for (int i = 0; i < mColumns.length; i++) {
				if (mColumns[i].mCoeffs.length != 1
						|| !mColumns[i].mCoeffs[0].equals(BigInteger.ONE))
					mSolver.mEngine.getLogger().debug("[" + i + "] " + mColumns[i]);
			}
			mSolver.mEngine.getLogger().debug("rows");
			for (int i = 0; i < mRows.length; i++) {
				if (!mRows[i].mCurval.isIntegral())
					mSolver.mEngine.getLogger().debug("[" + i + "] " + mRows[i]);
			}
		}
		
		boolean[] tight = computeTightness();
		boolean[] isBad = computeBadness();
		int best = -1;
		int bestlen = Integer.MAX_VALUE;
		int bestsize = Integer.MAX_VALUE;
		for (int i = 0; i < mRows.length; i++) {
			if (isBad[i])
				continue;
			/* prefer cuts over branches */
			if (!tight[i] && (best >= 0 && tight[best]))
				continue;
			/* prefer short cuts */
			if (mRows[i].mCoeffs.length > bestlen && tight[best] == tight[i])
				continue;
			/* prefer small cuts */
			int max = 0;
			for (BigInteger coeff : mRows[i].mCoeffs)
				max = Math.max(max, coeff.bitLength());
			if (max >= bestsize 
				&& mRows[i].mCoeffs.length == bestlen 
				&& tight[best] == tight[i])
				continue;
			
			best = i;
			bestsize = max;
			bestlen = mRows[i].mCoeffs.length;
		}
		if (best != -1)
			generateCut(best, tight[best]);
	}
}
