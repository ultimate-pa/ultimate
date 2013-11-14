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
			for (int i = 0 ; i < mCoeffs.length; i++)
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
				sb.append(plus).append(mIndices[i].matrixpos)
					.append(": ").append(mCoeffs[i]);
				plus = ", ";
			}
			return sb.toString();
		}
	}
	
	public class Row {
		LinVar[] indices;
		BigInteger[] coeffs;
		InfinitNumber curval;
		
		public Row(LinVar nonbasic) {
			if (nonbasic.isInitiallyBasic()) {
				Map<LinVar, BigInteger> linterm = nonbasic.getLinTerm();
				indices = new LinVar[linterm.size()];
				coeffs = new BigInteger[linterm.size()];
				int i = 0;
				for (Map.Entry<LinVar, BigInteger> entry :
					linterm.entrySet()) {
					indices[i] = entry.getKey();
					coeffs[i] = entry.getValue();
					i++;
				}
			} else {
				indices = new LinVar[] { nonbasic };
				coeffs = new BigInteger[] { BigInteger.ONE };
			}
			assert (indices.length > 0);
			curval = nonbasic.m_curval;
		}
		
		public void negate() {
			for (int i = 0 ; i < coeffs.length; i++)
				coeffs[i] = coeffs[i].negate();
			curval = curval.negate();
		}

		public void addmul(Row other, BigInteger factor) {
			LinVar[] newIndices = new LinVar[indices.length + other.indices.length];
			BigInteger[] newCoeffs = new BigInteger[newIndices.length];
			int idx = 0, oidx = 0, newidx = 0;
			while (idx < indices.length && oidx < other.indices.length) {
				if (indices[idx] == other.indices[oidx]) {
					BigInteger newcoeff = 
						coeffs[idx].add(other.coeffs[oidx].multiply(factor));
					if (newcoeff.signum() != 0) {
						newIndices[newidx] = indices[idx];
						newCoeffs[newidx] = newcoeff;
						newidx++;
					}
					idx++;
					oidx++;
				} else if (compare(indices[idx], other.indices[oidx]) < 0) {
					newIndices[newidx] = indices[idx];
					newCoeffs[newidx] = coeffs[idx];
					newidx++;
					idx++;
				} else {
					newIndices[newidx] = other.indices[oidx];
					newCoeffs[newidx] = other.coeffs[oidx].multiply(factor);
					newidx++;
					oidx++;
				}
			}
			while (idx < indices.length) {
				newIndices[newidx] = indices[idx];
				newCoeffs[newidx] = coeffs[idx];
				newidx++;
				idx++;
			}
			while (oidx < other.indices.length) {
				newIndices[newidx] = other.indices[oidx];
				newCoeffs[newidx] = other.coeffs[oidx].multiply(factor);
				newidx++;
				oidx++;
			}
			assert newidx > 0;
			if (newidx < newCoeffs.length) {
				indices = new LinVar[newidx];
				coeffs = new BigInteger[newidx];
				System.arraycopy(newIndices, 0, indices, 0, newidx);
				System.arraycopy(newCoeffs, 0, coeffs, 0, newidx);
			} else {
				indices = newIndices;
				coeffs = newCoeffs;
			}
			Rational fac = Rational.valueOf(factor, BigInteger.ONE);
			curval = curval.addmul(other.curval, fac);
		}
		
		public String getVar() {
			StringBuilder sb = new StringBuilder();
			String plus = "";
			for (int i = 0; i < indices.length; i++) {
				sb.append(plus).append(coeffs[i])
					.append(" * (").append(indices[i]).append(")");
				plus = " + ";
			}
			return sb.toString();
		}
		
		public String toString() {
			StringBuilder sb = new StringBuilder();
			sb.append(getVar());
			sb.append(" == ").append(curval);
			return sb.toString();
		}

		public Literal createConstraint() {
			MutableAffinTerm mat = new MutableAffinTerm();
			int maxlevel = 0;
			for (int i = 0; i < indices.length; i++) {
				if (maxlevel < indices[i].assertionstacklevel)
					maxlevel = indices[i].assertionstacklevel;
				mat.add(Rational.valueOf(coeffs[i], BigInteger.ONE), indices[i]);
			}
			mat.add(curval.floor().negate());
			return m_solver.generateConstraint(mat, false, maxlevel);
		}		
	}

	LinArSolve m_solver;
	Row[] m_rows;
	Column[] m_columns;
	
	private int compare(LinVar v1, LinVar v2) {
		if (v1.misint != v2.misint)
			return v1.misint ? 1 : -1;
		return v1.matrixpos - v2.matrixpos;
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
		for (LinVar lv : solver.m_linvars) {
			if (lv.mbasic)
				continue;
			boolean negated = false;
			if (lv.m_curval.lesseq(lv.getLowerBound()))
				negated = true;
			if (lv.isInitiallyBasic()) {
				for (Map.Entry<LinVar, BigInteger> entry :
					 lv.getLinTerm().entrySet()) {
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
		m_columns = new Column[colmap.size()];
		m_rows = new Row[colmap.size()];
		int i = 0;
		for (Map.Entry<LinVar, Collection<LinVarBigInt>> e : colmap.entrySet()) {
			Collection<LinVarBigInt> list = e.getValue();
			LinVar[] indices = new LinVar[list.size()];
			BigInteger[] coeffs = new BigInteger[list.size()];
			int j = 0;
			for (LinVarBigInt ib : list) {
				indices[j] = ib.mRow;
				coeffs[j] = ib.mCoeff;
				assert (j == 0 || compare(indices[j-1], indices[j]) < 0);
				j++;
			}
			m_columns[i] = new Column(indices, coeffs);
			m_rows[i] = new Row(e.getKey());
			i++;
		}
	}
	
	private void mgcdColumn(int nr) {
		/* find row to work on. */
		LinVar row = m_columns[nr].mIndices[0];
		for (int i = nr+1; i < m_columns.length; i++) {
			if (compare(m_columns[i].mIndices[0], row) < 0)
				row = m_columns[i].mIndices[0];
		}
		
		/* reorder columns: put zero columns at end,
		 * put column with smallest absolute coeff at front.
		 */
		int end = m_columns.length;
		while (end > nr + 1) {
			while (m_columns[end-1].mIndices[0] != row)
				end--;
			assert(end > nr);
			for (int i = nr; i < end; i++) {
				assert m_columns[end-1].mIndices[0] == row;
				if (m_columns[i].mIndices[0] != row) {
					// move to end
					Column tc = m_columns[i];
					m_columns[i] = m_columns[--end];
					m_columns[end] = tc;
					
					Row tr = m_rows[i];
					m_rows[i] = m_rows[end];
					m_rows[end] = tr;
				}
				while (m_columns[end-1].mIndices[0] != row)
					end--;
				assert m_columns[nr].mIndices[0] == row;
				assert m_columns[i].mIndices[0] == row;
				if (m_columns[nr].mCoeffs[0].abs().compareTo(m_columns[i].mCoeffs[0].abs()) > 0) {
					// move to front
					Column tc = m_columns[i];
					m_columns[i] = m_columns[nr];
					m_columns[nr] = tc;

					Row tr = m_rows[i];
					m_rows[i] = m_rows[nr];
					m_rows[nr] = tr;
				}
			}
			// make positive
			if (m_columns[nr].mCoeffs[0].signum() < 0) {
				m_columns[nr].negate();
				m_rows[nr].negate();
			}
			
			// now reduce all other rows with row[nr].
			BigInteger coeffNr = m_columns[nr].mCoeffs[0];
			BigInteger coeffNr2 = coeffNr.shiftRight(1);
			for (int i = nr+1; i < end; i++) {
				assert(m_columns[i].mIndices[0] == row);
				BigInteger coeffI = m_columns[i].mCoeffs[0];
				if (coeffI.signum() < 0) {
					coeffI = coeffI.subtract(coeffNr2);
				} else {
					coeffI = coeffI.add(coeffNr2);
				}
				BigInteger div = coeffI.divide(coeffNr);
				assert (div.signum() != 0);
				m_columns[i].addmul(m_columns[nr], div.negate());
				assert(m_columns[i].mIndices[0] != row
					   || m_columns[i].mCoeffs[0].abs().compareTo(coeffNr2.abs())<=0);
				m_rows[nr].addmul(m_rows[i], div);
			}
		}
		
		// Finally reduce the rows left of this column.
		BigInteger coeffNr = m_columns[nr].mCoeffs[0];
		BigInteger coeffNrM1 = coeffNr.subtract(BigInteger.ONE);
		BigInteger coeffNr2 = coeffNr.shiftRight(1);
		BigInteger coeffNr32 = coeffNr.shiftRight(5);
		for (int i = 0; i < nr; i++) {
			int j = 0;
			while (j < m_columns[i].mIndices.length
					&& compare(m_columns[i].mIndices[j], row) < 0)
				j++;
			if (j == m_columns[i].mIndices.length
				|| m_columns[i].mIndices[j] != row)
				continue;
			assert(m_columns[i].mIndices[j] == row);
			BigInteger coeffI = m_columns[i].mCoeffs[j];
			if (m_columns[i].mIndices[0].getUpperBound()
				.equals(m_columns[i].mIndices[0].getLowerBound())) {
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
				m_columns[i].addmul(m_columns[nr], div.negate());
				m_rows[nr].addmul(m_rows[i], div);
			}
		}
		assert(nr+1 == m_columns.length || m_columns[nr+1].mIndices[0] != row);
	}

	private boolean isTight(LinVar linVar) {
		return linVar.m_curval.lesseq(linVar.getLowerBound())
			|| linVar.getUpperBound().lesseq(linVar.m_curval);
	}

	private boolean[] computeTightness() {
		boolean[] tight = new boolean[m_columns.length];
		for (int i = 0; i < m_columns.length; i++)
			tight[i] = true;
		for (int i = 0; i < m_columns.length; i++) {
			if (!isTight(m_columns[i].mIndices[0]))
				tight[i] = false;
			if (!tight[i]) {
				int k = i+1;
				for (int j = 1; j < m_columns[i].mIndices.length; j++) {
					while (k < m_columns.length 
							&& compare(m_columns[k].mIndices[0], 
									m_columns[i].mIndices[j]) < 0)
						k++;
					if (k < m_columns.length 
						&& m_columns[k].mIndices[0] == m_columns[i].mIndices[j])
						tight[k] = false;
				}
			}
		}
		return tight;
	}

	private boolean[] computeBadness() {
		boolean[] isBad = new boolean[m_columns.length];
		for (int i = 0; i < m_columns.length; i++) {
			if (m_rows[i].curval.isIntegral()) {
				isBad[i] = true;
			} else {
				int k = i+1;
				for (int j = 1; j < m_columns[i].mIndices.length; j++) {
					while (k < m_columns.length 
							&& compare(m_columns[k].mIndices[0], 
								m_columns[i].mIndices[j]) < 0)
						k++;
					if (k < m_columns.length 
						&& m_columns[k].mIndices[0] == m_columns[i].mIndices[j])
						isBad[k] = true;
				}
			}
		}
		return isBad;
	}

	public void generateCut(int row, boolean isTight) {
		assert m_rows[row].indices[0].misint;
		assert !m_rows[row].curval.isIntegral();
		BoundConstraint cut = (BoundConstraint) m_rows[row].createConstraint().getAtom();
		LinVar cutVar = cut.getVar();
		if (cutVar.m_curval.less(cutVar.getLowerBound())) {
//			m_solver.mengine.getLogger().debug("cut: " + cut.negate());
			m_solver.moob.add(cutVar);
			m_solver.mproplist.add(cut.negate());
			m_solver.numCuts++;
		} else if (cutVar.getUpperBound().less(cutVar.m_curval)) {
//			m_solver.mengine.getLogger().debug("cut: " + cut);
			m_solver.moob.add(cutVar);
			m_solver.mproplist.add(cut);
			m_solver.numCuts++;
		} else {
			m_solver.mengine.getLogger().debug("branch on "+cut);
			assert(!m_solver.moob.isEmpty() || cut.getAtom().getDecideStatus() == null);
			m_solver.m_suggestions.add(cut);
			m_solver.numBranches++;
		}
	}

	public CutCreator(LinArSolve solver) {
		m_solver = solver;
		solver.calculateSimpVals();
		computeMatrix(solver);
	}
	
	public void generateCuts() {
		for (int i = 0; i < m_columns.length; i++)
			mgcdColumn(i);
		if (m_solver.mengine.getLogger().isDebugEnabled()) {
			m_solver.mengine.getLogger().debug("Cuts From Proofs");
			m_solver.mengine.getLogger().debug("cols");
			for (int i = 0; i < m_columns.length; i++) {
				if (m_columns[i].mCoeffs.length != 1
						|| !m_columns[i].mCoeffs[0].equals(BigInteger.ONE))
					m_solver.mengine.getLogger().debug("["+i+"] "+m_columns[i]);
			}
			m_solver.mengine.getLogger().debug("rows");
			for (int i = 0; i < m_rows.length; i++) {
				if (!m_rows[i].curval.isIntegral())
					m_solver.mengine.getLogger().debug("["+i+"] "+m_rows[i]);
			}
		}
		
		boolean[] tight = computeTightness();
		boolean[] isBad = computeBadness();
		int best = -1;
		int bestlen = Integer.MAX_VALUE;
		int bestsize = Integer.MAX_VALUE;
		for (int i = 0; i < m_rows.length; i++) {
			if (isBad[i])
				continue;
			/* prefer cuts over branches */
			if (!tight[i] && (best >= 0 && tight[best]))
				continue;
			/* prefer short cuts */
			if (m_rows[i].coeffs.length > bestlen && tight[best] == tight[i])
				continue;
			/* prefer small cuts */
			int max = 0;
			for (BigInteger coeff : m_rows[i].coeffs)
				max = Math.max(max, coeff.bitLength());
			if (max >= bestsize 
				&& m_rows[i].coeffs.length == bestlen 
				&& tight[best] == tight[i])
				continue;
			
			best = i;
			bestsize = max;
			bestlen = m_rows[i].coeffs.length;
		}
		if (best != -1)
			generateCut(best, tight[best]);
	}
}
