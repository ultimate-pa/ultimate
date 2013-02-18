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

import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * This represents an entry in our sparse matrix.  The entries
 * are doubly linked 2d-shaped list, i.e. each entry knows its
 * row and its column predecessor.  The row lists are sorted, 
 * the column lists are randomly ordered and not consistently 
 * ordered with respect to other column lists.
 * 
 * TODO: Evaluate if a singly linked list is enough, at least 
 * for the column lists.
 * TODO: Maybe a mix between linked list and tree may be
 * faster if rows grow big, but pivoted rows are small.
 * 
 * @author Jochen Hoenicke
 */
public class MatrixEntry {
	BigInteger coeff;
	LinVar     row;
	LinVar     column;
	
	MatrixEntry prevInRow;
	MatrixEntry nextInRow;
	MatrixEntry prevInCol;
	MatrixEntry nextInCol;
	
	/**
	 * Insert a column variable into a row at its sorted position.
	 * @param nb  the column (non-basic) variable.
	 * @param value the coefficient in the matrix.
	 */
	public void insertRow(LinVar nb, BigInteger value) {
		assert this.row.headEntry == this;
		assert this.row == this.column;
		assert nb != this.row;
		assert(!value.equals(Rational.ZERO));
		MatrixEntry ptr = this.nextInRow;
		int poscmp = Integer.MAX_VALUE - this.column.matrixpos;
		while (ptr.column.matrixpos + poscmp < nb.matrixpos + poscmp)
			ptr = ptr.nextInRow;
		if (ptr.column == nb) {
			assert ptr != this;
			/* Add to existing entry */
			ptr.coeff = ptr.coeff.add(value);
			if (ptr.coeff.equals(Rational.ZERO))
				ptr.removeFromMatrix();
		} else {
			ptr.insertBefore(nb, value);
		}
	}
	
	/**
	 * Insert a column variable into a row before the current
	 * position.
	 * @param nb  the column (non-basic) variable.
	 * @param value the coefficient in the matrix.
	 */
	public void insertBefore(LinVar col, BigInteger value) {
		assert !value.equals(BigInteger.ZERO);
		
		/* Create new entry before this */
		MatrixEntry newEntry = new MatrixEntry();
		newEntry.column = col;
		newEntry.row = this.row;
		newEntry.coeff = value;
		newEntry.nextInRow = this;
		newEntry.prevInRow = this.prevInRow;
		newEntry.nextInCol = col.headEntry.nextInCol;
		newEntry.prevInCol = col.headEntry;
		this.prevInRow.nextInRow = newEntry;
		this.prevInRow = newEntry;
		col.headEntry.nextInCol.prevInCol = newEntry;
		col.headEntry.nextInCol = newEntry;
		row.chainlength++;
		col.chainlength++;
	}

	public void removeFromRow() {
		prevInRow.nextInRow = nextInRow;
		nextInRow.prevInRow = prevInRow;
		row.chainlength--;
	}

	public void removeFromColumn() {
		prevInCol.nextInCol = nextInCol;
		nextInCol.prevInCol = prevInCol;
//		column.chainlength--;
	}

	public void removeFromMatrix() {
		prevInRow.nextInRow = nextInRow;
		nextInRow.prevInRow = prevInRow;
		prevInCol.nextInCol = nextInCol;
		nextInCol.prevInCol = prevInCol;
		row.chainlength--;
		column.chainlength--;
	}

	/**
	 * Adds two rows together eliminating a column variable.  When calling
	 * this, this.column == other.column must hold.  The current row is 
	 * multiplied with other.coeff and then this.coeff times the other row
	 * is subtracted.  On return this is removed from the matrix.
	 * @param other  The other row to add to this row.
	 */
	public void add(MatrixEntry other) {
		assert (this.column == other.column);
		BigInteger gcd = Rational.gcd(this.coeff, other.coeff);
		BigInteger tmul = other.coeff.divide(gcd);
		BigInteger omul = this.coeff.divide(gcd);
		// make sure we multiply this by a positive number.
		if (tmul.signum() < 0) {
			tmul = tmul.negate();
		} else {
			omul = omul.negate();
		}
		assert(this.coeff.multiply(tmul).add(other.coeff.multiply(omul)).signum() == 0);
		this.row.mulUpperLower(Rational.valueOf(tmul, BigInteger.ONE));

		// add this to matrixpos to reorder columns, such that this
		// column is the largest.
		int poscmp = Integer.MAX_VALUE - this.column.matrixpos;
		
		MatrixEntry trow = nextInRow;
		MatrixEntry orow = other.nextInRow;
		gcd = BigInteger.ZERO;
		while (orow != other) {
			while (trow.column.matrixpos + poscmp 
					< orow.column.matrixpos + poscmp) {
				trow.coeff = trow.coeff.multiply(tmul);
				gcd = Rational.gcd(gcd, trow.coeff);
				trow = trow.nextInRow;
			}
			BigInteger ocoeff = orow.coeff.multiply(omul);
			assert(!ocoeff.equals(Rational.ZERO));
			if (trow.column == orow.column) {
				BigInteger oldval = trow.coeff.multiply(tmul);
				trow.coeff = oldval.add(ocoeff);
				row.updateUpperLowerClear(oldval, trow.column);
				if (trow.coeff.equals(BigInteger.ZERO)) {
					trow.removeFromMatrix();
				} else {
					gcd = Rational.gcd(gcd, trow.coeff);
					row.updateUpperLowerSet(trow.coeff, trow.column);
				}
				trow = trow.nextInRow;
			} else {
				gcd = Rational.gcd(gcd, ocoeff);
				trow.insertBefore(orow.column, ocoeff);
				row.updateUpperLowerSet(ocoeff, orow.column);
			}
			orow = orow.nextInRow;
		}
		while (trow != this) {
			trow.coeff = trow.coeff.multiply(tmul);
			gcd = Rational.gcd(gcd, trow.coeff);
			trow = trow.nextInRow;
		}
		row.updateUpperLowerClear(coeff.multiply(tmul), trow.column);

		gcd = gcd.abs();
		if (!gcd.equals(BigInteger.ONE)) {
			for (trow = this.nextInRow; trow != this; trow = trow.nextInRow) {
				assert trow.coeff.remainder(gcd).equals(BigInteger.ZERO);
				trow.coeff = trow.coeff.divide(gcd);
			}
			this.row.mulUpperLower(Rational.valueOf(BigInteger.ONE, gcd));
		}
		/* Finally remove this entry */
		this.removeFromMatrix();
		column.chainlength++;
	}
	
	public void pivot() {
		column.headEntry.removeFromColumn();
		column.headEntry.nextInCol = column.headEntry.prevInCol = row.headEntry;
		row.headEntry.nextInCol = row.headEntry.prevInCol = column.headEntry;
		row.headEntry = column.headEntry;
		row.headEntry.column = row;
		column.headEntry = this;
		
		column.chainlength = row.chainlength;
		row.chainlength = 1;
		
		MatrixEntry entry = this;
		do {
			entry.row = column;
			entry = entry.nextInRow;
		} while (entry != this);
				
	}

	public String rowToString() {
		StringBuilder sb = new StringBuilder("[");
		sb.append(coeff).append("*(").append(column).append(")");
		for (MatrixEntry ptr = nextInRow; 
			ptr != this; ptr = ptr.nextInRow) {
			sb.append("+");
			sb.append(ptr.coeff).append("*(").append(ptr.column).append(")");
		}
		return sb.append("=0]").toString();
	}
	
	public String colToString() {
		StringBuilder sb = new StringBuilder("[");
		String comma = "";
		for (MatrixEntry ptr = nextInCol; 
			ptr != this; ptr = ptr.nextInCol) {
			sb.append(comma);
			sb.append("(").append(ptr.row).append(")->").append(ptr.coeff);
			comma = ",";
		}
		return sb.append("]").toString();
	}
	
	public String toString() {
		if (nextInRow == null)
			return column+":"+colToString();
		if (row == column)
			return rowToString();
		return "["+row+"/"+column+"]->"+coeff;
	}
}
