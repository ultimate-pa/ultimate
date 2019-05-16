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
 * This represents an entry in our sparse matrix. The entries are doubly linked 2d-shaped list, i.e. each entry knows
 * its row and its column predecessor.
 *
 * The overall matrix consists of rows of the form:
 *
 * <pre>
 * {@code
 *   b_i * y_i + a_i1 * x_1 + ... + a_in * x_n
 * }
 * </pre>
 * 
 * where {@code b_i}, and {@code a_ij} are big integers, {@code y_i} is the row variable for this row and
 * {@code x_1,...,x_n} are column variables. To be valid, the row should sum up to 0, if the linear variables are
 * replaced by their LinTerms. Also the gcd of the coefficients should be 1.
 * 
 * <p>
 * For each summand a matrix entry is created, whose field {@code mRow} points to {@code y_i} and {@code mColumn} points
 * to the respective y_i or x_i variable occuring in this summand. I.e. for the first entry both {@code mRow} and
 * {@code mColumn} point to y_i. The {@code mCoeff} field is the big integer b_i or a_ij. The {@code mPrevInRow} and
 * {@code mNextInRow} are iterating through the row. The variables {@code x_i, y_i} are sorted by their index so the y_i
 * term may appear in between the x_i according to the variable order.
 * 
 * <p>
 * The {@code mPrevInCol} and {@code mNextInCol} fields link the columns corresponding to the same column variable x_i.
 * They can be in any order and the order is not consistent between different columns. There is a special head entry for
 * each column variable with {@code mNextInRow == null}. The head entry for column variables points to this special
 * entry. The head entry for row variables points to the entry representing {@code b_i*y_i}.
 * 
 * <p>
 * TODO: Evaluate if a singly linked list is enough, at least for the column lists. Maybe a mix between linked list and
 * tree may be faster if rows grow big, but pivoted rows are small.
 * 
 * @author Jochen Hoenicke
 */
public class MatrixEntry {
	BigInteger mCoeff;
	LinVar     mRow;
	LinVar     mColumn;
	
	MatrixEntry mPrevInRow;
	MatrixEntry mNextInRow;
	MatrixEntry mPrevInCol;
	MatrixEntry mNextInCol;
	
	/**
	 * Insert a column variable into a row at its sorted position.
	 * @param nb  the column (non-basic) variable.
	 * @param value the coefficient in the matrix.
	 */
	public void insertRow(LinVar nb, BigInteger value) {
		assert mRow.mHeadEntry == this;
		assert mRow == mColumn;
		assert nb != mRow;
		assert(!value.equals(BigInteger.ZERO));
		MatrixEntry ptr = mNextInRow;
		final int poscmp = Integer.MAX_VALUE - mColumn.mMatrixpos;
		while (ptr.mColumn.mMatrixpos + poscmp < nb.mMatrixpos + poscmp) {
			ptr = ptr.mNextInRow;
		}
		if (ptr.mColumn == nb) {
			assert ptr != this;
			/* Add to existing entry */
			ptr.mCoeff = ptr.mCoeff.add(value);
			if (ptr.mCoeff.equals(BigInteger.ZERO)) {
				ptr.removeFromMatrix();
			}
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
		final MatrixEntry newEntry = new MatrixEntry();
		newEntry.mColumn = col;
		newEntry.mRow = mRow;
		newEntry.mCoeff = value;
		newEntry.mNextInRow = this;
		newEntry.mPrevInRow = mPrevInRow;
		newEntry.mNextInCol = col.mHeadEntry.mNextInCol;
		newEntry.mPrevInCol = col.mHeadEntry;
		mPrevInRow.mNextInRow = newEntry;
		mPrevInRow = newEntry;
		col.mHeadEntry.mNextInCol.mPrevInCol = newEntry;
		col.mHeadEntry.mNextInCol = newEntry;
		mRow.mChainlength++;
		col.mChainlength++;
	}

	public void removeFromRow() {
		mPrevInRow.mNextInRow = mNextInRow;
		mNextInRow.mPrevInRow = mPrevInRow;
		mRow.mChainlength--;
	}

	public void removeFromColumn() {
		mPrevInCol.mNextInCol = mNextInCol;
		mNextInCol.mPrevInCol = mPrevInCol;
//		column.chainlength--;
	}

	public void removeFromMatrix() {
		mPrevInRow.mNextInRow = mNextInRow;
		mNextInRow.mPrevInRow = mPrevInRow;
		mPrevInCol.mNextInCol = mNextInCol;
		mNextInCol.mPrevInCol = mPrevInCol;
		mRow.mChainlength--;
		mColumn.mChainlength--;
	}

	/**
	 * Adds two rows together eliminating a column variable.  When calling
	 * this, this.column == other.column must hold.  The current row is 
	 * multiplied with other.coeff and then this.coeff times the other row
	 * is subtracted.  On return this is removed from the matrix.
	 * @param other  The other row to add to this row.
	 */
	public void add(MatrixEntry other) {
		assert (mColumn == other.mColumn);
		BigInteger gcd = Rational.gcd(mCoeff, other.mCoeff);
		BigInteger tmul = other.mCoeff.divide(gcd);
		BigInteger omul = mCoeff.divide(gcd);
		// make sure we multiply this by a positive number.
		if (tmul.signum() < 0) {
			tmul = tmul.negate();
		} else {
			omul = omul.negate();
		}
		assert(mCoeff.multiply(tmul).add(
				other.mCoeff.multiply(omul)).signum() == 0);
		mRow.mulUpperLower(Rational.valueOf(tmul, BigInteger.ONE));

		// add this to matrixpos to reorder columns, such that this
		// column is the largest.
		final int poscmp = Integer.MAX_VALUE - mColumn.mMatrixpos;
		
		MatrixEntry trow = mNextInRow;
		MatrixEntry orow = other.mNextInRow;
		gcd = BigInteger.ZERO;
		while (orow != other) {
			while (trow.mColumn.mMatrixpos + poscmp 
					< orow.mColumn.mMatrixpos + poscmp) {
				trow.mCoeff = trow.mCoeff.multiply(tmul);
				gcd = Rational.gcd(gcd, trow.mCoeff);
				trow = trow.mNextInRow;
			}
			final BigInteger ocoeff = orow.mCoeff.multiply(omul);
			assert(!ocoeff.equals(BigInteger.ZERO));
			if (trow.mColumn == orow.mColumn) {
				final BigInteger oldval = trow.mCoeff.multiply(tmul);
				trow.mCoeff = oldval.add(ocoeff);
				mRow.updateUpperLowerClear(oldval, trow.mColumn);
				if (trow.mCoeff.equals(BigInteger.ZERO)) {
					trow.removeFromMatrix();
				} else {
					gcd = Rational.gcd(gcd, trow.mCoeff);
					mRow.updateUpperLowerSet(trow.mCoeff, trow.mColumn);
				}
				trow = trow.mNextInRow;
			} else {
				gcd = Rational.gcd(gcd, ocoeff);
				trow.insertBefore(orow.mColumn, ocoeff);
				mRow.updateUpperLowerSet(ocoeff, orow.mColumn);
			}
			orow = orow.mNextInRow;
		}
		while (trow != this) {
			trow.mCoeff = trow.mCoeff.multiply(tmul);
			gcd = Rational.gcd(gcd, trow.mCoeff);
			trow = trow.mNextInRow;
		}
		mRow.updateUpperLowerClear(mCoeff.multiply(tmul), trow.mColumn);

		gcd = gcd.abs();
		if (!gcd.equals(BigInteger.ONE)) {
			for (trow = mNextInRow; trow != this; trow = trow.mNextInRow) {
				assert trow.mCoeff.remainder(gcd).equals(BigInteger.ZERO);
				trow.mCoeff = trow.mCoeff.divide(gcd);
			}
			mRow.mulUpperLower(Rational.valueOf(BigInteger.ONE, gcd));
		}
		/* Finally remove this entry */
		removeFromMatrix();
		mColumn.mChainlength++;
	}
	
	/**
	 * Do the first half of the pivoting operation that swaps a column and row variable. The row and column variables
	 * are given by this entry, which must not be a head entry for any variable. This will adjust the head entries
	 * accordingly, but the other rows will still mention the old column variable. These rows will still be linked to
	 * this entry, so they can be easily identified.
	 * 
	 */
	public void pivot() {
		// unlink column head entry
		mColumn.mHeadEntry.removeFromColumn();
		// Now mRow head entry becomes a normal entry and mColumn.mHeadEntry will be the new mRow.mHeadEntry.
		// We initially have only
		mColumn.mHeadEntry.mNextInCol = mColumn.mHeadEntry.mPrevInCol = mRow.mHeadEntry;
		mRow.mHeadEntry.mNextInCol = mRow.mHeadEntry.mPrevInCol = mColumn.mHeadEntry;
		mRow.mHeadEntry = mColumn.mHeadEntry;
		mRow.mHeadEntry.mColumn = mRow;
		// this entry becomes the new mColumn head entry, which is now a row variable.
		mColumn.mHeadEntry = this;
		
		mColumn.mChainlength = mRow.mChainlength;
		mRow.mChainlength = 1;

		// update the mRow variables for all variables in this row.
		MatrixEntry entry = this;
		do {
			entry.mRow = mColumn;
			entry = entry.mNextInRow;
		} while (entry != this);
	}

	public String rowToString() {
		final StringBuilder sb = new StringBuilder("[");
		sb.append(mCoeff).append("*(").append(mColumn).append(')');
		for (MatrixEntry ptr = mNextInRow; 
			ptr != this; ptr = ptr.mNextInRow) {
			sb.append('+');
			sb.append(ptr.mCoeff).append("*(").append(ptr.mColumn).append(')');
		}
		return sb.append("=0]").toString();
	}
	
	public String colToString() {
		final StringBuilder sb = new StringBuilder("[");
		String comma = "";
		for (MatrixEntry ptr = mNextInCol; 
			ptr != this; ptr = ptr.mNextInCol) {
			sb.append(comma);
			sb.append('(').append(ptr.mRow).append(")->").append(ptr.mCoeff);
			comma = ",";
		}
		return sb.append(']').toString();
	}
	
	@Override
	public String toString() {
		if (mNextInRow == null) {
			return mColumn + ":" + colToString();
		}
		if (mRow == mColumn) {
			return rowToString();
		}
		return "[" + mRow + "/" + mColumn + "]->" + mCoeff;
	}
}
