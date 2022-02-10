package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Map;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * Data structure that stores a row of the linear arithmetic tableaux. For every row variable {@code y} there is a
 * tableaux row that encodes a linear relation {@code c0*y + c1*x1 + ... + cn*xn == 0}, where {@code x1...xn} are the
 * current column variables and the coefficients {@code ci} are all integers.
 *
 * @author Jochen Hoenicke
 */
public class TableauxRow {
	final static int LIMIT_BITS = 30;
	final static int LIMIT = 1 << LIMIT_BITS;
	final static int MARKER = LIMIT + 1;

	/**
	 * The entries are stored in a single integer array in the form {@code x0 c0 x1 c1 x2 c2 ...} where {@code xi} is
	 * the matrixpos of the i-th variable and {@code ci} the i-th coefficient ({@code x0} is the matrix pos of the row
	 * variable and {@code c0} is its coefficient). If the coefficient is big (doesn't fit in 31 bits), {@code ci} is
	 * stored as {@code MARKER + j} where j is the index into the {@code mBigEntries} array. The xi are sorted by matrix
	 * position, except that the row variable comes first.
	 */
	private int[] mEntries;
	/**
	 * This array stores all big coefficients that don't fit in 31 bits. The order is random and it may contain
	 * duplicates.
	 */
	private BigInteger[] mBigEntries;

	/**
	 * Create a tableaux row for the given coefficients. It first brings the coefficients to integer by dividing by the
	 * gcd of all coefficients.
	 *
	 * @param coeffs
	 *            The rational coefficients for the column variables.
	 */
	public TableauxRow(final LinVar rowVar, final SortedMap<LinVar, Rational> coeffs) {
		assert !coeffs.containsKey(rowVar);
		assert coeffs.size() >= 2;
		mEntries = new int[coeffs.size() * 2 + 2];
		Rational gcd = Rational.ONE;
		for (final Rational c : coeffs.values()) {
			gcd = gcd.gcd(c);
		}
		final ArrayList<BigInteger> bigInts = new ArrayList<>();
		mEntries[0] = rowVar.mMatrixpos;
		mEntries[1] = addBigInteger(bigInts, gcd.inverse().negate().numerator());
		int i = 2;
		for (final Map.Entry<LinVar, Rational> entry : coeffs.entrySet()) {
			assert entry.getValue().div(gcd).isIntegral();
			final BigInteger coeff = entry.getValue().div(gcd).numerator();
			mEntries[i] = entry.getKey().mMatrixpos;
			mEntries[i + 1] = addBigInteger(bigInts, coeff);
			i += 2;
		}
		if (bigInts.size() > 0) {
			mBigEntries = bigInts.toArray(new BigInteger[bigInts.size()]);
		}
	}

	private static int addBigInteger(final ArrayList<BigInteger> bigInts, final long coeff) {
		if (coeff >= -LIMIT && coeff < LIMIT) {
			return (int) coeff;
		} else {
			bigInts.add(BigInteger.valueOf(coeff));
			return MARKER + bigInts.size() - 1;
		}
	}

	private static int addBigInteger(final ArrayList<BigInteger> bigInts, final BigInteger coeff) {
		if (coeff.bitLength() <= LIMIT_BITS) {
			return coeff.intValue();
		} else {
			bigInts.add(coeff);
			return MARKER + bigInts.size() - 1;
		}
	}

	public int findRawIndex(final int matrixPos) {
		int low = 1;
		int high = size();
		while (low < high) {
			final int mid = (low + high) / 2;
			if (mEntries[2 * mid] < matrixPos) {
				low = mid + 1;
			} else {
				high = mid;
			}
		}
		return low;
	}

	private int findEntry(final int matrixPos) {
		final int idx = findRawIndex(matrixPos);
		return mEntries[2 * idx] == matrixPos ? mEntries[2 * idx + 1] : 0;
	}

	private BigInteger bigEntry(final int entry) {
		return entry < MARKER ? BigInteger.valueOf(entry) : mBigEntries[entry - MARKER];
	}

	private void addRowInt(final LinArSolve solver, final TableauxRow other) {
		final int matrixPos = other.mEntries[0];
		assert mBigEntries == null && other.mBigEntries == null;
		int myFactor = -other.mEntries[1];
		int otherFactor = findEntry(matrixPos);
		assert otherFactor != 0;
		final int gcdFactor = Rational.gcd(myFactor, otherFactor);
		myFactor = myFactor / gcdFactor;
		otherFactor = otherFactor / gcdFactor;

		final int[] newVars = new int[mEntries.length / 2 + other.mEntries.length / 2];
		final long[] newCoeffs = new long[mEntries.length / 2 + other.mEntries.length / 2];
		int myIndex = 2;
		int otherIndex = 2;
		int newIndex = 1;
		newVars[0] = mEntries[0];
		newCoeffs[0] = (long) mEntries[1] * myFactor;
		long gcd = newCoeffs[0];
		while (myIndex < mEntries.length || otherIndex < other.mEntries.length) {
			if (otherIndex == other.mEntries.length
					|| (myIndex < mEntries.length && mEntries[myIndex] < other.mEntries[otherIndex])) {
				if (mEntries[myIndex] != matrixPos) {
					newVars[newIndex] = mEntries[myIndex];
					final long newCoeff = (long) mEntries[myIndex + 1] * myFactor;
					gcd = Rational.gcd(gcd, newCoeff);
					newCoeffs[newIndex] = newCoeff;
					newIndex++;
				}
				myIndex += 2;
			} else if (myIndex == mEntries.length || mEntries[myIndex] > other.mEntries[otherIndex]) {
				solver.mDependentRows.get(other.mEntries[otherIndex]).set(mEntries[0]);
				newVars[newIndex] = other.mEntries[otherIndex];
				final long newCoeff = (long) other.mEntries[otherIndex + 1] * otherFactor;
				gcd = Rational.gcd(gcd, newCoeff);
				newCoeffs[newIndex] = newCoeff;
				otherIndex += 2;
				newIndex++;
			} else {
				assert mEntries[myIndex] == other.mEntries[otherIndex];
				final long newCoeff =
						(long) mEntries[myIndex + 1] * myFactor + (long) other.mEntries[otherIndex + 1] * otherFactor;
				if (newCoeff != 0) {
					newVars[newIndex] = mEntries[myIndex];
					gcd = Rational.gcd(gcd, newCoeff);
					newCoeffs[newIndex] = newCoeff;
					newIndex++;
				} else {
					solver.mDependentRows.get(mEntries[myIndex]).clear(mEntries[0]);
				}
				myIndex += 2;
				otherIndex += 2;
			}
		}
		final int[] result = new int[2 * newIndex];
		final ArrayList<BigInteger> bigInts = new ArrayList<>();
		for (int i = 0; i < newIndex; i++) {
			result[2 * i] = newVars[i];
			result[2 * i + 1] = addBigInteger(bigInts, newCoeffs[i] / gcd);
			assert result[2 * i + 1] >= -LIMIT && result[2 * i + 1] < MARKER + bigInts.size();
		}
		mEntries = result;
		if (bigInts.size() > 0) {
			mBigEntries = bigInts.toArray(new BigInteger[bigInts.size()]);
		}
	}

	private void addRowBigInt(final LinArSolve solver, final TableauxRow other) {
		final int matrixPos = other.mEntries[0];
		BigInteger myFactor = other.bigEntry(other.mEntries[1]).negate();
		BigInteger otherFactor = bigEntry(findEntry(matrixPos));
		assert otherFactor.signum() != 0;
		final BigInteger gcdFactor = Rational.gcd(myFactor, otherFactor);
		myFactor = myFactor.divide(gcdFactor);
		otherFactor = otherFactor.divide(gcdFactor);

		final int[] newVars = new int[mEntries.length / 2 + other.mEntries.length / 2];
		final BigInteger[] newCoeffs = new BigInteger[mEntries.length / 2 + other.mEntries.length / 2];
		int myIndex = 2;
		int otherIndex = 2;
		int newIndex = 1;
		newVars[0] = mEntries[0];
		newCoeffs[0] = bigEntry(mEntries[1]).multiply(myFactor);
		BigInteger gcd = newCoeffs[0];
		while (myIndex < mEntries.length || otherIndex < other.mEntries.length) {
			if (otherIndex == other.mEntries.length
					|| (myIndex < mEntries.length && mEntries[myIndex] < other.mEntries[otherIndex])) {
				if (mEntries[myIndex] != matrixPos) {
					newVars[newIndex] = mEntries[myIndex];
					final BigInteger newCoeff = bigEntry(mEntries[myIndex + 1]).multiply(myFactor);
					gcd = Rational.gcd(gcd, newCoeff);
					newCoeffs[newIndex] = newCoeff;
					newIndex++;
				}
				myIndex += 2;
			} else if (myIndex == mEntries.length || mEntries[myIndex] > other.mEntries[otherIndex]) {
				solver.mDependentRows.get(other.mEntries[otherIndex]).set(mEntries[0]);
				newVars[newIndex] = other.mEntries[otherIndex];
				final BigInteger newCoeff = other.bigEntry(other.mEntries[otherIndex + 1]).multiply(otherFactor);
				gcd = Rational.gcd(gcd, newCoeff);
				newCoeffs[newIndex] = newCoeff;
				otherIndex += 2;
				newIndex++;
			} else {
				assert mEntries[myIndex] == other.mEntries[otherIndex];
				final BigInteger newCoeff =
						bigEntry(mEntries[myIndex + 1]).multiply(myFactor).add(
								other.bigEntry(other.mEntries[otherIndex + 1]).multiply(otherFactor));
				if (newCoeff.signum() != 0) {
					newVars[newIndex] = mEntries[myIndex];
					gcd = Rational.gcd(gcd, newCoeff);
					newCoeffs[newIndex] = newCoeff;
					newIndex++;
				} else {
					solver.mDependentRows.get(mEntries[myIndex]).clear(mEntries[0]);
				}
				myIndex += 2;
				otherIndex += 2;
			}
		}
		final int[] result = new int[2 * newIndex];
		final ArrayList<BigInteger> bigInts = new ArrayList<>();
		for (int i = 0; i < newIndex; i++) {
			result[2 * i] = newVars[i];
			final BigInteger newCoeff = newCoeffs[i].divide(gcd);
			result[2 * i + 1] = addBigInteger(bigInts, newCoeff);
			assert result[2 * i + 1] >= -LIMIT && result[2 * i + 1] < MARKER + bigInts.size();
		}
		mEntries = result;
		if (bigInts.size() > 0) {
			mBigEntries = bigInts.toArray(new BigInteger[bigInts.size()]);
		} else {
			mBigEntries = null;
		}
	}

	/**
	 * Fixup the tableaux row after some column variable changed to a row variable. The other tableaux row corresponds
	 * to the old column variable and it is added to the current row multiplied with the coefficient the previous column
	 * variable had in this row. This method may only be called if the old column variable appeared in this tableaux
	 * row.
	 *
	 * @param other
	 *            The row describing the value of the previous column variable in terms of the new column variables.
	 * @param matrixPos
	 *            The matrix position of the previous column variable.
	 */
	public void addRow(final LinArSolve solver, final TableauxRow other) {
		if (mBigEntries == null && other.mBigEntries == null) {
			addRowInt(solver, other);
		} else {
			addRowBigInt(solver, other);
		}
	}

	/**
	 * Fixup the tableaux row after we swap the previous row variable with some column variable. The old column variable
	 * gets the new row variable andd the previous row variable gets a column variable.
	 *
	 * @param oldRowMatrixPos
	 *            The matrix position of the previous row variable.
	 * @param oldColMatrixPos
	 *            The matrix position of the previous column variable.
	 */
	public void swapRowCol(final int oldColMatrixPos) {
		final int oldRowMatrixPos = mEntries[0];
		final int oldIdx = findRawIndex(oldColMatrixPos);
		int newIdx = findRawIndex(oldRowMatrixPos);
		assert oldIdx >= 1;
		assert mEntries[2 * oldIdx] == oldColMatrixPos;
		assert 2 * newIdx == mEntries.length || mEntries[2 * newIdx] > oldRowMatrixPos;
		assert newIdx == 1 || mEntries[2 * (newIdx - 1)] < oldRowMatrixPos;
		final int newHeadCoeff = mEntries[2 * oldIdx + 1];
		if (oldIdx < newIdx) {
			newIdx--;
			System.arraycopy(mEntries, 2 * oldIdx + 2, mEntries, 2 * oldIdx, 2 * (newIdx - oldIdx));
		} else {
			System.arraycopy(mEntries, 2 * newIdx, mEntries, 2 * newIdx + 2, 2 * (oldIdx - newIdx));
		}
		mEntries[2 * newIdx] = oldRowMatrixPos;
		mEntries[2 * newIdx + 1] = mEntries[1];
		mEntries[0] = oldColMatrixPos;
		mEntries[1] = newHeadCoeff;
	}

	/**
	 * Returns the coefficient of the given column variable. It returns {@code BigInteger.valueOf(0)}, if the column
	 * variable doesn't appear in the tableaux row.
	 *
	 * @param matrixPos
	 *            the matrix position of the column variable.
	 * @return the corresponding coefficient.
	 */
	public BigInteger getCoeffForPos(final int matrixPos) {
		return bigEntry(findEntry(matrixPos));
	}

	int getRawIndex(final int idx) {
		return mEntries[2*idx];
	}

	BigInteger getRawCoeff(final int idx) {
		return bigEntry(mEntries[2*idx + 1]);
	}

	int size() {
		return mEntries.length / 2;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(getRawCoeff(0)).append(" * y").append(getRawIndex(0));
		for (int i = 1; i < size(); i++) {
			sb.append(" + ");
			sb.append(getRawCoeff(i)).append(" * x").append(getRawIndex(i));
		}
		return sb.toString();
	}
}
