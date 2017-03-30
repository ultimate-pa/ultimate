package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr;

import java.util.Arrays;

/**
 * Parametric Octagons Parametric octagons can (compared to regular octagons) have variables on the right side, so they
 * have the form: +-x+-y <= a*k+b, +-2x <= a*k+b, +-y <= a*k+b
 */

public class ParametricOct {

	private final int mSize;
	private ParametricOctValue[][] mValues;

	public ParametricOct() {
		mSize = 0;
	}

	public ParametricOct(final int size) {
		mSize = size;
	}

	public void setValues(final int row, final int column, final ParametricOctValue[] values) {
		if (values.length != 4) {
			throw new IllegalArgumentException("4 Values are required.");
		}
		setValue((int) Math.floor(row / 2), (int) Math.floor(column / 2), values[0]);
		setValue((int) Math.floor(row / 2) + 1, (int) Math.floor(column / 2), values[0]);
		setValue((int) Math.floor(row / 2), (int) Math.floor(column / 2) + 1, values[0]);
		setValue((int) Math.floor(row / 2) + 1, (int) Math.floor(column / 2) + 1, values[0]);
	}

	private void setValue(final int row, final int column, final ParametricOctValue value) {
		fixSize((row > column ? row : column));
		mValues[row][column] = value;
	}

	private void fixSize(final int newSize) {
		final int neededSize = (int) Math.pow(Math.ceil((newSize / 2)) * 2, 2);

		if (mValues.length < neededSize) {
			mValues = Arrays.copyOf(mValues, neededSize);
		}
	}

	private int getIndex(final int row, final int column) {
		/*
		 * 0 - 0 : 0 1 - 0 : 1 0 - 1 : 2 1 - 1 : 3
		 *
		 */
		return 0;
	}
}
