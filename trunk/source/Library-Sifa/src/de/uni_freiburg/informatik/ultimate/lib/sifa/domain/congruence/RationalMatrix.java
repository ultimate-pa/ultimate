package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.util.List;

import org.apache.commons.math3.fraction.BigFraction;
import org.apache.commons.math3.fraction.BigFractionField;
import org.apache.commons.math3.linear.Array2DRowFieldMatrix;
import org.apache.commons.math3.linear.FieldLUDecomposition;
import org.apache.commons.math3.linear.FieldMatrix;

import de.uni_freiburg.informatik.ultimate.logic.Rational;

public class RationalMatrix {
	private final FieldMatrix<BigFraction> mMatrix;

	private RationalMatrix(final FieldMatrix<BigFraction> matrix) {
		mMatrix = matrix;
	}

	public static RationalMatrix ofRowVectors(final List<RationalVector> rowVectors, final int columnCount) {
		final FieldMatrix<BigFraction> matrix = new Array2DRowFieldMatrix<>(BigFractionField.getInstance(),
				rowVectors.size(), columnCount);

		for (int i = 0; i < rowVectors.size(); i++) {
			matrix.setRowVector(i, rowVectors.get(i).getVector());
		}

		return new RationalMatrix(matrix);
	}

	public int getColumnCount() {
		return mMatrix.getColumnDimension();
	}

	public int getRowCount() {
		return mMatrix.getRowDimension();
	}

	public Rational get(final int row, final int column) {
		final BigFraction entry = mMatrix.getEntry(row, column);
		return RationalVector.getRationalFromBigFraction(entry);
	}

	public RationalMatrix transpose() {
		return new RationalMatrix(mMatrix.transpose());
	}

	public RationalMatrix invert() {
		final FieldLUDecomposition<BigFraction> lu = new FieldLUDecomposition<>(mMatrix);
		return new RationalMatrix(lu.getSolver().getInverse());
	}

	@Override
	public String toString() {
		return mMatrix.toString();
	}

}
