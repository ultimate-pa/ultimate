package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.util.ArrayList;
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

	public static RationalMatrix getZeroMatrix(final int rowCount, final int columnCount) {
		return new RationalMatrix(new Array2DRowFieldMatrix<>(BigFractionField.getInstance(), rowCount, columnCount));
	}

	public static RationalMatrix ofRowVectors(final List<RationalVector> rowVectors, final int columnCount) {
		final FieldMatrix<BigFraction> matrix = new Array2DRowFieldMatrix<>(BigFractionField.getInstance(),
				rowVectors.size(), columnCount);

		for (int i = 0; i < rowVectors.size(); i++) {
			matrix.setRowVector(i, rowVectors.get(i).getVector());
		}

		return new RationalMatrix(matrix);
	}

	public static RationalMatrix ofColumnVectors(final List<RationalVector> columnVectors, final int rowCount) {
		final FieldMatrix<BigFraction> matrix = new Array2DRowFieldMatrix<>(BigFractionField.getInstance(), rowCount,
				columnVectors.size());

		for (int i = 0; i < columnVectors.size(); i++) {
			matrix.setColumnVector(i, columnVectors.get(i).getVector());
		}

		return new RationalMatrix(matrix);
	}

	public List<RationalVector> getRowVectors() {
		final List<RationalVector> rowVectors = new ArrayList<>();
		for (int i = 0; i < getRowCount(); i++) {
			final RationalVector rowVector = new RationalVector(mMatrix.getRowVector(i));
			rowVectors.add(rowVector);
		}
		return rowVectors;
	}

	public List<RationalVector> getColumnVectors() {
		final List<RationalVector> columnVectors = new ArrayList<>();
		for (int i = 0; i < getColumnCount(); i++) {
			final RationalVector columnVector = new RationalVector(mMatrix.getColumnVector(i));
			columnVectors.add(columnVector);
		}
		return columnVectors;
	}

	public int getColumnCount() {
		return mMatrix.getColumnDimension();
	}

	public int getRowCount() {
		return mMatrix.getRowDimension();
	}

	public boolean isSquare() {
		return getColumnCount() == getRowCount();
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
