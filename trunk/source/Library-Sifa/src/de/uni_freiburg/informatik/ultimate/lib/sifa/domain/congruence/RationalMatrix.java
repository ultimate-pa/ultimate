package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import org.apache.commons.math3.fraction.BigFraction;
import org.apache.commons.math3.fraction.BigFractionField;
import org.apache.commons.math3.linear.FieldLUDecomposition;
import org.apache.commons.math3.linear.FieldMatrix;
import org.apache.commons.math3.linear.SparseFieldMatrix;

import de.uni_freiburg.informatik.ultimate.logic.Rational;

public class RationalMatrix {

	private final FieldMatrix<BigFraction> mMatrix;
	private final boolean mIsEmpty;

	private RationalMatrix(final FieldMatrix<BigFraction> matrix) {
		mMatrix = matrix;
		mIsEmpty = false;
	}

//	private RationalMatrix(final FieldMatrix<BigFraction> matrix) {
//		final SparseFieldMatrix<BigFraction> sparseMatrix = new SparseFieldMatrix<>(BigFractionField.getInstance(),
//				matrix.getRowDimension(), matrix.getColumnDimension());
//
//		for (int i = 0; i < matrix.getRowDimension(); i++) {
//			for (int j = 0; j < matrix.getColumnDimension(); j++) {
//				final BigFraction entry = matrix.getEntry(i, j);
//				if (!entry.equals(BigFraction.ZERO)) {
//					sparseMatrix.setEntry(i, j, entry);
//				}
//			}
//		}
//		mMatrix = sparseMatrix;
//		mIsEmpty = false;
//	}

	private RationalMatrix() {
		mMatrix = null;
		mIsEmpty = true;
	}

	public static RationalMatrix getZeroMatrix(final int rowCount, final int columnCount) {
		if (rowCount == 0 || columnCount == 0) {
			return new RationalMatrix();
		}
		return new RationalMatrix(new SparseFieldMatrix<>(BigFractionField.getInstance(), rowCount, columnCount));
	}

	public static RationalMatrix fromRowVectors(final List<RationalVector> rowVectors, final int columnCount) {
		if (rowVectors.size() == 0 || columnCount == 0) {
			return new RationalMatrix();
		}

		final SparseFieldMatrix<BigFraction> matrix = new SparseFieldMatrix<>(BigFractionField.getInstance(),
				rowVectors.size(), columnCount);

		for (int i = 0; i < rowVectors.size(); i++) {
			matrix.setRowVector(i, rowVectors.get(i).getVector());
		}

		return new RationalMatrix(matrix);
	}

	public static RationalMatrix fromColumnVectors(final List<RationalVector> columnVectors, final int rowCount) {
		if (rowCount == 0 || columnVectors.size() == 0) {
			return new RationalMatrix();
		}

		final SparseFieldMatrix<BigFraction> matrix = new SparseFieldMatrix<>(BigFractionField.getInstance(), rowCount,
				columnVectors.size());

		for (int i = 0; i < columnVectors.size(); i++) {
			matrix.setColumnVector(i, columnVectors.get(i).getVector());
		}

		return new RationalMatrix(matrix);
	}

	public static RationalMatrix fromIntList(final List<Integer> integerList, final int rowCount,
			final int columnCount) {
		final List<Rational> rationalList = new ArrayList<>();
		for (final Integer integer : integerList) {
			rationalList.add(Rational.valueOf(integer.longValue(), 1));
		}
		return fromRationalList(rationalList, rowCount, columnCount);
	}

	public static RationalMatrix fromRationalList(final List<Rational> rationalList, final int rowCount,
			final int columnCount) {
		final List<RationalVector> rationalVectorList = new ArrayList<>();
		for (int i = 0; i < rowCount; i++) {
			final int index = i * columnCount;
			rationalVectorList.add(new RationalVector(rationalList.subList(index, index + columnCount)));
		}
		return fromRowVectors(rationalVectorList, columnCount);
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
		if (isEmpty()) {
			return 0;
		}
		return mMatrix.getColumnDimension();
	}

	public int getRowCount() {
		if (isEmpty()) {
			return 0;
		}
		return mMatrix.getRowDimension();
	}

	public boolean isSquare() {
		return getColumnCount() == getRowCount();
	}

	public boolean isEmpty() {
		return mIsEmpty;
	}

	public Rational get(final int row, final int column) {
		if ((0 <= row && row < getRowCount()) && (0 <= column && column < getColumnCount())) {
			final BigFraction entry = mMatrix.getEntry(row, column);
			return RationalVector.getRationalFromBigFraction(entry);
		}
		throw new ArrayIndexOutOfBoundsException(null);

	}

	public RationalMatrix transpose() {
		if (isEmpty()) {
			return this;
		}
		return new RationalMatrix(mMatrix.transpose());
	}

	public RationalMatrix invert() {
		if (isEmpty()) {
			return this;
		}
		final FieldLUDecomposition<BigFraction> lu = new FieldLUDecomposition<>(mMatrix);
		return new RationalMatrix(lu.getSolver().getInverse());
	}

	@Override
	public int hashCode() {
		return Objects.hash(mIsEmpty, mMatrix);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final RationalMatrix other = (RationalMatrix) obj;
		return mIsEmpty == other.mIsEmpty && Objects.equals(mMatrix, other.mMatrix);
	}

	@Override
	public String toString() {
		final StringBuilder out = new StringBuilder("\n[ ");

		for (int i = 0; i < getRowCount(); i++) {
			if (i != 0) {
				out.append("\n");
			}
			for (int j = 0; j < getColumnCount(); j++) {
				out.append(get(i, j));
				if (j != getColumnCount() - 1) {
					out.append(", ");
				}
			}
		}
		out.append(" ]\n");
		return out.toString();
	}

}
