package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.util.ArrayList;
import java.util.List;

import org.ojalgo.matrix.MatrixQ128;
import org.ojalgo.scalar.RationalNumber;

public class GeneratorRepresentation {
	final private MatrixQ128 mLineMatrix;
	final private MatrixQ128 mParameterMatrix;

	final private boolean mIsMinimal;

	public GeneratorRepresentation(final List<MatrixQ128> lines, final List<MatrixQ128> parameters) {
		mLineMatrix = CongruenceUtil.getMatrixFromRows(lines);
		mParameterMatrix = CongruenceUtil.getMatrixFromRows(parameters);
		mIsMinimal = false;
	}

	public GeneratorRepresentation(final List<MatrixQ128> lines, final List<MatrixQ128> parameters,
			final boolean isMinimal) {
		mLineMatrix = CongruenceUtil.getMatrixFromRows(lines);
		mParameterMatrix = CongruenceUtil.getMatrixFromRows(parameters);
		mIsMinimal = isMinimal;
	}

	@Override
	public String toString() {
		return "GeneratorRepresentation [mLineMatrix=" + mLineMatrix + ", mParameterMatrix=" + mParameterMatrix
				+ ", mIsMinimal=" + mIsMinimal + "]";
	}

	public MatrixQ128 getLineMatrix() {
		return mLineMatrix;
	}

	public MatrixQ128 getParameterMatrix() {
		return mParameterMatrix;
	}

	public List<MatrixQ128> getLines() {
		return CongruenceUtil.getRowsFromMatrix(mLineMatrix);
	}

	public List<MatrixQ128> getParameters() {
		return CongruenceUtil.getRowsFromMatrix(mParameterMatrix);
	}

	public boolean isMinimal() {
		return mIsMinimal;
	}

	public GeneratorRepresentation getMinimalForm() {
		if (isMinimal()) {
			return this;
		}

		final List<MatrixQ128> lines = getLines();
		final List<MatrixQ128> parameters = getParameters();

		final List<MatrixQ128> vectors = new ArrayList<>(lines);
		vectors.addAll(parameters);

		final int numLines = lines.size();

		final List<Integer> vectorsToDelete = new ArrayList<>();

		// Making the vector pivots unique
		for (int i = 0; i < vectors.size(); i++) {
			final MatrixQ128 vector = vectors.get(i);
			final long pivot = CongruenceUtil.firstPivot(vector);

			if (pivot == vector.countColumns()) {
				// vector is empty, can be deleted
				vectorsToDelete.add(i);
			} else {
				// Make pivotValue positive
				final RationalNumber pivotValue = vector.get(0, pivot);
				if (pivotValue.compareTo(RationalNumber.ZERO) < 0) {
					vectors.set(i, vector.multiply((-1)));
				}

				// Eliminate the pivot field from the following vectors
				for (int j = i + 1; j < vectors.size(); j++) {
					final MatrixQ128 other = vectors.get(j);
					vectors.set(j, CongruenceUtil.eliminateField(other, vector, pivot));
				}
			}
		}

		final List<MatrixQ128> newLines = new ArrayList<>();
		final List<MatrixQ128> newParameters = new ArrayList<>();

		for (int i = 0; i < vectors.size(); i++) {
			final MatrixQ128 vector = vectors.get(i);

			if (i < numLines) {
				newLines.add(vector);
			} else {
				newParameters.add(vector);
			}
		}

		for (final int i : vectorsToDelete.reversed()) {
			if (i < numLines) {
				newLines.remove(i);
			} else {
				newParameters.remove(i - numLines);
			}
		}
		return new GeneratorRepresentation(newLines, newParameters, true);

	}

	public ConstraintRepresentation computeConstraintRepresentation() {
		// TODO
		return null;
	}
}
