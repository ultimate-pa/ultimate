package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.ojalgo.matrix.MatrixQ128;
import org.ojalgo.scalar.RationalNumber;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class GeneratorRepresentation {
	private MatrixQ128 mLineMatrix;
	private MatrixQ128 mParameterMatrix;

	final private int mVectorLength;

	private boolean mIsMinimal;

	public GeneratorRepresentation(final List<MatrixQ128> lines, final List<MatrixQ128> parameters,
			final int vectorLength) {
		this(lines, parameters, vectorLength, false);
	}

	/**
	 * WARNING: Only give isMinimal as true if lineMatrix and parameterMatrix are
	 * minimal. Alternatively just use the constructor without isMinimal and call
	 * minimize afterwards.
	 */
	GeneratorRepresentation(final MatrixQ128 lineMatrix, final MatrixQ128 parameterMatrix, final int vectorLength,
			final boolean isMinimal) {
		mLineMatrix = lineMatrix;
		mParameterMatrix = parameterMatrix;
		mVectorLength = vectorLength;
		mIsMinimal = isMinimal;
	}

	/**
	 * WARNING: Only give isMinimal as true if lineMatrix and parameterMatrix are
	 * minimal. Alternatively use the constructor without isMinimal and call
	 * minimize afterwards.
	 */
	GeneratorRepresentation(final List<MatrixQ128> lines, final List<MatrixQ128> parameters, final int vectorLength,
			final boolean isMinimal) {
		this(CongruenceUtil.getMatrixFromRows(lines), CongruenceUtil.getMatrixFromRows(parameters), vectorLength,
				isMinimal);
	}

	@Override
	public String toString() {
		return "GeneratorRepresentation [mLineMatrix=" + getLineMatrix() + ", mParameterMatrix=" + getParameterMatrix()
				+ ", mIsMinimal=" + isMinimal() + "]";
	}

	public boolean equals(final GeneratorRepresentation other) {
		if (!getLineMatrix().equals(other.getLineMatrix())) {
			return false;
		}
		if (!getParameterMatrix().equals(other.getParameterMatrix())) {
			return false;
		}
		return true;
	}

	public MatrixQ128 getLineMatrix() {
		return mLineMatrix;
	}

	public MatrixQ128 getParameterMatrix() {
		return mParameterMatrix;
	}

	public List<MatrixQ128> getLines() {
		return CongruenceUtil.getRowsFromMatrix(getLineMatrix());
	}

	public List<MatrixQ128> getParameters() {
		return CongruenceUtil.getRowsFromMatrix(getParameterMatrix());
	}

	public boolean isMinimal() {
		return mIsMinimal;
	}

	public void minimize() {
		if (isMinimal()) {
			return;
		}

		final List<MatrixQ128> lines = getLines();
		final List<MatrixQ128> parameters = getParameters();

		final List<Integer> linesToDelete = new ArrayList<>();
		final List<Integer> parametersToDelete = new ArrayList<>();

		// Making the line pivots unique
		for (int i = 0; i < lines.size(); i++) {
			MatrixQ128 line = lines.get(i);
			final long pivot = CongruenceUtil.firstPivot(line);

			if (pivot == line.countColumns()) {
				// line is empty, can be deleted
				linesToDelete.add(i);
			} else {
				// Make pivotValue positive
				final RationalNumber pivotValue = line.get(0, pivot);
				if (pivotValue.compareTo(RationalNumber.ZERO) < 0) {
					line = line.negate();
					lines.set(i, line);
				}

				// Eliminate the pivot field from the following lines
				for (int j = i + 1; j < lines.size(); j++) {
					final MatrixQ128 other = lines.get(j);
					lines.set(j, CongruenceUtil.gaussEliminateField(other, line, pivot));
				}
				// Eliminate the pivot field from the parameters
				for (int j = 0; j < parameters.size(); j++) {
					final MatrixQ128 other = parameters.get(j);
					parameters.set(j, CongruenceUtil.gaussEliminateField(other, line, pivot));
				}
			}
		}

		// Making the parameter pivots unique
		for (int i = 0; i < parameters.size(); i++) {
			MatrixQ128 parameter = parameters.get(i);
			final long pivot = CongruenceUtil.firstPivot(parameter);

			if (pivot == parameter.countColumns()) {
				// parameter is empty, can be deleted
				parametersToDelete.add(i);
			} else {
				// Make pivotValue positive
				final RationalNumber pivotValue = parameter.get(0, pivot);
				if (pivotValue.compareTo(RationalNumber.ZERO) < 0) {
					parameter = parameter.negate();
					parameters.set(i, parameter);
				}

				// Eliminate the pivot field from the following parameters
				for (int j = i; j < parameters.size(); j++) {
					final MatrixQ128 other = parameters.get(j);
					final Pair<MatrixQ128, MatrixQ128> pair = CongruenceUtil.hermitEliminateField(other, parameter,
							pivot);
					parameters.set(j, pair.getFirst());
					parameters.set(i, pair.getSecond());
				}
			}
		}

		for (final int i : linesToDelete.reversed()) {
			lines.remove(i);
		}
		for (final int i : parametersToDelete.reversed()) {
			parameters.remove(i);
		}

		final MatrixQ128 minimalLineMatrix = CongruenceUtil.getMatrixFromRows(lines);
		final MatrixQ128 minimalParameterMatrix = CongruenceUtil.getMatrixFromRows(parameters);

		mLineMatrix = minimalLineMatrix;
		mParameterMatrix = minimalParameterMatrix;
		mIsMinimal = true;
	}

	public GeneratorRepresentation getReorderedForm(final Map<Integer, Integer> reorderMap,
			final int resultColumnCount) {
		final MatrixQ128 reorderedLineMatrix = CongruenceUtil.reorderByColumns(reorderMap, resultColumnCount,
				getLineMatrix());
		final MatrixQ128 reorderedParameterMatrix = CongruenceUtil.reorderByColumns(reorderMap, resultColumnCount,
				getParameterMatrix());
		return new GeneratorRepresentation(reorderedLineMatrix, reorderedParameterMatrix, resultColumnCount,
				isMinimal());
	}

	public ConstraintRepresentation computeConstraintRepresentation() {
		// TODO
		return null;
	}
}
