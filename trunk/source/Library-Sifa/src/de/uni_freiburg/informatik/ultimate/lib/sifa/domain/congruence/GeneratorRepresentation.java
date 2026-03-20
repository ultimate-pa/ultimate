package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.util.List;

import org.ojalgo.matrix.MatrixQ128;

public class GeneratorRepresentation {
	final private MatrixQ128 mLineMatrix;
	final private MatrixQ128 mParameterMatrix;

	final private boolean mIsMinimal;

	public GeneratorRepresentation(final MatrixQ128 lineMatrix, final MatrixQ128 parameterMatrix,
			final boolean isMinimal) {
		mLineMatrix = lineMatrix;
		mParameterMatrix = parameterMatrix;
		mIsMinimal = isMinimal;
	}

	public MatrixQ128 getLineMatrix() {
		return mLineMatrix;
	}

	public MatrixQ128 getParameterMatrix() {
		return mParameterMatrix;
	}

	public boolean isIsMinimal() {
		return mIsMinimal;
	}

	public List<MatrixQ128> getLines() {
		return CongruenceUtil.getRowsFromMatrix(mLineMatrix);
	}

	public List<MatrixQ128> getParameters() {
		return CongruenceUtil.getRowsFromMatrix(mParameterMatrix);
	}

	public GeneratorRepresentation convertToMinimalForm() {
		// TODO
		return null;
	}

	public ConstraintRepresentation computeConstraintRepresentation() {
		return null;
	}
}
