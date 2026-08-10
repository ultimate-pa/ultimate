package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class GeneratorRepresentation {
	private List<RationalVector> mLines;
	private List<RationalVector> mParameters;

	final private int mVectorLength;

	private boolean mIsMinimal;

	public GeneratorRepresentation(final List<RationalVector> lines, final List<RationalVector> parameters,
			final int vectorLength) {
		this(lines, parameters, vectorLength, false);
	}

	/**
	 * WARNING: Only give isMinimal as true if lineMatrix and parameterMatrix are
	 * minimal. Alternatively use the constructor without isMinimal and call
	 * minimize afterwards.
	 */
	GeneratorRepresentation(final List<RationalVector> lines, final List<RationalVector> parameters,
			final int vectorLength, final boolean isMinimal) {
		mLines = lines;
		mParameters = parameters;
		mVectorLength = vectorLength;
		mIsMinimal = isMinimal;
	}

	@Override
	public String toString() {
		return "GeneratorRepresentation [mLineMatrix=" + getLineMatrix() + ", mParameterMatrix=" + getParameterMatrix()
				+ ", mIsMinimal=" + isMinimal() + "]";
	}

	@Override
	public int hashCode() {
		return Objects.hash(mLines, mParameters, mVectorLength, mIsMinimal);
	}

	@Override
	public boolean equals(final Object object) {
		if (!(object instanceof final GeneratorRepresentation other)) {
			return false;
		}

		if (!getLineMatrix().equals(other.getLineMatrix())) {
			return false;
		}
		if (!getParameterMatrix().equals(other.getParameterMatrix())) {
			return false;
		}
		return true;
	}

	public RationalMatrix getLineMatrix() {
		return RationalMatrix.fromRowVectors(mLines, mVectorLength);
	}

	public RationalMatrix getParameterMatrix() {
		return RationalMatrix.fromRowVectors(mParameters, mVectorLength);
	}

	public List<RationalVector> getLines() {
		return new ArrayList<>(mLines);
	}

	public List<RationalVector> getParameters() {
		return new ArrayList<>(mParameters);
	}

	public int getVectorLength() {
		return mVectorLength;
	}

	public boolean isMinimal() {
		return mIsMinimal;
	}

	public boolean isUnsat() {
		minimize();
		for (final RationalVector line : getLines()) {
			if (!line.get(0).equals(Rational.ZERO)) {
				return false;
			}
		}
		for (final RationalVector parameter : getParameters()) {
			final Rational constantFactor = parameter.get(0);
			if (!constantFactor.equals(Rational.ZERO)) {
				final BigInteger absNumerator = constantFactor.numerator().abs();

				if (absNumerator.equals(BigInteger.ONE)) {
					return false;
				}
			}
		}

		return true;
	}

	public void minimize() {
		if (isMinimal()) {
			return;
		}

		final List<RationalVector> lines = getLines();
		final List<RationalVector> parameters = getParameters();

		final List<Integer> linesToDelete = new ArrayList<>();
		final List<Integer> parametersToDelete = new ArrayList<>();

		// Making the line pivots unique
		for (int i = 0; i < lines.size(); i++) {
			RationalVector line = lines.get(i);
			final int pivot = line.firstPivot();

			if (pivot == line.getLength()) {
				// line is empty, can be deleted
				linesToDelete.add(i);
			} else {
				// Make pivotValue positive
				final Rational pivotValue = line.get(pivot);
				if (pivotValue.compareTo(Rational.ZERO) < 0) {
					line = line.negate();
					lines.set(i, line);
				}

				// Eliminate the pivot field from the following lines
				for (int j = i + 1; j < lines.size(); j++) {
					final RationalVector other = lines.get(j);
					lines.set(j, CongruenceUtil.gaussEliminateField(other, line, pivot));
				}
				// Eliminate the pivot field from the parameters
				for (int j = 0; j < parameters.size(); j++) {
					final RationalVector other = parameters.get(j);
					parameters.set(j, CongruenceUtil.gaussEliminateField(other, line, pivot));
				}
			}
		}

		// Delete the empty lines
		for (final int i : linesToDelete.reversed()) {
			lines.remove(i);
		}

		// Making the parameter pivots unique
		for (int index = 0; index < mVectorLength; index++) {
			// Find a parameter with pivot == index
			int i;
			int pivot = mVectorLength;
			RationalVector parameter = null;
			for (i = 0; i < parameters.size(); i++) {
				parameter = parameters.get(i);
				pivot = parameter.firstPivot();

				if (pivot == index) {
					break;
				}
			}

			// If no such parameter is found i is already so large that there is no rest we
			// have to look through

			// Eliminate the pivot field from the following parameters
			for (int j = i + 1; j < parameters.size(); j++) {
				final RationalVector other = parameters.get(j);
				final int otherPivot = other.firstPivot();

				if (pivot == otherPivot) {
					final Pair<RationalVector, RationalVector> pair = CongruenceUtil.hermitEliminateField(other,
							parameter, pivot);
					parameters.set(j, pair.getFirst());
					parameters.set(i, pair.getSecond());
				}
			}
		}

		// Scan for empty parameters
		for (int i = 0; i < parameters.size(); i++) {
			final RationalVector parameter = parameters.get(i);
			final long pivot = parameter.firstPivot();

			if (pivot == parameter.getLength()) {
				// parameter is empty, can be deleted
				parametersToDelete.add(i);
			}
		}

		// Delete the empty parameters
		for (final int i : parametersToDelete.reversed()) {
			parameters.remove(i);
		}

		// Make pivot values for parameters positive
		for (int i = 0; i < parameters.size(); i++) {
			RationalVector parameter = parameters.get(i);
			final int pivot = parameter.firstPivot();
			final var pivotValue = parameter.get(pivot);
			if (pivotValue.compareTo(Rational.ZERO) < 0) {
				parameter = parameter.negate();
				parameters.set(i, parameter);
			}
		}

		mLines = lines;
		mParameters = parameters;
		mIsMinimal = true;

		if (lines.size() + parameters.size() > mVectorLength) {
			throw new AssertionError(
					"lines and parameters are too long\n Lines: " + lines + "\n Parameters: " + parameters);
		}

	}

	public ConstraintRepresentation computeConstraintRepresentation() {
		minimize();

		final List<RationalVector> lines = getLines();
		final int linesNum = lines.size();
		final List<RationalVector> parameters = getParameters();
		final int parametersNum = parameters.size();

		final List<RationalVector> generatorList = new ArrayList<>(lines);
		generatorList.addAll(parameters);

		final Set<Integer> missingPivots = IntStream.range(0, mVectorLength).boxed().collect(Collectors.toSet());
		for (final RationalVector vector : generatorList) {
			missingPivots.remove(vector.firstPivot());
		}

		final List<RationalVector> fillerList = new ArrayList<>();
		for (final Integer missingPivot : missingPivots) {
			fillerList.add(RationalVector.getUnitVector(missingPivot, mVectorLength));
		}
		final int fillerNum = fillerList.size();

		final List<RationalVector> vectorList = new ArrayList<>(generatorList);
		vectorList.addAll(fillerList);
		final RationalMatrix generatorMatrix = RationalMatrix.fromRowVectors(vectorList, mVectorLength);

		if (!generatorMatrix.isSquare()) {
			throw new AssertionError("generatorMatrix is not square. generatorMatrix:  \n" + generatorMatrix);
		}

		final RationalMatrix constraintMatrix = generatorMatrix.invert().transpose();
		final List<RationalVector> constraintList = constraintMatrix.getRowVectors();

		final List<RationalVector> congruences = constraintList.subList(linesNum, linesNum + parametersNum);
		final List<RationalVector> equalities = constraintList.subList(linesNum + parametersNum,
				linesNum + parametersNum + fillerNum);

		return new ConstraintRepresentation(equalities, congruences, mVectorLength, true, false);
	}
}
