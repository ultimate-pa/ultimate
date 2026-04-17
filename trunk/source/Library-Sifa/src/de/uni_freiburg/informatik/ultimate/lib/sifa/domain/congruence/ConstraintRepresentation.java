package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.LongStream;

import org.ojalgo.matrix.MatrixQ128;
import org.ojalgo.scalar.RationalNumber;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class ConstraintRepresentation {
	private MatrixQ128 mEqualityMatrix;
	private MatrixQ128 mCongruenceMatrix;

	final private int mVectorLength;

	private boolean mIsMinimal;
	private boolean mIsStrongMinimal;

	public ConstraintRepresentation(final List<MatrixQ128> equalities, final List<MatrixQ128> congruences,
			final int vectorLength) {
		this(equalities, congruences, vectorLength, false, false);
	}

	/**
	 * WARNING: Only give isMinimal/isStrongMinimal as true if lineMatrix and
	 * parameterMatrix are minimal/strongly minimal. Alternatively use the
	 * constructor without isMinimal/isStrongMinimal and call
	 * minimize/stronglyMinimize afterwards.
	 */
	ConstraintRepresentation(final List<MatrixQ128> equalities, final List<MatrixQ128> congruences,
			final int vectorLength, final boolean isMinimal, final boolean isStrongMinimal) {
		mEqualityMatrix = CongruenceUtil.getMatrixFromRows(equalities);
		mCongruenceMatrix = CongruenceUtil.getMatrixFromRows(congruences);
		mVectorLength = vectorLength;
		mIsMinimal = isMinimal;
		mIsStrongMinimal = isStrongMinimal;
	}

	public MatrixQ128 getEqualityMatrix() {
		return mEqualityMatrix;
	}

	public MatrixQ128 getCongruenceMatrix() {
		return mCongruenceMatrix;
	}

	public List<MatrixQ128> getEqualities() {
		return CongruenceUtil.getRowsFromMatrix(mEqualityMatrix);
	}

	public List<MatrixQ128> getCongruences() {
		return CongruenceUtil.getRowsFromMatrix(mCongruenceMatrix);
	}

	public boolean isMinimal() {
		return mIsMinimal;
	}

	public boolean isStrongMinimal() {
		return mIsStrongMinimal;
	}

	@Override
	public String toString() {
		return "ConstraintRepresentation [mEqualityMatrix=" + mEqualityMatrix + ", mCongruenceMatrix="
				+ mCongruenceMatrix + ", mIsMinimal=" + mIsMinimal + ", mIsStrongMinimal=" + mIsStrongMinimal + "]";
	}

	public static ConstraintRepresentation getEmpty(final int vectorLength) {
		return new ConstraintRepresentation(List.of(), List.of(), vectorLength, true, true);
	}

	public static ConstraintRepresentation getUnsat(final int vectorLength) {
		return new ConstraintRepresentation(List.of(unsatVector(vectorLength)), List.of(), vectorLength, true, true);
	}

	private void markAsUnsat() {
		mEqualityMatrix = unsatVector(mVectorLength);
		mCongruenceMatrix = CongruenceUtil.getMatrixFromRows(List.of());
		mIsMinimal = true;
		mIsStrongMinimal = true;
	}

	public boolean isUnsat() {
		minimize();
		for (final MatrixQ128 equality : getEqualities()) {
			if (equality.equals(ConstraintRepresentation.unsatVector(mVectorLength))) {
				return true;
			}
		}
		return false;
	}

	private static MatrixQ128 unsatVector(final int length) {
		final List<Integer> list = new ArrayList<>(Collections.nCopies(length, 0));
		list.set(0, -1);
		return CongruenceUtil.getRowVectorFromIntList(list);
	}

	public void minimize() {
		if (mIsMinimal) {
			return;
		}

		final List<MatrixQ128> equalities = getEqualities();
		final List<MatrixQ128> congruences = getCongruences();

		final List<Integer> equalitiesToDelete = new ArrayList<>();
		final List<Integer> congruencesToDelete = new ArrayList<>();

		// Making the equality pivots unique
		for (int i = 0; i < equalities.size(); i++) {
			MatrixQ128 equality = equalities.get(i);
			final long pivot = CongruenceUtil.lastPivot(equality);

			if (pivot == -1) {
				// vector is empty, can be deleted
				equalitiesToDelete.add(i);
			} else if (pivot == 0) {
				// equality is unsatisfiable and so is the whole system
				markAsUnsat();
				return;

			} else {
				// Make pivotValue positive
				final RationalNumber pivotValue = equality.get(0, pivot);
				if (pivotValue.compareTo(RationalNumber.ZERO) < 0) {
					equality = equality.negate();
					equalities.set(i, equality);
				}

				// Eliminate the pivot field from the following equalities
				for (int j = i + 1; j < equalities.size(); j++) {
					final MatrixQ128 other = equalities.get(j);
					equalities.set(j, CongruenceUtil.gaussEliminateField(other, equality, pivot));
				}

				// Eliminate the pivot field from the following congruence's
				for (int j = 0; j < congruences.size(); j++) {
					final MatrixQ128 other = congruences.get(j);
					congruences.set(j, CongruenceUtil.gaussEliminateField(other, equality, pivot));
				}
			}
		}

		// Making the congruence pivots unique
		for (int i = 0; i < congruences.size(); i++) {
			MatrixQ128 congruence = congruences.get(i);
			final long pivot = CongruenceUtil.lastPivot(congruence);

			if (pivot == -1) {
				// vector is empty, can be deleted
				congruencesToDelete.add(i);
			} else if (pivot == 0) {
				// We just have a constant
				if (CongruenceUtil.getDenominator(congruence.get(0, pivot)) == 1) {
					// The constant is whole and so it's 0 mod 1
					// We dont need this trivial term further on tho
					congruencesToDelete.add(i);
				}
				// The constant is not 0 mod 1
				// So the congruence is unsatisfiable and so is the whole system
				markAsUnsat();
				return;
			} else {
				// Make pivotValue positive
				final var pivotValue = congruence.get(0, pivot);
				if (pivotValue.compareTo(RationalNumber.ZERO) < 0) {
					congruence = congruence.negate();
					congruences.set(i, congruence);
				}

				// Eliminate the pivot field from the following congruence's
				// We can't eliminate it from the equalities, since adding a congruence to an
				// equality doesn't conserve the equality
				// We need to use the hermit elimination to preserve congruence's
				for (int j = i + 1; j < congruences.size(); j++) {
					final MatrixQ128 other = congruences.get(j);
					final long otherPivot = CongruenceUtil.lastPivot(other);

					if (pivot == otherPivot) {
						final Pair<MatrixQ128, MatrixQ128> pair = CongruenceUtil.hermitEliminateField(other, congruence,
								pivot);
						congruences.set(j, pair.getFirst());
						congruences.set(i, pair.getSecond());
					}
				}
			}
		}
		for (final int i : equalitiesToDelete.reversed()) {
			equalities.remove(i);
		}
		for (final int i : congruencesToDelete.reversed()) {
			congruences.remove(i);
		}

		mEqualityMatrix = CongruenceUtil.getMatrixFromRows(equalities);
		mCongruenceMatrix = CongruenceUtil.getMatrixFromRows(congruences);
		mIsMinimal = true;
	}

	public void stronglyMinimize() {
		if (isStrongMinimal()) {
			return;
		}

		minimize();

		final List<MatrixQ128> equalities = getEqualities();
		final List<MatrixQ128> congruences = getCongruences();
		// Sorting the congruence's by last pivot is needed for the rest
		congruences.sort((v1, v2) -> (CongruenceUtil.lastPivot(v1) < CongruenceUtil.lastPivot(v2)) ? 1 : -1);

		for (int i = 0; i < congruences.size(); i++) {
			for (int j = 0; j < congruences.size(); j++) {
				if (i == j) {
					continue;
				}
				final MatrixQ128 congruence = congruences.get(i);
				final MatrixQ128 other = congruences.get(j);
				final long index = CongruenceUtil.lastPivot(other);

				final RationalNumber indexValue = congruence.get(0, index);
				final RationalNumber otherIndexValue = other.get(0, index);
				final RationalNumber indexValue2 = indexValue.multiply(2);

				if (indexValue2.compareTo(otherIndexValue.negate()) <= 0
						|| indexValue2.compareTo(otherIndexValue) > 0) {
					final MatrixQ128 v1 = congruence;
					final MatrixQ128 v2 = other;

					final long congruenceDenominator = CongruenceUtil.getCommonDenominator(congruence);
					final long otherDenominator = CongruenceUtil.getCommonDenominator(other);
					final long commonDenominator = CongruenceUtil.lcm(congruenceDenominator, otherDenominator);
					final RationalNumber commonDenominatorRational = RationalNumber.of(commonDenominator, 1);

					final MatrixQ128 wholeV1 = v1.multiply(commonDenominatorRational);
					final MatrixQ128 wholeV2 = v2.multiply(commonDenominatorRational);

					final RationalNumber wholeIndexElement1Rational = wholeV1.get(0, index);
					final RationalNumber wholeIndexElement2Rational = wholeV2.get(0, index);
					final long wholeIndexElement1 = CongruenceUtil.getNumerator(wholeIndexElement1Rational);
					final long wholeIndexElement2 = CongruenceUtil.getNumerator(wholeIndexElement2Rational);

					long factor;
					if ((wholeIndexElement1 % wholeIndexElement2) * 2 > wholeIndexElement1) {
						factor = Math.ceilDivExact(wholeIndexElement1, wholeIndexElement2);
					} else {
						factor = Math.floorDivExact(wholeIndexElement1, wholeIndexElement2);
					}

					final MatrixQ128 newWholeV1 = wholeV1.subtract(wholeV2.multiply(factor));
					final MatrixQ128 newCongruence = newWholeV1.divide(commonDenominatorRational);
					congruences.set(i, newCongruence);
				}

			}
		}
		mEqualityMatrix = CongruenceUtil.getMatrixFromRows(equalities);
		mCongruenceMatrix = CongruenceUtil.getMatrixFromRows(congruences);
		mIsStrongMinimal = true;
	}

	public GeneratorRepresentation computeGeneratorRepresentation() {
		minimize();
		final List<MatrixQ128> equalities = getEqualities();
		final int equalitiesNum = equalities.size();
		final List<MatrixQ128> congruences = getCongruences();
		final int congruencesNum = congruences.size();

		final List<MatrixQ128> constraintList = new ArrayList<>(congruences);
		constraintList.addAll(equalities);

		final Set<Long> missingPivots = LongStream.range(0, mVectorLength).boxed().collect(Collectors.toSet());
		for (final MatrixQ128 vector : constraintList) {
			missingPivots.remove(CongruenceUtil.lastPivot(vector));
		}

		final List<MatrixQ128> fillerList = new ArrayList<>();
		for (final Long missingPivot : missingPivots) {
			fillerList.add(CongruenceUtil.getStandardBasisVector(missingPivot.intValue(), mVectorLength));
		}
		final int fillerNum = fillerList.size();

		final List<MatrixQ128> vectorList = new ArrayList<>(fillerList);
		vectorList.addAll(constraintList);
		final MatrixQ128 constraintMatrix = CongruenceUtil.getMatrixFromRows(vectorList);
		final MatrixQ128 generatorMatrix = constraintMatrix.invert().transpose();
		final List<MatrixQ128> generatorList = CongruenceUtil.getRowsFromMatrix(generatorMatrix);

		final List<MatrixQ128> lines = generatorList.subList(0, fillerNum);
		final List<MatrixQ128> parameters = generatorList.subList(fillerNum, fillerNum + congruencesNum);

		return new GeneratorRepresentation(lines, parameters, mVectorLength, true);
	}
}
