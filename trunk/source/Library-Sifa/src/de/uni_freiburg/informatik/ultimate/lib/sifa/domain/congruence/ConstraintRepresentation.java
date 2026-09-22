/*
 * Copyright (C) 2026 Max Lehr
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Constraint based representation of equalities and congruences. Stores equalities of form "∑ a_i * x_i = c" as vectors
 * [-c, a_0, ..., a_n] and stores congruences of form "∑ a_i * x_i ≡b c" as vectors [-c/b, a_0/b, ..., a_n/b], where x_i
 * correspond to numerical (ints and reals) variables and a_i, b and c to constants.
 *
 * @author Max Lehr
 *
 */
public class ConstraintRepresentation {
	private List<RationalVector> mEqualities;
	private List<RationalVector> mCongruences;

	private final int mVectorLength;

	private boolean mIsMinimal;
	private boolean mIsStrongMinimal;

	public ConstraintRepresentation(final List<RationalVector> equalities, final List<RationalVector> congruences,
			final int vectorLength) {
		this(equalities, congruences, vectorLength, false, false);
	}

	/**
	 * WARNING: Only give isMinimal/isStrongMinimal as true if lineMatrix and parameterMatrix are minimal/strongly
	 * minimal. Alternatively use the constructor without isMinimal/isStrongMinimal and call minimize/stronglyMinimize
	 * afterwards.
	 */
	ConstraintRepresentation(final List<RationalVector> equalities, final List<RationalVector> congruences,
			final int vectorLength, final boolean isMinimal, final boolean isStrongMinimal) {
		mEqualities = equalities;
		mCongruences = congruences;
		mVectorLength = vectorLength;

		mIsMinimal = isMinimal;
		mIsStrongMinimal = isStrongMinimal;
	}

	public RationalMatrix getEqualityMatrix() {
		return RationalMatrix.fromRowVectors(mEqualities, mVectorLength);
	}

	public RationalMatrix getCongruenceMatrix() {
		return RationalMatrix.fromRowVectors(mCongruences, mVectorLength);
	}

	public List<RationalVector> getEqualities() {
		return new ArrayList<>(mEqualities);
	}

	public List<RationalVector> getCongruences() {
		return new ArrayList<>(mCongruences);
	}

	public int getVectorLength() {
		return mVectorLength;
	}

	public boolean isMinimal() {
		return mIsMinimal;
	}

	public boolean isStrongMinimal() {
		return mIsStrongMinimal;
	}

	@Override
	public String toString() {
		return "ConstraintRepresentation [mEqualityMatrix=" + getEqualityMatrix() + ", mCongruenceMatrix="
				+ getCongruenceMatrix() + ", mIsMinimal=" + mIsMinimal + ", mIsStrongMinimal=" + mIsStrongMinimal + "]";
	}

	@Override
	public int hashCode() {
		return Objects.hash(mCongruences, mEqualities, mIsMinimal, mIsStrongMinimal, mVectorLength);
	}

	@Override
	public boolean equals(final Object object) {
		if (!(object instanceof final ConstraintRepresentation other)) {
			return false;
		}

		if (!getEqualityMatrix().equals(other.getEqualityMatrix())) {
			return false;
		}
		if (!getCongruenceMatrix().equals(other.getCongruenceMatrix())) {
			return false;
		}
		return true;
	}

	/**
	 * Returns an empty instance of a {@link ConstraintRepresentation}, so without any equalities or constraints.
	 */
	public static ConstraintRepresentation getEmpty(final int vectorLength) {
		return new ConstraintRepresentation(List.of(), List.of(), vectorLength, true, true);
	}

	/**
	 * Returns the amount of vectors needed to generate all vectors that satisfy the constraints. This can be seen as
	 * the dimension of the space containing all valid variable assignments.
	 */
	public int getDim() {
		minimize();
		return getVectorLength() - getEqualities().size();
	}

	/**
	 * Reorders the entries of the equality and congruence vectors according to the permutation given by reorderMap and
	 * extends them to have size resultColumnCount. Returns a new {@link ConstraintRepresentation} containing the
	 * reordered equalities and constraints.
	 */
	public ConstraintRepresentation getReorderedForm(final Map<Integer, Integer> reorderMap,
			final int resultColumnCount) {

		final RationalMatrix reorderedEqualityMatrix =
				CongruenceUtil.reorderByColumns(reorderMap, resultColumnCount, getEqualityMatrix());
		final RationalMatrix reorderedCongruenceMatrix =
				CongruenceUtil.reorderByColumns(reorderMap, resultColumnCount, getCongruenceMatrix());

		return new ConstraintRepresentation(reorderedEqualityMatrix.getRowVectors(),
				reorderedCongruenceMatrix.getRowVectors(), resultColumnCount);
	}

	/**
	 * Converts the representation to be in minimal form. In minimal form the index of the last non zero entry of every
	 * equality and congruence vector is unique and the entry is positive.
	 */
	public void minimize() {
		if (mIsMinimal) {
			return;
		}

		final List<RationalVector> equalities = getEqualities();
		final List<RationalVector> congruences = getCongruences();

		final List<Integer> equalitiesToDelete = new ArrayList<>();
		final List<Integer> congruencesToDelete = new ArrayList<>();

		// Making the equality pivots unique
		for (int i = 0; i < equalities.size(); i++) {
			RationalVector equality = equalities.get(i);
			final int pivot = equality.lastPivot();

			if (pivot == -1) {
				// vector is empty, can be deleted
				equalitiesToDelete.add(i);

			} else {
				// Make pivotValue positive
				final Rational pivotValue = equality.get(pivot);
				if (pivotValue.compareTo(Rational.ZERO) < 0) {
					equality = equality.negate();
					equalities.set(i, equality);
				}

				// Eliminate the pivot field from the following equalities
				for (int j = i + 1; j < equalities.size(); j++) {
					final RationalVector other = equalities.get(j);
					equalities.set(j, CongruenceUtil.gaussEliminateField(other, equality, pivot));
				}

				// Eliminate the pivot field from the following congruence's
				for (int j = 0; j < congruences.size(); j++) {
					final RationalVector other = congruences.get(j);
					congruences.set(j, CongruenceUtil.gaussEliminateField(other, equality, pivot));
				}
			}
		}
		// Deleter empty equalities
		for (final int i : equalitiesToDelete.reversed()) {
			equalities.remove(i);
		}

		// Making the congruence pivots unique
		for (int index = mVectorLength - 1; index >= 0; index--) {
			// Find a congruence with pivot == index
			int i;
			int pivot = mVectorLength;
			RationalVector congruence = null;
			for (i = 0; i < congruences.size(); i++) {
				congruence = congruences.get(i);
				pivot = congruence.lastPivot();

				if (pivot == index) {
					break;
				}
			}

			// If no such congruence is found i is already so large that there is no rest we
			// have to look through

			// Eliminate the pivot field from the following congruence's
			// We can't eliminate it from the equalities, since adding a congruence to an
			// equality doesn't conserve the equality
			// We need to use the hermit elimination to preserve congruence's
			for (int j = i + 1; j < congruences.size(); j++) {
				final RationalVector other = congruences.get(j);
				final long otherPivot = other.lastPivot();

				if (pivot == otherPivot) {
					final Pair<RationalVector, RationalVector> pair =
							CongruenceUtil.hermitEliminateField(other, congruence, pivot);
					congruences.set(j, pair.getFirst());
					congruences.set(i, pair.getSecond());
				}
			}
		}

		// Scan for empty congruence's
		for (int i = 0; i < congruences.size(); i++) {
			final RationalVector congruence = congruences.get(i);
			final long pivot = congruence.lastPivot();

			if (pivot == -1) {
				// parameter is empty, can be deleted
				congruencesToDelete.add(i);
			}
		}

		// Remove empty congruence's
		for (final int i : congruencesToDelete.reversed()) {
			congruences.remove(i);
		}

		// Make pivot values for congruence's positive
		for (int i = 0; i < congruences.size(); i++) {
			RationalVector congruence = congruences.get(i);
			final int pivot = congruence.lastPivot();
			final var pivotValue = congruence.get(pivot);

			if (pivotValue.compareTo(Rational.ZERO) < 0) {
				congruence = congruence.negate();
				congruences.set(i, congruence);
			}
		}

		mEqualities = equalities;
		mCongruences = congruences;
		mIsMinimal = true;

		if (equalities.size() + congruences.size() > mVectorLength) {
			throw new AssertionError("equalities and congruences are too long\n Equalities: " + mEqualities
					+ "\n Congruences: " + mCongruences);
		}
	}

	/**
	 * Converts the representation to be in strong minimal form. In strong minimal form the representation is minimal
	 * and for each pair of distinct congruence vectors v, u it holds that -v_k < 2*u_k ≤ v_k for k being the index of
	 * the last non zero entry of v.
	 */
	public void stronglyMinimize() {
		if (isStrongMinimal()) {
			return;
		}
		minimize();

		final List<RationalVector> equalities = getEqualities();
		final List<RationalVector> congruences = new ArrayList<>(getCongruences());
		// Sorting the congruence's by last pivot is needed for the rest
		congruences.sort((v1, v2) -> (v1.lastPivot() < v2.lastPivot()) ? 1 : -1);

		for (int i = 0; i < congruences.size(); i++) {
			for (int j = 0; j < congruences.size(); j++) {
				if (i == j) {
					continue;
				}
				final RationalVector congruence = congruences.get(i);
				final RationalVector other = congruences.get(j);
				final int index = other.lastPivot();

				final Rational indexValue = congruence.get(index);
				final Rational otherIndexValue = other.get(index);
				final Rational indexValue2 = indexValue.mul(BigInteger.TWO);

				if (indexValue2.compareTo(otherIndexValue.negate()) <= 0
						|| indexValue2.compareTo(otherIndexValue) > 0) {
					final RationalVector v1 = congruence;
					final RationalVector v2 = other;

					final BigInteger congruenceDenominator = CongruenceUtil.getCommonDenominator(congruence);
					final BigInteger otherDenominator = CongruenceUtil.getCommonDenominator(other);
					final BigInteger commonDenominator = CongruenceUtil.lcm(congruenceDenominator, otherDenominator);
					final Rational commonDenominatorRational = Rational.valueOf(commonDenominator, BigInteger.ONE);

					final RationalVector wholeV1 = v1.multiply(commonDenominatorRational);
					final RationalVector wholeV2 = v2.multiply(commonDenominatorRational);

					final Rational wholeIndexElement1Rational = wholeV1.get(index);
					final Rational wholeIndexElement2Rational = wholeV2.get(index);
					final BigInteger wholeIndexElement1 = wholeIndexElement1Rational.numerator();
					final BigInteger wholeIndexElement2 = wholeIndexElement2Rational.numerator();

					BigInteger factor;
					final BigInteger e1ModE2Times2 =
							wholeIndexElement1.mod(wholeIndexElement2).multiply(BigInteger.TWO);

					final BigInteger[] divideAndRemainder = wholeIndexElement1.divideAndRemainder(wholeIndexElement2);
					final BigInteger divide = divideAndRemainder[0];
					final BigInteger remainder = divideAndRemainder[1];

					if (e1ModE2Times2.compareTo(wholeIndexElement1) > 0) {
						if (remainder.equals(BigInteger.ZERO)) {
							factor = divide;
						} else {
							factor = divide.add(BigInteger.ONE);
						}
					} else {
						factor = divide;
					}

					final RationalVector newWholeV1 = wholeV1.subtract(wholeV2.multiply(factor));
					final RationalVector newCongruence = newWholeV1.divide(commonDenominatorRational);
					congruences.set(i, newCongruence);
				}

			}
		}
		mEqualities = equalities;
		mCongruences = congruences;
		mIsStrongMinimal = true;
	}

	/**
	 * Returns an equivalent {@link GeneratorRepresentation}.
	 */
	public GeneratorRepresentation computeGeneratorRepresentation() {
		minimize();
		final List<RationalVector> equalities = getEqualities();
		final List<RationalVector> congruences = getCongruences();
		final int congruencesNum = congruences.size();

		final List<RationalVector> constraintList = new ArrayList<>(congruences);
		constraintList.addAll(equalities);

		final Set<Integer> missingPivots = IntStream.range(0, mVectorLength).boxed().collect(Collectors.toSet());
		for (final RationalVector vector : constraintList) {
			missingPivots.remove(vector.lastPivot());
		}

		final List<RationalVector> fillerList = new ArrayList<>();
		for (final Integer missingPivot : missingPivots) {
			fillerList.add(RationalVector.getUnitVector(missingPivot, mVectorLength));
		}
		final int fillerNum = fillerList.size();

		final List<RationalVector> vectorList = new ArrayList<>(fillerList);
		vectorList.addAll(constraintList);
		final RationalMatrix constraintMatrix = RationalMatrix.fromRowVectors(vectorList, mVectorLength);

		if (!constraintMatrix.isSquare()) {
			throw new AssertionError("constraintMatrix is not square. \n constraintMatrix: \n" + constraintMatrix);
		}

		final RationalMatrix generatorMatrix = constraintMatrix.invert().transpose();
		final List<RationalVector> generatorList = generatorMatrix.getRowVectors();

		final List<RationalVector> lines = generatorList.subList(0, fillerNum);
		final List<RationalVector> parameters = generatorList.subList(fillerNum, fillerNum + congruencesNum);

		return new GeneratorRepresentation(lines, parameters, mVectorLength, true);
	}
}
