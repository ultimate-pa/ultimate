package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.ojalgo.matrix.MatrixQ128;
import org.ojalgo.scalar.RationalNumber;

public class ConstraintRepresentation {
	public static ConstraintRepresentation EMPTY = new ConstraintRepresentation(List.of(), List.of(), true, true);

	final private MatrixQ128 mEqualityMatrix;
	final private MatrixQ128 mCongruenceMatrix;

	private final ConstraintRepresentation mMinimalRepresenation;
	private final ConstraintRepresentation mStrongMinimalRepresenation;

	final private boolean mIsMinimal;
	final private boolean mIsStrongMinimal;

	public ConstraintRepresentation(final List<MatrixQ128> equalities, final List<MatrixQ128> congruences) {
		// TODO: Maybe make Equalities and Congruences non final IFF minimal and strong
		// minimal is equivalent
		mEqualityMatrix = CongruenceUtil.getMatrixFromRows(equalities);
		mCongruenceMatrix = CongruenceUtil.getMatrixFromRows(congruences);
		mIsMinimal = false;
		mIsStrongMinimal = false;
		mMinimalRepresenation = null;
		mStrongMinimalRepresenation = null;
	}

	private ConstraintRepresentation(final List<MatrixQ128> equalities, final List<MatrixQ128> congruences,
			final boolean isMinimal, final boolean isStrongMinimal) {
		mEqualityMatrix = CongruenceUtil.getMatrixFromRows(equalities);
		mCongruenceMatrix = CongruenceUtil.getMatrixFromRows(congruences);
		mIsMinimal = isMinimal;
		mIsStrongMinimal = isStrongMinimal;
		mMinimalRepresenation = null;
		mStrongMinimalRepresenation = null;
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

	public boolean isUnsat() {
		final ConstraintRepresentation minimalConstraints = getMinimalForm();
		final List<MatrixQ128> equalities = minimalConstraints.getEqualities();
		final List<MatrixQ128> congruences = minimalConstraints.getCongruences();

		if (equalities.size() == 1 && congruences.size() == 0) {
			final var equality = equalities.get(0);

			if (equality.equals(ConstraintRepresentation.unsatVector(equality.size()))) {
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

	public ConstraintRepresentation getMinimalForm() {
		// TODO: Fix to properly work
		if (mIsMinimal) {
			return this;
		}

		final List<MatrixQ128> equalities = getEqualities();
		final List<MatrixQ128> congruences = getCongruences();

		final List<Integer> equalitiesToDelete = new ArrayList<>();
		final List<Integer> congruencesToDelete = new ArrayList<>();

		// Making the equality pivots unique
		for (int i = 0; i < equalities.size(); i++) {
			final MatrixQ128 equality = equalities.get(i);
			final long pivot = CongruenceUtil.lastPivot(equality);

			if (pivot == -1) {
				// vector is empty, can be deleted
				equalitiesToDelete.add(i);
			} else if (pivot == 0) {
				// equality is unsatisfiable and so is the whole system
				return new ConstraintRepresentation(List.of(unsatVector(equality.size())), List.of(), true, true);

			} else {
				// Make pivotValue positive
				final RationalNumber pivotValue = equality.get(0, pivot);
				if (pivotValue.compareTo(RationalNumber.ZERO) < 0) {
					equalities.set(i, equality.multiply((-1)));
				}

				// Eliminate the pivot field from the following equalities
				for (int j = i + 1; j < equalities.size(); j++) {
					final MatrixQ128 other = equalities.get(j);
					equalities.set(j, CongruenceUtil.eliminateField(other, equality, pivot));
				}

				// Eliminate the pivot field from the following congruence's
				for (int j = 0; j < congruences.size(); j++) {
					final MatrixQ128 other = congruences.get(j);
					congruences.set(j, CongruenceUtil.eliminateField(other, equality, pivot));
				}

			}
		}

		// Making the congruence pivots unique
		for (int i = 0; i < congruences.size(); i++) {
			final MatrixQ128 congruence = congruences.get(i);
			final long pivot = CongruenceUtil.lastPivot(congruence);

			if (pivot == -1) {
				// vector is empty, can be deleted
				congruencesToDelete.add(i);
			} else if (pivot == 0 && CongruenceUtil.getDenominator(congruence.get(0, pivot)) == 1) {
				// congruence is unsatisfiable and so is the whole system
				// First entry has to be 0 modulo 1 which is exactly the case when the
				// pivotValue is a whole number
				return new ConstraintRepresentation(List.of(unsatVector(congruence.size())), List.of(), true, true);
			} else {
				// Make pivotValue positive
				final var pivotValue = congruence.get(0, pivot);
				if (CongruenceUtil.getNumerator(pivotValue) < 0) {
					congruences.set(i, congruence.multiply((-1)));
				}

				// Eliminate the pivot field from the following congruence's
				// We can't eliminate it from the equalities, since adding a congruence to an
				// equality doesn't conserve the equality
				for (int j = i + 1; j < congruences.size(); j++) {
					final MatrixQ128 other = congruences.get(j);
					congruences.set(j, CongruenceUtil.eliminateField(other, congruence, pivot));
				}
			}
		}
		for (final int i : equalitiesToDelete.reversed()) {
			equalities.remove(i);
		}
		for (final int i : congruencesToDelete.reversed()) {
			congruences.remove(i);
		}

		return new ConstraintRepresentation(equalities, congruences, true, false);
	}

	public ConstraintRepresentation getStrongMinimalForm() {
		// TODO: Fix to properly work
		if (isStrongMinimal()) {
			return this;
		}

		final ConstraintRepresentation minimalConstraints = getMinimalForm();

		final List<MatrixQ128> equalities = minimalConstraints.getEqualities();
		final List<MatrixQ128> congruences = minimalConstraints.getCongruences();

		for (int i = congruences.size() - 1; i >= 0; i--) {
			final MatrixQ128 congruence = congruences.get(i);
			final long pivot = CongruenceUtil.lastPivot(congruence);

			for (int j = i - 1; j >= 0; j--) {
				final MatrixQ128 other = congruences.get(j);
				congruences.set(j, CongruenceUtil.eliminateField(other, congruence, pivot));
			}
		}
		return new ConstraintRepresentation(equalities, congruences, true, true);
	}

	public GeneratorRepresentation computeGeneratorRepresentation() {
		// TODO
		return null;
	}
}
