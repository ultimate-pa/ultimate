package de.uni_freiburg.informatik.ultimate.lib.sifa.test;

import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;
import org.ojalgo.matrix.MatrixQ128;

import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence.CongruenceUtil;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence.ConstraintRepresentation;
import de.uni_freiburg.informatik.ultimate.logic.Rational;

public class ConstraintRepresentationTest {
	List<ConstraintRepresentation> TEST_CONSTRAINTS = List.of(getConstraints1(), getConstraints2(), getConstraints3(),
			getConstraints4());

	public ConstraintRepresentation getConstraints1() {
		// @formatter:off
		/*
		 * x1 = -1
		 * x1 = -1
		 * x1 + x2 = -1
		 * x1 + x2 - 2*x3 = 0 [1]
		 * x4 = 0 [1]
		 */
		// @formatter:on
		final List<MatrixQ128> equalities = new ArrayList<>();
		equalities.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 1, 0, 0, 0)));
		equalities.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 1, 0, 0, 0)));
		equalities.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 1, 1, 0, 0)));

		final List<MatrixQ128> congruences = new ArrayList<>();
		congruences.add(CongruenceUtil.getRowVectorFromIntList(List.of(0, 1, 1, -2, 0)));
		congruences.add(CongruenceUtil.getRowVectorFromIntList(List.of(0, 0, 0, 0, 1)));

		return new ConstraintRepresentation(equalities, congruences);
	}

	public ConstraintRepresentation getConstraints2() {
		// @formatter:off
		/*
		 * x1 = -1
		 * x1 + x4 = -1
		 * x1 + x2 = -1
		 * x1 + x2 - 2*x3 = 0 [1]
		 * x4 = -1 [1]
		 */
		// @formatter:on

		final List<MatrixQ128> equalities = new ArrayList<>();
		equalities.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 1, 0, 0, 0)));
		equalities.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 1, 0, 0, 1)));
		equalities.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 1, 1, 0, 0)));

		final List<MatrixQ128> congruences = new ArrayList<>();
		congruences.add(CongruenceUtil.getRowVectorFromIntList(List.of(0, 1, 1, -2, 0)));
		congruences.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 0, 0, 0, 1)));

		return new ConstraintRepresentation(equalities, congruences);
	}

	public ConstraintRepresentation getConstraints3() {
		// @formatter:off
		/*
		 * x1 = -1
		 * x1 = 1
		 */
		// @formatter:on

		final List<MatrixQ128> equalities = new ArrayList<>();
		equalities.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 1, 0, 0, 0)));
		equalities.add(CongruenceUtil.getRowVectorFromIntList(List.of(-1, 1, 0, 0, 0)));

		final List<MatrixQ128> congruences = new ArrayList<>();

		return new ConstraintRepresentation(equalities, congruences);
	}

	public ConstraintRepresentation getConstraints4() {
		// @formatter:off
		/*
		 * x4 = 1 [2]
		 */
		// @formatter:on

		final List<MatrixQ128> equalities = new ArrayList<>();

		final List<MatrixQ128> congruences = new ArrayList<>();
		congruences.add(CongruenceUtil.getRowVectorFromRationalList(
				List.of(Rational.valueOf(-1, 2), Rational.ZERO, Rational.ZERO, Rational.ZERO, Rational.valueOf(1, 2))));

		return new ConstraintRepresentation(equalities, congruences);
	}

	@Test
	public void testGetMinimalForm() {
		for (final ConstraintRepresentation constraints : TEST_CONSTRAINTS) {
			final var minimalConstraints = constraints.getMinimalForm();
			// System.out.println(constraints);
			// System.out.println(minimalConstraints);
			Assert.assertTrue(hasMinimalForm(minimalConstraints));
		}
	}

	@Test
	public void testIsUnsat() {
		Assert.assertFalse(getConstraints1().isUnsat());
		Assert.assertTrue(getConstraints2().isUnsat());
		Assert.assertTrue(getConstraints3().isUnsat());
		Assert.assertFalse(getConstraints4().isUnsat());

	}

	public boolean hasMinimalForm(final ConstraintRepresentation constraints) {
		if (!constraints.isMinimal()) {
			return false;
		}

		final List<MatrixQ128> equalities = constraints.getEqualities();
		final List<MatrixQ128> congruences = constraints.getCongruences();

		// Check if it got set as unsatisfiable
		if (constraints.isUnsat()) {
			return true;
		}

		// Check the satisfiable case
		final List<MatrixQ128> vectors = new ArrayList<>(equalities);
		vectors.addAll(congruences);

		for (int i = 0; i < vectors.size(); i++) {
			final var vector = vectors.get(i);
			final var pivot = CongruenceUtil.lastPivot(vector);

			if (pivot == -1) {
				return false;
			}
			final var value = vector.get(0, pivot);
			if (CongruenceUtil.getNumerator(value) <= 0) {
				return false;
			}
			for (int j = i + 1; j < vectors.size(); j++) {
				final var other = vectors.get(j);
				if (pivot == CongruenceUtil.lastPivot(other)) {
					return false;
				}
			}
		}
		return true;
	}
}
