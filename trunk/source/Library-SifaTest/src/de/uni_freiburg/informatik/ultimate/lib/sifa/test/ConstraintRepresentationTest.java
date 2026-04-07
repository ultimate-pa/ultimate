package de.uni_freiburg.informatik.ultimate.lib.sifa.test;

import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;
import org.ojalgo.matrix.MatrixQ128;
import org.ojalgo.scalar.RationalNumber;

import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence.CongruenceUtil;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence.ConstraintRepresentation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence.GeneratorRepresentation;
import de.uni_freiburg.informatik.ultimate.logic.Rational;

public class ConstraintRepresentationTest {
	public List<ConstraintRepresentation> getTestConstraints() {
		return List.of(getConstraints1(), getConstraints2(), getConstraints3(), getConstraints4(), getConstraints5(),
				getConstraints6(), getConstraints7(), getConstraints8(), getConstraints9(), getConstraints10(),
				getConstraints11(), getConstraints12());
	}

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

		return new ConstraintRepresentation(equalities, congruences, 5);
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

		return new ConstraintRepresentation(equalities, congruences, 5);
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

		return new ConstraintRepresentation(equalities, congruences, 5);
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

		return new ConstraintRepresentation(equalities, congruences, 5);
	}

	public ConstraintRepresentation getConstraints5() {
		// @formatter:off
		/*
		 * x1 = 0 [2]
		 * x1 + x2 = 0 [3]
		 */
		// @formatter:on
		final List<MatrixQ128> equalities = new ArrayList<>();

		final List<MatrixQ128> congruences = new ArrayList<>();
		congruences.add(CongruenceUtil
				.getRowVectorFromRationalList(List.of(Rational.ZERO, Rational.valueOf(1, 2), Rational.ZERO)));
		congruences.add(CongruenceUtil
				.getRowVectorFromRationalList(List.of(Rational.ZERO, Rational.valueOf(1, 3), Rational.valueOf(1, 3))));

		return new ConstraintRepresentation(equalities, congruences, 3);
	}

	public ConstraintRepresentation getConstraints6() {
		// @formatter:off
		/*
		 * 1 = 0 [2]
		 */
		// @formatter:on
		final List<MatrixQ128> equalities = new ArrayList<>();

		final List<MatrixQ128> congruences = new ArrayList<>();
		congruences.add(CongruenceUtil.getRowVectorFromRationalList(List.of(Rational.ONE, Rational.ZERO)));

		return new ConstraintRepresentation(equalities, congruences, 2);
	}

	public ConstraintRepresentation getConstraints7() {
		// @formatter:off
		/*
		 * x1 - x2 = 0 [2]
		 * x1 + x2 = 0 [3]
		 * x1 + x2 + 2*x3 = 1 [5]
		 */
		// @formatter:on
		final List<MatrixQ128> equalities = new ArrayList<>();

		final List<MatrixQ128> congruences = new ArrayList<>();
		congruences.add(CongruenceUtil.getRowVectorFromRationalList(
				List.of(Rational.ZERO, Rational.valueOf(1, 2), Rational.valueOf(-1, 2), Rational.ZERO)));
		congruences.add(CongruenceUtil.getRowVectorFromRationalList(
				List.of(Rational.ZERO, Rational.valueOf(1, 3), Rational.valueOf(1, 3), Rational.ZERO)));
		congruences.add(CongruenceUtil.getRowVectorFromRationalList(List.of(Rational.valueOf(-1, 5),
				Rational.valueOf(1, 5), Rational.valueOf(1, 5), Rational.valueOf(2, 5))));

		return new ConstraintRepresentation(equalities, congruences, 4);
	}

	public ConstraintRepresentation getConstraints8() {
		// @formatter:off
		/*
		 * x1 = 1 [2]
		 */
		// @formatter:on
		final List<MatrixQ128> equalities = new ArrayList<>();

		final List<MatrixQ128> congruences = new ArrayList<>();
		congruences.add(
				CongruenceUtil.getRowVectorFromRationalList(List.of(Rational.valueOf(-1, 2), Rational.valueOf(1, 2))));

		return new ConstraintRepresentation(equalities, congruences, 2);
	}

	public ConstraintRepresentation getConstraints9() {
		// @formatter:off
		/*
		 * 0 = -1
		 */
		// @formatter:on
		final List<MatrixQ128> equalities = new ArrayList<>();
		equalities.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 0)));

		final List<MatrixQ128> congruences = new ArrayList<>();

		return new ConstraintRepresentation(equalities, congruences, 2);
	}

	public ConstraintRepresentation getConstraints10() {
		// @formatter:off
		/*
		 * No constraints
		 */
		// @formatter:on
		final List<MatrixQ128> equalities = new ArrayList<>();

		final List<MatrixQ128> congruences = new ArrayList<>();

		return new ConstraintRepresentation(equalities, congruences, 2);
	}

	public ConstraintRepresentation getConstraints11() {
		// @formatter:off
		/*
		 * 2*x1 + 3*x2 = 4 [10]
		 */
		// @formatter:on
		final List<MatrixQ128> equalities = new ArrayList<>();

		final List<MatrixQ128> congruences = new ArrayList<>();
		congruences.add(CongruenceUtil.getRowVectorFromRationalList(
				List.of(Rational.valueOf(-4, 10), Rational.valueOf(2, 10), Rational.valueOf(3, 10))));

		return new ConstraintRepresentation(equalities, congruences, 3);
	}

	public ConstraintRepresentation getConstraints12() {
		// @formatter:off
		/*
		 * x1 = 1
		 * x1 + x2 = 2 [3]
		 */
		// @formatter:on
		final List<MatrixQ128> equalities = new ArrayList<>();
		equalities.add(CongruenceUtil
				.getRowVectorFromRationalList(List.of(Rational.valueOf(-1, 1), Rational.ONE, Rational.ZERO)));

		final List<MatrixQ128> congruences = new ArrayList<>();
		congruences.add(CongruenceUtil.getRowVectorFromRationalList(
				List.of(Rational.valueOf(-2, 3), Rational.valueOf(1, 3), Rational.valueOf(1, 3))));

		return new ConstraintRepresentation(equalities, congruences, 3);
	}

	@Test
	public void testGetMinimalForm() {
		for (final ConstraintRepresentation constraints : getTestConstraints()) {
			// System.out.println("-----------------------");
			// System.out.println("constraints: " + constraints);
			constraints.minimize();
			// System.out.println("constraints: " + constraints);
			// System.out.println(hasMinimalForm(constraints));
			Assert.assertTrue(hasMinimalForm(constraints));
		}
	}

	@Test
	public void testIsUnsat() {
		Assert.assertFalse(getConstraints1().isUnsat());
		Assert.assertTrue(getConstraints2().isUnsat());
		Assert.assertTrue(getConstraints3().isUnsat());
		Assert.assertFalse(getConstraints4().isUnsat());
		Assert.assertFalse(getConstraints5().isUnsat());
		Assert.assertTrue(getConstraints6().isUnsat());
	}

	@Test
	public void testGetStrongMinimalForm() {
		// Add more tests for this
		for (final ConstraintRepresentation constraints : getTestConstraints()) {
			constraints.stronglyMinimize();
			// System.out.println(constraints);
			// System.out.println(constraints.getMinimalForm());
			// System.out.println(strongMinimalConstraints);
			Assert.assertTrue(hasStrongMinimalForm(constraints));
		}
	}

	@Test
	public void testComputeGeneratorRepresentation() {
		final List<ConstraintRepresentation> constraints = List.of(getConstraints8(), getConstraints9(),
				getConstraints10(), getConstraints11(), getConstraints12());
		final List<GeneratorRepresentation> generators = List.of(GeneratorRepresentationTest.getGenerators8(),
				GeneratorRepresentationTest.getGenerators9(), GeneratorRepresentationTest.getGenerators10(),
				GeneratorRepresentationTest.getGenerators11(), GeneratorRepresentationTest.getGenerators12());

		for (int i = 0; i < constraints.size(); i++) {
			final GeneratorRepresentation expected = generators.get(i);
			final GeneratorRepresentation result = constraints.get(i).computeGeneratorRepresentation();
			// System.out.println(expected);
			// System.out.println(result);
			Assert.assertTrue(expected.equals(result));
		}
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

	public boolean hasStrongMinimalForm(final ConstraintRepresentation constraints) {
		if (!hasMinimalForm(constraints)) {
			return false;
		}

		if (!constraints.isStrongMinimal()) {
			return false;
		}

		final List<MatrixQ128> congruences = constraints.getCongruences();

		for (int i = 0; i < congruences.size(); i++) {
			final MatrixQ128 congruence = congruences.get(i);
			final long pivot = CongruenceUtil.lastPivot(congruence);
			final RationalNumber pivotElement = congruence.get(0, pivot);

			for (int j = 0; j < congruences.size(); j++) {
				if (i == j) {
					continue;
				}
				final MatrixQ128 other = congruences.get(j);
				final RationalNumber otherElement = other.get(0, pivot);
				final RationalNumber otherElement2 = otherElement.multiply(RationalNumber.TWO);

				// Test if: -pivotElement < 2 * otherElement <= pivotElement
				if (!(pivotElement.negate().compareTo(otherElement2) < 0)) {
					return false;
				}
				if (!(otherElement2.compareTo(pivotElement) <= 0)) {
					return false;
				}

			}
		}
		return true;
	}

}
