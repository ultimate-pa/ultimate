package de.uni_freiburg.informatik.ultimate.lib.sifa.test;

import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence.ConstraintRepresentation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence.GeneratorRepresentation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence.RationalVector;
import de.uni_freiburg.informatik.ultimate.logic.Rational;

public class GeneratorRepresentationTest {
	public List<GeneratorRepresentation> getTestGenerators() {
		return List.of(getGenerators1(), getGenerators2(), getGenerators3(), getGenerators4(), getGenerators5(),
				getGenerators8(), getGenerators9(), getGenerators10(), getGenerators11(), getGenerators12(),
				getGenerators13(), getGenerators14());
	}

	public GeneratorRepresentation getGenerators1() {
		// @formatter:off
		/*
		 * L = {(1, 1, 0, 0, 0), (1, 1, 1, 0, 0)}
		 * Q = {}
		 */
		// @formatter:on
		final List<RationalVector> lines = new ArrayList<>();
		lines.add(RationalVector.fromIntList(List.of(1, 1, 0, 0, 0)));
		lines.add(RationalVector.fromIntList(List.of(1, 1, 0, 0, 0)));
		lines.add(RationalVector.fromIntList(List.of(1, 1, 1, 0, 0)));

		final List<RationalVector> parameters = new ArrayList<>();

		return new GeneratorRepresentation(lines, parameters, 5);
	}

	public GeneratorRepresentation getGenerators2() {
		// @formatter:off
		/*
		 * L = {}
		 * Q = {(0, 1, 1, -2, 0), (0, 0, 0, 0, 1)}
		 */
		// @formatter:on
		final List<RationalVector> lines = new ArrayList<>();

		final List<RationalVector> parameters = new ArrayList<>();
		parameters.add(RationalVector.fromIntList(List.of(0, 1, 1, -2, 0)));
		parameters.add(RationalVector.fromIntList(List.of(0, 0, 0, 0, 1)));

		return new GeneratorRepresentation(lines, parameters, 5);
	}

	public GeneratorRepresentation getGenerators3() {
		// @formatter:off
		/*
		 * L = {(1, 1, 0, 0, 0), (1, 1, 1, 0, 0)}
		 * Q = {(0, 1, 1, -2, 0), (0, 0, 0, 0, 1)}
		 */
		// @formatter:on
		final List<RationalVector> lines = new ArrayList<>();
		lines.add(RationalVector.fromIntList(List.of(1, 1, 0, 0, 0)));
		lines.add(RationalVector.fromIntList(List.of(1, 1, 0, 0, 0)));
		lines.add(RationalVector.fromIntList(List.of(1, 1, 1, 0, 0)));

		final List<RationalVector> parameters = new ArrayList<>();
		parameters.add(RationalVector.fromIntList(List.of(0, 1, 1, -2, 0)));
		parameters.add(RationalVector.fromIntList(List.of(0, 0, 0, 0, 1)));

		return new GeneratorRepresentation(lines, parameters, 5);
	}

	public GeneratorRepresentation getGenerators4() {
		// @formatter:off
		/*
		 * L = {(1, 0, 2, 0, 0), (1, 1, 0, 0, 0)}
		 * Q = {(0, 1, 1, -2, 0), (0, 0, 0, 0, 1)}
		 */
		// @formatter:on
		final List<RationalVector> lines = new ArrayList<>();
		lines.add(RationalVector.fromIntList(List.of(1, 0, 2, 0, 0)));
		lines.add(RationalVector.fromIntList(List.of(1, 1, 0, 0, 0)));

		final List<RationalVector> parameters = new ArrayList<>();
		parameters.add(RationalVector.fromIntList(List.of(0, 1, 1, -2, 0)));
		parameters.add(RationalVector.fromIntList(List.of(1, 1, 0, 0, 0)));
		parameters.add(RationalVector.fromIntList(List.of(0, 0, 0, 0, 1)));

		return new GeneratorRepresentation(lines, parameters, 5);
	}

	public GeneratorRepresentation getGenerators5() {
		// @formatter:off
		/*
		 * L = {}
		 * Q = {(0, 1/2, 4), (2, 4/3, 5), (7, 13/7, 1/3)}
		 */
		// @formatter:on
		final List<RationalVector> lines = new ArrayList<>();

		final List<RationalVector> parameters = new ArrayList<>();
		parameters.add(new RationalVector(List.of(Rational.ZERO, Rational.valueOf(1, 2), Rational.valueOf(4, 1))));
		parameters.add(new RationalVector(List.of(Rational.TWO, Rational.valueOf(4, 3), Rational.valueOf(5, 1))));
		parameters.add(
				new RationalVector(List.of(Rational.valueOf(7, 1), Rational.valueOf(13, 7), Rational.valueOf(1, 3))));

		return new GeneratorRepresentation(lines, parameters, 3);
	}

	public static GeneratorRepresentation getGenerators8() {
		// @formatter:off
		/*
		 * L = {(1, 1)}
		 * Q = {(0, 2)}
		 */
		// @formatter:on
		final List<RationalVector> equalities = new ArrayList<>();
		equalities.add(new RationalVector(List.of(Rational.ONE, Rational.ONE)));

		final List<RationalVector> congruences = new ArrayList<>();
		congruences.add(new RationalVector(List.of(Rational.ZERO, Rational.TWO)));

		return new GeneratorRepresentation(equalities, congruences, 2);
	}

	public static GeneratorRepresentation getGenerators9() {
		// @formatter:off
		/*
		 * L = {(0, 1)}
		 * Q = {}
		 */
		// @formatter:on
		final List<RationalVector> equalities = new ArrayList<>();
		equalities.add(new RationalVector(List.of(Rational.ZERO, Rational.ONE)));

		final List<RationalVector> congruences = new ArrayList<>();

		return new GeneratorRepresentation(equalities, congruences, 2);
	}

	public static GeneratorRepresentation getGenerators10() {
		// @formatter:off
		/*
		 * L = {(1, 0), (0, 1)}
		 * Q = {}
		 */
		// @formatter:on
		final List<RationalVector> equalities = new ArrayList<>();
		equalities.add(new RationalVector(List.of(Rational.ONE, Rational.ZERO)));
		equalities.add(new RationalVector(List.of(Rational.ZERO, Rational.ONE)));

		final List<RationalVector> congruences = new ArrayList<>();

		return new GeneratorRepresentation(equalities, congruences, 2);
	}

	public static GeneratorRepresentation getGenerators11() {
		// @formatter:off
		/*
		 * L = {(1, 0, 4/3), (0, 1, -2/3)}
		 * Q = {(0, 0, 10/3)}
		 */
		// @formatter:on
		final List<RationalVector> equalities = new ArrayList<>();
		equalities.add(new RationalVector(List.of(Rational.ONE, Rational.ZERO, Rational.valueOf(4, 3))));
		equalities.add(new RationalVector(List.of(Rational.ZERO, Rational.ONE, Rational.valueOf(-2, 3))));

		final List<RationalVector> congruences = new ArrayList<>();
		congruences.add(new RationalVector(List.of(Rational.ZERO, Rational.ZERO, Rational.valueOf(10, 3))));

		return new GeneratorRepresentation(equalities, congruences, 3);
	}

	public static GeneratorRepresentation getGenerators12() {
		// @formatter:off
		/*
		 * L = {(1, 1, 1)}
		 * Q = {(0, 0, 3)}
		 */
		// @formatter:on
		final List<RationalVector> equalities = new ArrayList<>();
		equalities.add(new RationalVector(List.of(Rational.ONE, Rational.ONE, Rational.ONE)));

		final List<RationalVector> congruences = new ArrayList<>();
		congruences.add(new RationalVector(List.of(Rational.ZERO, Rational.ZERO, Rational.valueOf(3, 1))));

		return new GeneratorRepresentation(equalities, congruences, 3);
	}

	public static GeneratorRepresentation getGenerators13() {
		// @formatter:off
		/*
		 * L = {}
		 * Q = {}
		 */
		// @formatter:on
		final List<RationalVector> equalities = new ArrayList<>();

		final List<RationalVector> congruences = new ArrayList<>();

		return new GeneratorRepresentation(equalities, congruences, 3);
	}

	public static GeneratorRepresentation getGenerators14() {
		// @formatter:off
		/*
		 * L = {}
		 * Q = {(0, 4/3, 0), (1, 0, 1), (0, 2, 1), (1, 0, -1)}
		 */
		// @formatter:on
		final List<RationalVector> equalities = new ArrayList<>();

		final List<RationalVector> congruences = new ArrayList<>();
		congruences.add(new RationalVector(List.of(Rational.ZERO, Rational.valueOf(4, 3), Rational.ZERO)));
		congruences.add(RationalVector.fromIntList(List.of(1, 0, 1)));
		congruences.add(RationalVector.fromIntList(List.of(0, 2, 1)));
		congruences.add(RationalVector.fromIntList(List.of(1, 0, -1)));

		return new GeneratorRepresentation(equalities, congruences, 3);
	}

	@Test
	public void testMinimize() {
		for (final GeneratorRepresentation generators : getTestGenerators()) {
			// System.out.println(generators);
			generators.minimize();
			// System.out.println(generators);
			Assert.assertTrue(hasMinimalForm(generators));
		}
	}

	@Test
	public void testComputeConstraintRepresentation() {
		final List<ConstraintRepresentation> constraints = List.of(ConstraintRepresentationTest.getConstraints8(),
				ConstraintRepresentationTest.getConstraints9(), ConstraintRepresentationTest.getConstraints10(),
				ConstraintRepresentationTest.getConstraints11(), ConstraintRepresentationTest.getConstraints12(),
				ConstraintRepresentationTest.getConstraints13());
		final List<GeneratorRepresentation> generators = List.of(getGenerators8(), getGenerators9(), getGenerators10(),
				getGenerators11(), getGenerators12(), getGenerators13());

		for (int i = 0; i < constraints.size(); i++) {
			System.out.println("------------------------");
			System.out.println(i);

			final ConstraintRepresentation expected = constraints.get(i);
			expected.minimize();
			final ConstraintRepresentation result = generators.get(i).computeConstraintRepresentation();
			System.out.println(expected);
			System.out.println(result);
			Assert.assertEquals(expected, result);
		}
	}

	public boolean hasMinimalForm(final GeneratorRepresentation generators) {
		if (!generators.isMinimal()) {
			return false;
		}

		final List<RationalVector> lines = generators.getLines();
		final List<RationalVector> parameters = generators.getParameters();

		final List<RationalVector> vectors = new ArrayList<>(lines);
		vectors.addAll(parameters);

		for (int i = 0; i < vectors.size(); i++) {
			final var vector = vectors.get(i);
			final var pivot = vector.firstPivot();
			final var pivotValue = vector.get(pivot);

			if (pivotValue.compareTo(Rational.ZERO) < 0) {
				return false;
			}
			for (int j = i + 1; j < vectors.size(); j++) {
				final var other = vectors.get(j);
				if (pivot == other.firstPivot()) {
					return false;
				}
			}
		}
		return true;
	}

}
