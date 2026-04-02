package de.uni_freiburg.informatik.ultimate.lib.sifa.test;

import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;
import org.ojalgo.matrix.MatrixQ128;
import org.ojalgo.scalar.RationalNumber;

import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence.CongruenceUtil;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence.GeneratorRepresentation;
import de.uni_freiburg.informatik.ultimate.logic.Rational;

public class GeneratorRepresentationTest {
	List<GeneratorRepresentation> TEST_GENERATORS = List.of(getGenerators1(), getGenerators2(), getGenerators3(),
			getGenerators4());

	public GeneratorRepresentation getGenerators1() {
		// @formatter:off
		/*
		 * L = {(1, 1, 0, 0, 0), (1, 1, 1, 0, 0)}
		 * Q = {}
		 */
		// @formatter:on
		final List<MatrixQ128> lines = new ArrayList<>();
		lines.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 1, 0, 0, 0)));
		lines.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 1, 0, 0, 0)));
		lines.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 1, 1, 0, 0)));

		final List<MatrixQ128> parameters = new ArrayList<>();

		return new GeneratorRepresentation(lines, parameters);
	}

	public GeneratorRepresentation getGenerators2() {
		// @formatter:off
		/*
		 * L = {}
		 * Q = {(0, 1, 1, -2, 0), (0, 0, 0, 0, 1)}
		 */
		// @formatter:on
		final List<MatrixQ128> lines = new ArrayList<>();

		final List<MatrixQ128> parameters = new ArrayList<>();
		parameters.add(CongruenceUtil.getRowVectorFromIntList(List.of(0, 1, 1, -2, 0)));
		parameters.add(CongruenceUtil.getRowVectorFromIntList(List.of(0, 0, 0, 0, 1)));

		return new GeneratorRepresentation(lines, parameters);
	}

	public GeneratorRepresentation getGenerators3() {
		// @formatter:off
		/*
		 * L = {(1, 1, 0, 0, 0), (1, 1, 1, 0, 0)}
		 * Q = {(0, 1, 1, -2, 0), (0, 0, 0, 0, 1)}
		 */
		// @formatter:on
		final List<MatrixQ128> lines = new ArrayList<>();
		lines.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 1, 0, 0, 0)));
		lines.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 1, 0, 0, 0)));
		lines.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 1, 1, 0, 0)));

		final List<MatrixQ128> parameters = new ArrayList<>();
		parameters.add(CongruenceUtil.getRowVectorFromIntList(List.of(0, 1, 1, -2, 0)));
		parameters.add(CongruenceUtil.getRowVectorFromIntList(List.of(0, 0, 0, 0, 1)));

		return new GeneratorRepresentation(lines, parameters);
	}

	public GeneratorRepresentation getGenerators4() {
		// @formatter:off
		/*
		 * L = {(1, 0, 2, 0, 0), (1, 1, 0, 0, 0)}
		 * Q = {(0, 1, 1, -2, 0), (0, 0, 0, 0, 1)}
		 */
		// @formatter:on
		final List<MatrixQ128> lines = new ArrayList<>();
		lines.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 0, 2, 0, 0)));
		lines.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 1, 0, 0, 0)));

		final List<MatrixQ128> parameters = new ArrayList<>();
		parameters.add(CongruenceUtil.getRowVectorFromIntList(List.of(0, 1, 1, -2, 0)));
		parameters.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 1, 0, 0, 0)));
		parameters.add(CongruenceUtil.getRowVectorFromIntList(List.of(0, 0, 0, 0, 1)));

		return new GeneratorRepresentation(lines, parameters);
	}

	public GeneratorRepresentation getGenerators5() {
		// @formatter:off
		/*
		 * L = {}
		 * Q = {(0, 1/2, 4), (2, 4/3, 5), (7, 13/7, 1/3)}
		 */
		// @formatter:on
		final List<MatrixQ128> lines = new ArrayList<>();

		final List<MatrixQ128> parameters = new ArrayList<>();
		parameters.add(CongruenceUtil
				.getRowVectorFromRationalList(List.of(Rational.ZERO, Rational.valueOf(1, 2), Rational.valueOf(4, 1))));
		parameters.add(CongruenceUtil
				.getRowVectorFromRationalList(List.of(Rational.TWO, Rational.valueOf(4, 3), Rational.valueOf(5, 1))));
		parameters.add(CongruenceUtil.getRowVectorFromRationalList(
				List.of(Rational.valueOf(7, 1), Rational.valueOf(13, 7), Rational.valueOf(1, 3))));

		return new GeneratorRepresentation(lines, parameters);
	}

	@Test
	public void testGetMinimalForm() {
		for (final GeneratorRepresentation generators : TEST_GENERATORS) {
			final var minimalGenerators = generators.getMinimalForm();
			// System.out.println(generators);
			// System.out.println(minimalGenerators);
			Assert.assertTrue(hasMinimalForm(minimalGenerators));
		}
	}

	public boolean hasMinimalForm(final GeneratorRepresentation generators) {
		if (!generators.isMinimal()) {
			return false;
		}

		final List<MatrixQ128> lines = generators.getLines();
		final List<MatrixQ128> parameters = generators.getParameters();

		final List<MatrixQ128> vectors = new ArrayList<>(lines);
		vectors.addAll(parameters);

		for (int i = 0; i < vectors.size(); i++) {
			final var vector = vectors.get(i);
			final var pivot = CongruenceUtil.firstPivot(vector);
			final var pivotValue = vector.get(0, pivot);

			if (pivotValue.compareTo(RationalNumber.ZERO) < 0) {
				return false;
			}
			for (int j = i + 1; j < vectors.size(); j++) {
				final var other = vectors.get(j);
				if (pivot == CongruenceUtil.firstPivot(other)) {
					return false;
				}
			}
		}
		return true;
	}

}
