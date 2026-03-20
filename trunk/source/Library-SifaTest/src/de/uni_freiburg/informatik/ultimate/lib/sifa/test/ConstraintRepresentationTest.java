package de.uni_freiburg.informatik.ultimate.lib.sifa.test;

import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;
import org.ojalgo.matrix.MatrixQ128;

import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence.CongruenceUtil;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence.ConstraintRepresentation;

public class ConstraintRepresentationTest {
	@Test
	public void testGetMinimalForm() {
		final List<MatrixQ128> equalities1 = new ArrayList<>();
		equalities1.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 1, 0, 0, 0)));
		equalities1.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 1, 0, 0, 0)));
		equalities1.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 1, 1, 0, 0)));

		final List<MatrixQ128> congruences1 = new ArrayList<>();
		congruences1.add(CongruenceUtil.getRowVectorFromIntList(List.of(0, 1, 1, -2, 0)));
		congruences1.add(CongruenceUtil.getRowVectorFromIntList(List.of(0, 0, 0, 0, 1)));

		final var constraints1 = new ConstraintRepresentation(equalities1, congruences1, false, false);
		final var minimalConstraints1 = constraints1.getMinimalForm();
		// System.out.println(constraints1);
		// System.out.println(minimalConstraints1);

		Assert.assertTrue(hasMinimalForm(minimalConstraints1));

		final List<MatrixQ128> equalities2 = new ArrayList<>();
		equalities2.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 1, 0, 0, 0)));
		equalities2.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 1, 0, 0, 1)));
		equalities2.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 1, 1, 0, 0)));

		final List<MatrixQ128> congruences2 = new ArrayList<>();
		congruences2.add(CongruenceUtil.getRowVectorFromIntList(List.of(0, 1, 1, -2, 0)));
		congruences2.add(CongruenceUtil.getRowVectorFromIntList(List.of(1, 0, 0, 0, 1)));

		final var constraints2 = new ConstraintRepresentation(equalities2, congruences2, false, false);
		final var minimalConstraints2 = constraints2.getMinimalForm();
		// System.out.println(constraints2);
		// System.out.println(minimalConstraints2);

		Assert.assertTrue(hasMinimalForm(minimalConstraints2));
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
