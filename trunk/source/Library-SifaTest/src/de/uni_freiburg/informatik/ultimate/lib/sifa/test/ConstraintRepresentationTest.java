package de.uni_freiburg.informatik.ultimate.lib.sifa.test;

import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;
import org.ojalgo.matrix.MatrixQ128;

import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.CongruenceState;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.ConstraintRepresentation;

public class ConstraintRepresentationTest {
	@Test
	public void testConstraintRepresentationGetMinimalForm() {
		final List<MatrixQ128> equalities1 = new ArrayList<>();
		equalities1.add(CongruenceState.getRowVectorFromIntList(List.of(1, 1, 0, 0, 0)));
		equalities1.add(CongruenceState.getRowVectorFromIntList(List.of(1, 1, 0, 0, 0)));
		equalities1.add(CongruenceState.getRowVectorFromIntList(List.of(1, 1, 1, 0, 0)));

		final List<MatrixQ128> congruences1 = new ArrayList<>();
		congruences1.add(CongruenceState.getRowVectorFromIntList(List.of(0, 1, 1, -2, 0)));
		congruences1.add(CongruenceState.getRowVectorFromIntList(List.of(0, 0, 0, 0, 1)));

		final var constraints1 = new ConstraintRepresentation(equalities1, congruences1, false);
		final var minimalConstraints1 = constraints1.getMinimalForm();
		// System.out.println(constraints1);
		// System.out.println(minimalConstraints1);

		Assert.assertTrue(constraintRepresentationHasMinimalForm(minimalConstraints1));

		final List<MatrixQ128> equalities2 = new ArrayList<>();
		equalities2.add(CongruenceState.getRowVectorFromIntList(List.of(1, 1, 0, 0, 0)));
		equalities2.add(CongruenceState.getRowVectorFromIntList(List.of(1, 1, 0, 0, 1)));
		equalities2.add(CongruenceState.getRowVectorFromIntList(List.of(1, 1, 1, 0, 0)));

		final List<MatrixQ128> congruences2 = new ArrayList<>();
		congruences2.add(CongruenceState.getRowVectorFromIntList(List.of(0, 1, 1, -2, 0)));
		congruences2.add(CongruenceState.getRowVectorFromIntList(List.of(1, 0, 0, 0, 1)));

		final var constraints2 = new ConstraintRepresentation(equalities2, congruences2, false);
		final var minimalConstraints2 = constraints2.getMinimalForm();
		// System.out.println(constraints2);
		// System.out.println(minimalConstraints2);

		Assert.assertTrue(constraintRepresentationHasMinimalForm(minimalConstraints2));
	}

	public boolean constraintRepresentationHasMinimalForm(final ConstraintRepresentation constraints) {
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
			final var pivot = CongruenceState.lastPivot(vector);

			if (pivot == -1) {
				return false;
			}
			final var value = vector.get(0, pivot);
			if (CongruenceState.getNumerator(value) <= 0) {
				return false;
			}
			for (int j = i + 1; j < vectors.size(); j++) {
				final var other = vectors.get(j);
				if (pivot == CongruenceState.lastPivot(other)) {
					return false;
				}
			}
		}
		return true;
	}
}
