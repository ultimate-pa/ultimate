package de.uni_freiburg.informatik.ultimate.lib.sifa;

import java.util.List;

import org.ojalgo.array.Array1D;
import org.ojalgo.matrix.MatrixQ128;
import org.ojalgo.matrix.store.GenericStore;
import org.ojalgo.scalar.RationalNumber;

public class TestMatrix {
	public TestMatrix() {
		// See https://www.ojalgo.org/code-examples/ for more examples
		final var x = MatrixQ128.FACTORY.make(10, 10);
		final RationalNumber y = x.get(0, 0);
		// final Method m = y.getClass().getDeclaredMethod("getNumenator");
		// m.setAccessible(true);
		// final var z = y.getNumerator();

		final List<Array1D<RationalNumber>> rows;
		// final MatrixQ128 matrix = MatrixQ128.FACTORY.row(rows);

		final int n1 = 3; // rows
		final int m1 = 3; // columns

		final GenericStore<RationalNumber> matrix1 = GenericStore.Q128.make(n1, m1);

		final List<RationalNumber> numbers = List.of(RationalNumber.valueOf(1), RationalNumber.valueOf(2),
				RationalNumber.valueOf(3), RationalNumber.valueOf(4), RationalNumber.valueOf(5),
				RationalNumber.valueOf(6), RationalNumber.valueOf(7), RationalNumber.valueOf(8),
				RationalNumber.valueOf(9));

		for (int i = 0; i < n1; i++) {
			for (int j = 0; j < m1; j++) {
				matrix1.set(i, j, numbers.get(i * m1 + j));
			}
		}

		final var realmatrix1 = MatrixQ128.FACTORY.copy(matrix1);

		final int[] zi = { 1 };
		final var sth = realmatrix1.select(zi, null);

	}
}
