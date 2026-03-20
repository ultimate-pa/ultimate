package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.ojalgo.matrix.MatrixQ128;
import org.ojalgo.matrix.store.GenericStore;
import org.ojalgo.scalar.RationalNumber;

import de.uni_freiburg.informatik.ultimate.logic.Rational;

public class CongruenceUtil {
	// TODO: Make Congruence relation to encapsulate equalities and congruence's
	public static MatrixQ128 equalityToVector(final int[] poliArray, final int result) {
		final List<Integer> list = new ArrayList<>(List.of(-result));
		for (final int item : poliArray) {
			list.add(item);
		}
		return getRowVectorFromIntList(list);
	}

	public static MatrixQ128 CongruenceToVector(final int[] poliArray, final int result, final int mod) {
		final int[] modPoliArray = Arrays.stream(poliArray).map(n -> n % mod).toArray();
		final int modResult = result % mod;
		return equalityToVector(modPoliArray, modResult).divide(mod);
	}

	public static long firstPivot(final MatrixQ128 vector) {
		final long k = vector.countColumns();

		for (long i = 0; i < k; i++) {
			if (!vector.get(0, i).isZero()) {
				return i;
			}
		}
		return k;
	}

	public static long lastPivot(final MatrixQ128 vector) {
		final var k = vector.countColumns();

		for (long i = k - 1; i >= 0; i--) {
			if (!vector.get(0, i).isZero()) {
				return i;
			}
		}
		return -1;
	}

	/*
	 * Eliminates the field in v1 by subtracting a multiple of v2
	 */
	public static MatrixQ128 eliminateField(final MatrixQ128 v1, final MatrixQ128 v2, final long pivot) {
		final var v1Value = v1.get(0, pivot);
		final var v2Value = v2.get(0, pivot);
		final var factor = v1Value.divide(v2Value);
		return v1.subtract(v2.multiply(factor));
	}

	public static List<MatrixQ128> getRowsFromMatrix(final MatrixQ128 matrix) {
		final ArrayList<MatrixQ128> rows = new ArrayList<>();
		for (int i = 0; i < matrix.countRows(); i++) {
			final var row = matrix.select(new int[] { i }, null);
			rows.add(row);
		}
		return rows;
	}

	public static MatrixQ128 getMatrixFromRows(final List<MatrixQ128> rows) {
		final var n = rows.size();
		long m = 0;
		if (n != 0) {
			m = rows.get(0).countColumns();
		}

		final GenericStore<RationalNumber> protoMatrix = GenericStore.Q128.make(n, m);
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < m; j++) {
				protoMatrix.set(i, j, rows.get(i).get(0, j));
			}
		}

		return MatrixQ128.FACTORY.copy(protoMatrix);
	}

	public static MatrixQ128 getMatrixFromIntList(final List<Integer> entries, final int rowCount,
			final int columnCount) {
		final GenericStore<RationalNumber> protoMatrix = GenericStore.Q128.make(rowCount, columnCount);

		for (int i = 0; i < rowCount; i++) {
			for (int j = 0; j < columnCount; j++) {
				final var rationalEntry = RationalNumber.of(entries.get(i * columnCount + j), 1);
				protoMatrix.set(i, j, rationalEntry);
			}
		}

		final var matrix = MatrixQ128.FACTORY.copy(protoMatrix);
		return matrix;
	}

	public static MatrixQ128 getMatrixFromRationalList(final List<Rational> entries, final int rowCount,
			final int columnCount) {
		final GenericStore<RationalNumber> protoMatrix = GenericStore.Q128.make(rowCount, columnCount);

		for (int i = 0; i < rowCount; i++) {
			for (int j = 0; j < columnCount; j++) {
				final Rational rational = entries.get(i * columnCount + j);
				final RationalNumber rationalEntry = RationalNumber.of(rational.numerator().longValueExact(),
						rational.denominator().longValueExact());
				protoMatrix.set(i, j, rationalEntry);
			}
		}

		final var matrix = MatrixQ128.FACTORY.copy(protoMatrix);
		return matrix;
	}

	public static MatrixQ128 getRowVectorFromIntList(final List<Integer> entries) {
		return getMatrixFromIntList(entries, 1, entries.size());
	}

	public static MatrixQ128 getRowVectorFromRationalList(final List<Rational> entries) {
		return getMatrixFromRationalList(entries, 1, entries.size());
	}

	public static long getNumerator(final RationalNumber num) {
		// TODO: Replace with new ojalgo release by internal methods
		final Pattern pattern = Pattern.compile("\\(\\s*(-?\\d+)\\s*/\\s*\\d+\\s*\\)");
		final Matcher matcher = pattern.matcher(num.toString());

		if (matcher.matches()) {
			return Long.parseLong(matcher.group(1));
		}
		throw new IllegalArgumentException("Invalid format: " + num);
	}

	public static long getDenominator(final RationalNumber num) {
		// TODO: Replace with new ojalgo release by internal methods
		final Pattern pattern = Pattern.compile("\\(\\s*-?\\d+\\s*/\\s*(\\d+)\\s*\\)");
		final Matcher matcher = pattern.matcher(num.toString());

		if (matcher.matches()) {
			return Long.parseLong(matcher.group(1));
		}
		throw new IllegalArgumentException("Invalid format: " + num);
	}
}
