package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.ojalgo.matrix.MatrixQ128;
import org.ojalgo.matrix.store.GenericStore;
import org.ojalgo.scalar.RationalNumber;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class CongruenceUtil {
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
	 * Eliminates the field in minuendVector by subtracting a multiple of the
	 * subtrahendVector and returns the updated minuendVector
	 */
	public static MatrixQ128 gaussEliminateField(final MatrixQ128 minuendVector, final MatrixQ128 subtrahendVector,
			final long pivot) {
		final MatrixQ128 v1 = subtrahendVector;
		final MatrixQ128 v2 = minuendVector;
		final var v1Value = v1.get(0, pivot);
		final var v2Value = v2.get(0, pivot);
		final var factor = v2Value.divide(v1Value);
		return v2.subtract(v1.multiply(factor));
	}

	/*
	 * Eliminates the field in minuendVector by subtracting a multiple of the
	 * subtrahendVector in a way that conserves modulo relations and returns the
	 * updated minuendVector and subtrahendVector
	 */
	public static Pair<MatrixQ128, MatrixQ128> hermitEliminateField(final MatrixQ128 minuendVector,
			final MatrixQ128 subtrahendVector, final long pivot) {
		final MatrixQ128 v1 = subtrahendVector;
		final MatrixQ128 v2 = minuendVector;

		final List<RationalNumber> elementList = new ArrayList<>(v1.asList());
		elementList.addAll(v2.asList());
		final long commonDenominator = getCommonDenominator(elementList);
		final RationalNumber commonDenominatorRational = RationalNumber.of(commonDenominator, 1);

		final MatrixQ128 wholeV1 = v1.multiply(commonDenominatorRational);
		final MatrixQ128 wholeV2 = v2.multiply(commonDenominatorRational);

		final RationalNumber wholePivotElement1Rational = wholeV1.get(0, pivot);
		final RationalNumber wholePivotElement2Rational = wholeV2.get(0, pivot);
		final long wholePivotElement1 = getNumerator(wholePivotElement1Rational);
		final long wholePivotElement2 = getNumerator(wholePivotElement2Rational);

		final long[] rst = gcdext(wholePivotElement1, wholePivotElement2);
		final long r = rst[0];
		final RationalNumber rRational = RationalNumber.of(r, 1);
		final long s = rst[1];
		final RationalNumber sRational = RationalNumber.of(s, 1);
		final long t = rst[2];
		final RationalNumber tRational = RationalNumber.of(t, 1);

		final MatrixQ128 newWholeV1 = wholeV1.multiply(sRational).add(wholeV2.multiply(tRational));
		final RationalNumber factor1 = wholePivotElement2Rational.negate().divide(rRational);
		final RationalNumber factor2 = wholePivotElement1Rational.divide(rRational);
		final MatrixQ128 newWholeV2 = wholeV1.multiply(factor1).add(wholeV2.multiply(factor2));

		final MatrixQ128 newV1 = newWholeV1.divide(commonDenominatorRational);
		final MatrixQ128 newV2 = newWholeV2.divide(commonDenominatorRational);

		final MatrixQ128 newSubtrahendVector = newV1;
		final MatrixQ128 newMinuendVector = newV2;

		return new Pair<>(newMinuendVector, newSubtrahendVector);
	}

	public static List<MatrixQ128> getRowsFromMatrix(final MatrixQ128 matrix) {
		final ArrayList<MatrixQ128> rows = new ArrayList<>();
		for (int i = 0; i < matrix.countRows(); i++) {
			final var row = matrix.select(new int[] { i }, null);
			rows.add(row);
		}
		return rows;
	}

	public static List<MatrixQ128> getColumnsFromMatrix(final MatrixQ128 matrix) {
		return getRowsFromMatrix(matrix.transpose());
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

	public static MatrixQ128 getMatrixFromColumns(final List<MatrixQ128> columns) {
		return getMatrixFromRows(columns).transpose();
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

	public static MatrixQ128 getMatrixFromRationalNumberList(final List<RationalNumber> entries, final int rowCount,
			final int columnCount) {
		final GenericStore<RationalNumber> protoMatrix = GenericStore.Q128.make(rowCount, columnCount);

		for (int i = 0; i < rowCount; i++) {
			for (int j = 0; j < columnCount; j++) {
				protoMatrix.set(i, j, entries.get(i * columnCount + j));
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

	public static MatrixQ128 getZeroMatrix(final int rowCount, final int columnCount) {
		final List<Rational> list = new ArrayList<>(Collections.nCopies(rowCount * columnCount, Rational.ZERO));
		return getMatrixFromRationalList(list, rowCount, columnCount);
	}

	public static MatrixQ128 reorderByColumns(final Map<Integer, Integer> map, final int resultColumnCount,
			final MatrixQ128 matrix) {
		final List<MatrixQ128> columns = getColumnsFromMatrix(matrix);
		final List<MatrixQ128> resultColumns = getColumnsFromMatrix(
				getZeroMatrix(matrix.getRowDim(), resultColumnCount));

		for (int i = 0; i < columns.size(); i++) {
			resultColumns.set(map.get(i), columns.get(i));
		}

		return getMatrixFromColumns(resultColumns);
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

	public static <K> Map<K, Integer> mergeMaps(final Map<K, Integer> map1, final Map<K, Integer> map2) {
		final Map<K, Integer> newMap = new HashMap<>();

		Integer freeIndex = 1;
		for (final K var : map1.keySet()) {
			newMap.put(var, freeIndex);
			freeIndex++;
		}

		for (final K var : map2.keySet()) {
			if (!newMap.containsKey(var)) {
				newMap.put(var, freeIndex);
				freeIndex++;
			}
		}
		return newMap;
	}

	/**
	 * Constructs a map that corresponds to targetMap o originMap^-1
	 */
	public static <K> Map<Integer, Integer> getReorderForMaps(final Map<K, Integer> originMap,
			final Map<K, Integer> targetMap) {
		final Map<Integer, Integer> newMap = new HashMap<>();

		for (final K key : originMap.keySet()) {
			final Integer originInteger = originMap.get(key);
			final Integer targetInteger = targetMap.get(key);
			newMap.put(originInteger, targetInteger);
		}
		return newMap;
	}

	private static long wholeDiv(final long x, final long y) {
		return Math.floorDiv(x, y);
	}

	public static long[] gcdext(final long x, final long y) {
		long oldR = x;
		long newR = y;
		long oldS = 1;
		long newS = 0;
		long oldT = 0;
		long newT = 1;

		while (newR != 0) {
			final long q = wholeDiv(oldR, newR);

			final long tempR = oldR;
			oldR = newR;
			newR = tempR - q * newR;

			final long tempS = oldS;
			oldS = newS;
			newS = tempS - q * newS;

			final long tempT = oldT;
			oldT = newT;
			newT = tempT - q * newT;
		}

		return new long[] { oldR, oldS, oldT };
	}

	public static long lcm(final long x, final long y) {
		final long gcd = gcdext(x, y)[0];
		if (gcd == 0) {
			return 0;
		}
		return Math.abs(Math.divideExact(x, gcd) * y);
	}

	public static long getCommonDenominator(final List<RationalNumber> list) {
		long commonDenominator = 1;
		for (final RationalNumber rationalNumber : list) {
			final long denominator = getDenominator(rationalNumber);
			commonDenominator = lcm(denominator, commonDenominator);
		}
		return commonDenominator;
	}

	public static long getCommonDenominator(final MatrixQ128 matrix) {
		final List<RationalNumber> list = matrix.asList();
		return getCommonDenominator(list);
	}

	public static List<MatrixQ128> sortForLastPivot(final List<MatrixQ128> list) {
		if (list.isEmpty()) {
			return list;
		}
		list.sort((v1, v2) -> (lastPivot(v1) < lastPivot(v2)) ? 1 : -1);
		return list;
	}
}
