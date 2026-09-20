package de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SubtermPropertyChecker;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class CongruenceUtil {

	/**
	 * Eliminates the field in minuendVector by subtracting a multiple of the
	 * subtrahendVector and returns the updated minuendVector
	 */
	public static RationalVector gaussEliminateField(final RationalVector minuendVector,
			final RationalVector subtrahendVector, final int pivot) {
		final RationalVector v1 = subtrahendVector;
		final RationalVector v2 = minuendVector;
		final Rational v1Value = v1.get(pivot);
		final Rational v2Value = v2.get(pivot);
		final Rational factor = v2Value.div(v1Value);
		return v2.subtract(v1.multiply(factor));
	}

	/**
	 * Eliminates the field in minuendVector by subtracting a multiple of the
	 * subtrahendVector in a way that conserves modulo relations and returns the
	 * updated minuendVector and subtrahendVector
	 */
	public static Pair<RationalVector, RationalVector> hermitEliminateField(final RationalVector minuendVector,
			final RationalVector subtrahendVector, final int pivot) {
		final RationalVector v1 = subtrahendVector;
		final RationalVector v2 = minuendVector;

		final List<Rational> elementList = new ArrayList<>(v1.asList());
		elementList.addAll(v2.asList());
		final BigInteger commonDenominator = getCommonDenominator(elementList);
		final Rational commonDenominatorRational = Rational.valueOf(commonDenominator, BigInteger.ONE);

		final RationalVector wholeV1 = v1.multiply(commonDenominatorRational);
		final RationalVector wholeV2 = v2.multiply(commonDenominatorRational);

		final Rational wholePivotElement1Rational = wholeV1.get(pivot);
		final Rational wholePivotElement2Rational = wholeV2.get(pivot);
		final BigInteger wholePivotElement1 = wholePivotElement1Rational.numerator();
		final BigInteger wholePivotElement2 = wholePivotElement2Rational.numerator();

		final BigInteger[] rst = gcdext(wholePivotElement1, wholePivotElement2);
		final BigInteger r = rst[0];
		final Rational rRational = Rational.valueOf(r, BigInteger.ONE);
		final BigInteger s = rst[1];
		final Rational sRational = Rational.valueOf(s, BigInteger.ONE);
		final BigInteger t = rst[2];
		final Rational tRational = Rational.valueOf(t, BigInteger.ONE);

		final RationalVector newWholeV1 = wholeV1.multiply(sRational).add(wholeV2.multiply(tRational));
		final Rational factor1 = wholePivotElement2Rational.negate().div(rRational);
		final Rational factor2 = wholePivotElement1Rational.div(rRational);
		final RationalVector newWholeV2 = wholeV1.multiply(factor1).add(wholeV2.multiply(factor2));

		final RationalVector newV1 = newWholeV1.divide(commonDenominatorRational);
		final RationalVector newV2 = newWholeV2.divide(commonDenominatorRational);

		final RationalVector newSubtrahendVector = newV1;
		final RationalVector newMinuendVector = newV2;

		return new Pair<>(newMinuendVector, newSubtrahendVector);
	}

	/**
	 * Reorders the columns of matrix according to the permutation given by map and
	 * returns the resulting matrix with dimensions matrix.rowCount x
	 * resultColumnCount.
	 */
	public static RationalMatrix reorderByColumns(final Map<Integer, Integer> map, final int resultColumnCount,
			final RationalMatrix matrix) {
		final List<RationalVector> columns = matrix.getColumnVectors();
		final List<RationalVector> resultColumns = RationalMatrix.getZeroMatrix(matrix.getRowCount(), resultColumnCount)
				.getColumnVectors();

		for (int i = 0; i < columns.size(); i++) {
			resultColumns.set(map.get(i), columns.get(i));
		}

		return RationalMatrix.fromColumnVectors(resultColumns, matrix.getRowCount());
	}

	/**
	 * Returns a new map that contains every key in map1 and map2 exactly once and
	 * maps each key to a unique Integer.
	 */
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

	private static BigInteger wholeDiv(final BigInteger x, final BigInteger y) {
		return x.divideAndRemainder(y)[0];
	}

	/**
	 * Given two values x, y returns an array [r, s, t] for which it holds that:
	 * <ul>
	 * <li>r = gcd(x, y)
	 * <li>s * x + t * y = r
	 * </ul>
	 */
	public static BigInteger[] gcdext(final BigInteger x, final BigInteger y) {
		BigInteger oldR = x;
		BigInteger newR = y;
		BigInteger oldS = BigInteger.ONE;
		BigInteger newS = BigInteger.ZERO;
		BigInteger oldT = BigInteger.ZERO;
		BigInteger newT = BigInteger.ONE;

		while (!newR.equals(BigInteger.ZERO)) {
			final BigInteger q = wholeDiv(oldR, newR);

			final BigInteger tempR = oldR;
			oldR = newR;
			newR = tempR.subtract(q.multiply(newR));

			final BigInteger tempS = oldS;
			oldS = newS;
			newS = tempS.subtract(q.multiply(newS));

			final BigInteger tempT = oldT;
			oldT = newT;
			newT = tempT.subtract(q.multiply(newT));
		}

		return new BigInteger[] { oldR, oldS, oldT };
	}

	/**
	 * Returns the least common multiple (lcm) of x and y.
	 */
	public static BigInteger lcm(final BigInteger x, final BigInteger y) {
		final BigInteger gcd = x.gcd(y);
		if (gcd.equals(BigInteger.ZERO)) {
			return BigInteger.ZERO;
		}
		return x.divideAndRemainder(gcd)[0].multiply(y).abs();
	}

	/**
	 * Returns the common denominator of the entries of the list.
	 */
	public static BigInteger getCommonDenominator(final List<Rational> list) {
		BigInteger commonDenominator = BigInteger.ONE;
		for (final Rational rational : list) {
			final BigInteger denominator = rational.denominator();
			commonDenominator = lcm(denominator, commonDenominator);
		}
		return commonDenominator;
	}

	/**
	 * Returns the common denominator of the entries of the vector.
	 */
	public static BigInteger getCommonDenominator(final RationalVector vector) {
		final List<Rational> list = vector.asList();
		return getCommonDenominator(list);
	}

	/**
	 * Returns true if the last non-zero entries of vector1 and vector2 are equal
	 * and located at the same index in their respective vectors.
	 */
	public static boolean isEqualsInLastNonZero(final RationalVector vector1, final RationalVector vector2) {
		final int k = vector1.lastPivot();
		if (k == vector2.lastPivot()) {
			if (k == 0) {
				return true;
			}
			final Rational value1 = vector1.get(k);
			final Rational value2 = vector2.get(k);
			if (value1.equals(value2)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Returns true if term contains a mod application.
	 */
	public static boolean containsMod(final Term term) {
		final var checker = new SubtermPropertyChecker(x -> SmtUtils.isFunctionApplication(x, "mod"));
		return checker.isSatisfiedBySomeSubterm(term);
	}

}
