package de.uni_freiburg.informatik.ultimate.lib.sifa.test;

import java.util.List;
import java.util.Map;

import org.junit.Assert;
import org.junit.Test;
import org.ojalgo.matrix.MatrixQ128;
import org.ojalgo.scalar.RationalNumber;

import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence.CongruenceUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class CongruenceUtilTest {

	@Test
	public void testFirstPivot() {
		final MatrixQ128 vector0 = CongruenceUtil.getRowVectorFromIntList(List.of(-1, 0, 1));
		Assert.assertEquals(CongruenceUtil.firstPivot(vector0), 0);

		final MatrixQ128 vector1 = CongruenceUtil.getRowVectorFromIntList(List.of(0, 1, 2));
		Assert.assertEquals(CongruenceUtil.firstPivot(vector1), 1);

		final MatrixQ128 vector2 = CongruenceUtil.getRowVectorFromIntList(List.of(0, 0, 1));
		Assert.assertEquals(CongruenceUtil.firstPivot(vector2), 2);

		final MatrixQ128 vector3 = CongruenceUtil.getRowVectorFromIntList(List.of(0, 0, 0));
		Assert.assertEquals(CongruenceUtil.firstPivot(vector3), 3);

	}

	@Test
	public void testLastPivot() {
		final MatrixQ128 vector0 = CongruenceUtil.getRowVectorFromIntList(List.of(1, 0, -1));
		Assert.assertEquals(CongruenceUtil.lastPivot(vector0), 2);

		final MatrixQ128 vector1 = CongruenceUtil.getRowVectorFromIntList(List.of(2, 1, 0));
		Assert.assertEquals(CongruenceUtil.lastPivot(vector1), 1);

		final MatrixQ128 vector2 = CongruenceUtil.getRowVectorFromIntList(List.of(1, 0, 0));
		Assert.assertEquals(CongruenceUtil.lastPivot(vector2), 0);

		final MatrixQ128 vector3 = CongruenceUtil.getRowVectorFromIntList(List.of(0, 0, 0));
		Assert.assertEquals(CongruenceUtil.lastPivot(vector3), -1);

	}

	// TODO: Remove this
	/*
	 * @Test public void testCongruenceToVector() { final var vector1 =
	 * CongruenceUtil.CongruenceToVector(new int[] { 1, 2, -3 }, -4, 5); final var
	 * vector2 = CongruenceUtil.getRowVectorFromIntList(List.of(4, 1, 2,
	 * -3)).divide(5); Assert.assertTrue(vector1.equals(vector2));
	 * 
	 * final var vector3 = CongruenceUtil.CongruenceToVector(new int[] { 1, 2, -3 },
	 * 4, 2); final var vector4 = CongruenceUtil.getRowVectorFromIntList(List.of(0,
	 * 1, 0, -1)).divide(2); Assert.assertTrue(vector3.equals(vector4)); }
	 */

	@Test
	public void testGetRowVectorFromIntList() {
		final var vector1 = CongruenceUtil.getRowVectorFromIntList(List.of(4, 1, 2, -3));
		final var vector2 = MatrixQ128.FACTORY.row(RationalNumber.of(4, 1), RationalNumber.of(1, 1),
				RationalNumber.of(2, 1), RationalNumber.of(-3, 1));
		Assert.assertTrue(vector1.equals(vector2));

		final var vector3 = CongruenceUtil.getRowVectorFromIntList(List.of());
		final var vector4 = MatrixQ128.FACTORY.row();
		Assert.assertTrue(vector3.equals(vector4));
	}

	@Test
	public void testGetRowsFromMatrix() {
		final var matrix1 = CongruenceUtil.getMatrixFromIntList(List.of(1, 2, 3, 4, 5, 6), 2, 3);
		final var matrix1Rows = CongruenceUtil.getRowsFromMatrix(matrix1);
		final var rows1 = List.of(CongruenceUtil.getRowVectorFromIntList(List.of(1, 2, 3)),
				CongruenceUtil.getRowVectorFromIntList(List.of(4, 5, 6)));
		Assert.assertTrue(matrix1Rows.get(0).equals(rows1.get(0)));
		Assert.assertTrue(matrix1Rows.get(1).equals(rows1.get(1)));
		/*
		 * System.out.println(matrix1); System.out.println(matrix1Rows);
		 * System.out.println(rows1);
		 */

		final var matrix2 = CongruenceUtil.getMatrixFromIntList(List.of(1, 2, 3, 4, 5, 6), 3, 2);
		final var matrix2Rows = CongruenceUtil.getRowsFromMatrix(matrix2);
		final var rows2 = List.of(CongruenceUtil.getRowVectorFromIntList(List.of(1, 2)),
				CongruenceUtil.getRowVectorFromIntList(List.of(3, 4)),
				CongruenceUtil.getRowVectorFromIntList(List.of(5, 6)));
		Assert.assertTrue(matrix2Rows.get(0).equals(rows2.get(0)));
		Assert.assertTrue(matrix2Rows.get(1).equals(rows2.get(1)));
		Assert.assertTrue(matrix2Rows.get(2).equals(rows2.get(2)));

		final var matrix3 = CongruenceUtil.getMatrixFromIntList(List.of(), 0, 0);
		final var matrix3Rows = CongruenceUtil.getRowsFromMatrix(matrix3);
		Assert.assertEquals(matrix3Rows.size(), 0);
	}

	@Test
	public void testGetMatrixFromRows() {
		final var matrix1 = CongruenceUtil.getMatrixFromIntList(List.of(1, 2, 3, 4, 5, 6), 2, 3);
		final var rows2 = List.of(CongruenceUtil.getRowVectorFromIntList(List.of(1, 2, 3)),
				CongruenceUtil.getRowVectorFromIntList(List.of(4, 5, 6)));
		final var matrix2 = CongruenceUtil.getMatrixFromRows(rows2);
		Assert.assertTrue(matrix1.equals(matrix2));

		final var matrix3 = CongruenceUtil.getMatrixFromIntList(List.of(1, 2, 3, 4, 5, 6), 3, 2);
		final var rows3 = List.of(CongruenceUtil.getRowVectorFromIntList(List.of(1, 2)),
				CongruenceUtil.getRowVectorFromIntList(List.of(3, 4)),
				CongruenceUtil.getRowVectorFromIntList(List.of(5, 6)));
		final var matrix4 = CongruenceUtil.getMatrixFromRows(rows3);
		Assert.assertTrue(matrix3.equals(matrix4));

		final List<MatrixQ128> rows5 = List.of();
		final var matrix5 = CongruenceUtil.getMatrixFromRows(rows5);
		Assert.assertEquals(matrix5.countColumns(), 0);
		Assert.assertEquals(matrix5.countRows(), 0);
	}

	@Test
	public void testGetNumeratorAndGetDenominator() {
		final var num1 = RationalNumber.of(1, 2);
		Assert.assertEquals(1, CongruenceUtil.getNumerator(num1));
		Assert.assertEquals(2, CongruenceUtil.getDenominator(num1));

		final var num2 = RationalNumber.of(2, 1);
		Assert.assertEquals(2, CongruenceUtil.getNumerator(num2));
		Assert.assertEquals(1, CongruenceUtil.getDenominator(num2));

		final var num3 = RationalNumber.of(2, 4);
		Assert.assertEquals(1, CongruenceUtil.getNumerator(num3));
		Assert.assertEquals(2, CongruenceUtil.getDenominator(num3));

		final var num4 = RationalNumber.of(1, -2);
		Assert.assertEquals(-1, CongruenceUtil.getNumerator(num4));
		Assert.assertEquals(2, CongruenceUtil.getDenominator(num4));
	}

	@Test
	public void testReorderByColumns() {
		final var matrix = CongruenceUtil.getMatrixFromIntList(List.of(1, 2, 3, 4, 5, 6), 2, 3);
		// System.out.println(matrix);

		final Map<Integer, Integer> map1 = Map.of(0, 1, 1, 2, 2, 0);
		final var matrix1 = CongruenceUtil.getMatrixFromIntList(List.of(3, 1, 2, 6, 4, 5), 2, 3);
		final var matrixReorder1 = CongruenceUtil.reorderByColumns(map1, 3, matrix);
		// System.out.println(matrix1);
		// System.out.println(matrixReorder1);
		Assert.assertTrue(matrix1.equals(matrixReorder1));

		final Map<Integer, Integer> map2 = Map.of(0, 1, 1, 2, 2, 3);
		final var matrix2 = CongruenceUtil.getMatrixFromIntList(List.of(0, 1, 2, 3, 0, 4, 5, 6), 2, 4);
		final var matrixReorder2 = CongruenceUtil.reorderByColumns(map2, 4, matrix);
		// System.out.println(matrix2);
		// System.out.println(matrixReorder2);
		Assert.assertTrue(matrix2.equals(matrixReorder2));
	}

	private static boolean testMergedMapsHelper(final Map<String, Integer> map1, final Map<String, Integer> map2,
			final Map<String, Integer> mergedMap) {
		for (final String s : map1.keySet()) {
			if (!mergedMap.containsKey(s)) {
				return false;
			}
		}
		for (final String s : map2.keySet()) {
			if (!mergedMap.containsKey(s)) {
				return false;
			}
		}
		for (final String s1 : mergedMap.keySet()) {
			for (final String s2 : mergedMap.keySet()) {
				if (!s1.equals(s2) && mergedMap.get(s1).equals(mergedMap.get(s2))) {
					return false;
				}
			}
		}
		return true;
	}

	@Test
	public void testMergeMaps() {
		final Map<String, Integer> map1 = Map.of("a", 0, "b", 1, "c", 2);
		final Map<String, Integer> map2 = Map.of("d", 0, "e", 1, "f", 2);
		final Map<String, Integer> mergedMap12 = CongruenceUtil.mergeMaps(map1, map2);
		// System.out.println(mergedMap12);
		Assert.assertTrue(testMergedMapsHelper(map1, map2, mergedMap12));

		final Map<String, Integer> map3 = Map.of("a", 2, "b", 5, "d", 1);
		final Map<String, Integer> mergedMap13 = CongruenceUtil.mergeMaps(map1, map3);
		// System.out.println(mergedMap13);
		Assert.assertTrue(testMergedMapsHelper(map1, map3, mergedMap13));
	}

	@Test
	public void testGetReorderForMaps() {
		final Map<String, Integer> map1 = Map.of("a", 0, "b", 1, "c", 2);
		final Map<String, Integer> map2 = Map.of("a", 2, "b", 1, "c", 0, "e", 4, "f", 5);
		final Map<Integer, Integer> map12 = Map.of(0, 2, 1, 1, 2, 0);
		final Map<Integer, Integer> reorderMap12 = CongruenceUtil.getReorderForMaps(map1, map2);
		Assert.assertTrue(map12.equals(reorderMap12));

		final Map<String, Integer> map3 = Map.of("a", 2, "b", 5, "c", 0);
		final Map<Integer, Integer> map13 = Map.of(0, 2, 1, 5, 2, 0);
		final Map<Integer, Integer> reorderMap13 = CongruenceUtil.getReorderForMaps(map1, map3);
		Assert.assertTrue(map13.equals(reorderMap13));

	}

	@Test
	public void testGcdext() {
		final long range = 20;
		for (long x = -range; x <= range; x++) {
			for (long y = -range; y <= range; y++) {
				final long[] rst = CongruenceUtil.gcdext(x, y);
				final long gcd = rst[0];
				// System.out.println(x);
				// System.out.println(y);
				// System.out.println(gcd);
				// System.out.println(x.gcd(y));

				if (x == 0 && y == 0) {
					Assert.assertTrue(gcd == 0);
				} else {
					Assert.assertTrue(x % gcd == 0);
					Assert.assertTrue(y % gcd == 0);
				}
				final long s = rst[1];
				final long t = rst[2];
				final long v = s * x + t * y;
				Assert.assertTrue(gcd == v);
			}
		}
	}

	@Test
	public void testLcm() {
		final long range = 20;
		for (long x = -range; x <= range; x++) {
			for (long y = -range; y <= range; y++) {
				final long lcm = CongruenceUtil.lcm(x, y);
				final long gcd = CongruenceUtil.gcdext(x, y)[0];
				final long v1 = Math.abs(gcd * lcm);
				final long v2 = Math.abs(x * y);
				// System.out.println("x:" + x);
				// System.out.println(y);
				// System.out.println(lcm);
				// System.out.println(gcd);
				// System.out.println(v1);
				// System.out.println(v2);
				Assert.assertTrue(v1 == v2);
			}
		}
	}

	@Test
	public void testGaussEliminateField() {
		// 1, 2/3, 1/2
		final List<RationalNumber> list1 = List.of(RationalNumber.of(1, 1), RationalNumber.of(2, 3),
				RationalNumber.of(1, 2));
		// 2, 1/4, 0
		final List<RationalNumber> list2 = List.of(RationalNumber.of(2, 1), RationalNumber.of(1, 4),
				RationalNumber.of(0, 1));

		// 0, -13/12, -1
		final List<RationalNumber> list3 = List.of(RationalNumber.of(0, 1), RationalNumber.of(-13, 12),
				RationalNumber.of(-1, 1));
		// 13/8, 0, -3/16
		final List<RationalNumber> list4 = List.of(RationalNumber.of(13, 8), RationalNumber.of(0, 1),
				RationalNumber.of(-3, 16));

		final MatrixQ128 v1 = CongruenceUtil.getMatrixFromRationalNumberList(list1, 1, 3);
		final MatrixQ128 v2 = CongruenceUtil.getMatrixFromRationalNumberList(list2, 1, 3);

		final MatrixQ128 expected1 = CongruenceUtil.getMatrixFromRationalNumberList(list3, 1, 3);
		final MatrixQ128 expected2 = CongruenceUtil.getMatrixFromRationalNumberList(list4, 1, 3);
		final MatrixQ128 expected3 = v2;

		final MatrixQ128 res1 = CongruenceUtil.gaussEliminateField(v2, v1, 0);
		final MatrixQ128 res2 = CongruenceUtil.gaussEliminateField(v2, v1, 1);
		final MatrixQ128 res3 = CongruenceUtil.gaussEliminateField(v2, v1, 2);

		Assert.assertTrue(expected1.equals(res1));
		Assert.assertTrue(expected2.equals(res2));
		Assert.assertTrue(expected3.equals(res3));
	}

	@Test
	public void testHermitEliminateField() {
		// 1, 2/3, 1/2
		final List<RationalNumber> list1 = List.of(RationalNumber.of(1, 1), RationalNumber.of(2, 3),
				RationalNumber.of(1, 2));
		// 2, 1/4, 0
		final List<RationalNumber> list2 = List.of(RationalNumber.of(2, 1), RationalNumber.of(1, 4),
				RationalNumber.of(0, 1));

		// 0, -13/12, -12/12
		final List<RationalNumber> list3 = List.of(RationalNumber.of(0, 1), RationalNumber.of(-13, 12),
				RationalNumber.of(-12, 12));

		// 60/12, 1/12, -6/12
		final List<RationalNumber> list4 = List.of(RationalNumber.of(60, 12), RationalNumber.of(1, 12),
				RationalNumber.of(-6, 12));
		// 156/12, 0, -18/12
		final List<RationalNumber> list5 = List.of(RationalNumber.of(156, 12), RationalNumber.of(0, 1),
				RationalNumber.of(-18, 12));

		final MatrixQ128 v1 = CongruenceUtil.getMatrixFromRationalNumberList(list1, 1, 3);
		final MatrixQ128 v2 = CongruenceUtil.getMatrixFromRationalNumberList(list2, 1, 3);
		final MatrixQ128 v3 = CongruenceUtil.getMatrixFromRationalNumberList(list3, 1, 3);
		final MatrixQ128 v4 = CongruenceUtil.getMatrixFromRationalNumberList(list4, 1, 3);
		final MatrixQ128 v5 = CongruenceUtil.getMatrixFromRationalNumberList(list5, 1, 3);

		final Pair<MatrixQ128, MatrixQ128> expected1 = new Pair<>(v3, v1);
		final Pair<MatrixQ128, MatrixQ128> expected2 = new Pair<>(v5, v4);
		final Pair<MatrixQ128, MatrixQ128> expected3 = new Pair<>(v2, v1);

		final Pair<MatrixQ128, MatrixQ128> res1 = CongruenceUtil.hermitEliminateField(v2, v1, 0);
		final Pair<MatrixQ128, MatrixQ128> res2 = CongruenceUtil.hermitEliminateField(v2, v1, 1);
		final Pair<MatrixQ128, MatrixQ128> res3 = CongruenceUtil.hermitEliminateField(v2, v1, 2);

		Assert.assertTrue(expected1.equals(res1));
		Assert.assertTrue(expected2.equals(res2));
		Assert.assertTrue(expected3.equals(res3));
	}

	@Test
	public void testGetStandardBasisVector() {
		final List<RationalNumber> list1 = List.of(RationalNumber.ZERO, RationalNumber.ZERO, RationalNumber.ONE);
		final MatrixQ128 expected1 = CongruenceUtil.getMatrixFromRationalNumberList(list1, 1, 3);
		final MatrixQ128 result1 = CongruenceUtil.getStandardBasisVector(2, 3);
		Assert.assertTrue(result1.equals(expected1));

		final List<RationalNumber> list2 = List.of(RationalNumber.ONE, RationalNumber.ZERO, RationalNumber.ZERO);
		final MatrixQ128 expected2 = CongruenceUtil.getMatrixFromRationalNumberList(list2, 1, 3);
		final MatrixQ128 result2 = CongruenceUtil.getStandardBasisVector(0, 3);
		Assert.assertTrue(result2.equals(expected2));
	}

}
