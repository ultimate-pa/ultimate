package de.uni_freiburg.informatik.ultimate.lib.sifa.test;

import java.util.List;
import java.util.Map;

import org.junit.Assert;
import org.junit.Test;
import org.ojalgo.matrix.MatrixQ128;
import org.ojalgo.scalar.RationalNumber;

import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.congruence.CongruenceUtil;

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

	@Test
	public void testCongruenceToVector() {
		final var vector1 = CongruenceUtil.CongruenceToVector(new int[] { 1, 2, -3 }, -4, 5);
		final var vector2 = CongruenceUtil.getRowVectorFromIntList(List.of(4, 1, 2, -3)).divide(5);
		Assert.assertTrue(vector1.equals(vector2));

		final var vector3 = CongruenceUtil.CongruenceToVector(new int[] { 1, 2, -3 }, 4, 2);
		final var vector4 = CongruenceUtil.getRowVectorFromIntList(List.of(0, 1, 0, -1)).divide(2);
		Assert.assertTrue(vector3.equals(vector4));
	}

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

}
