package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctMatrix;

public class OctMatrixTest {
	
	@Test
	public void testEmpty() {
		OctMatrix m = OctMatrix.top(0);
		assertIsEqualTo(m, m.strongClosureNaiv());
		assertIsEqualTo(m, m.tightClosure());
		assertIsEqualTo(m, m.add(m));
		assertIsEqualTo(m, OctMatrix.min(m, m));
		assertIsEqualTo(m, OctMatrix.max(m, m));
	}
	
	@Test
	public void testStrongClosure1() {
		 OctMatrix m = OctMatrix.parseBlockLowerTriangular(
			  "0 9\n"
			+ "0 0\n"
			+ "0 8 0 9\n"
			+ "8 2 0 0\n"
			+ "7 4 8 6 0 9\n"
			+ "0 3 6 7 0 0\n");
		 OctMatrix mStrongClosure = OctMatrix.parseBlockLowerTriangular(
			  "0 7\n"
			+ "0 0\n"
			+ "0 7 0 7\n"
			+ "0 2 0 0\n"
			+ "4 4 4 4 0 8\n"
			+ "0 3 0 3 0 0\n");
		assertIsEqualTo(mStrongClosure, m.strongClosureNaiv());
		assertIsEqualTo(mStrongClosure, mStrongClosure.strongClosureNaiv());
	}

	@Test
	public void testStrongClosure2() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular(
			  "0.6  inf\n"
			+ "inf  0.6\n"
			+ "inf  1.3 inf inf\n"
			+ "inf -1.5 4.9 inf\n");
		OctMatrix mStrongClosure = OctMatrix.parseBlockLowerTriangular(
			  "0.0 -0.2\n"
			+ "inf  0.0\n"
			+ "inf  1.3 0.0 inf\n"
			+ "inf -1.5 4.9 0.0\n");
		assertIsEqualTo(mStrongClosure, m.strongClosureNaiv());
		assertIsEqualTo(mStrongClosure, mStrongClosure.strongClosureNaiv());
	}
	
	@Test
	public void testStrongClosure3() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular(
			  "  0 inf\n"
			+ "  2   0\n"
			+ "inf inf   0 inf\n"
			+ "inf inf   4   0\n");
		OctMatrix mStrongClosure = OctMatrix.parseBlockLowerTriangular(
			  "  0 inf\n"
			+ "  2   0\n"
			+ "inf inf   0 inf\n"
			+ "  3 inf   4   0\n");
		assertIsEqualTo(mStrongClosure, m.strongClosureNaiv());
		assertIsEqualTo(mStrongClosure, mStrongClosure.strongClosureNaiv());
	}
	
	@Test
	public void testStrongClosure4() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular(
			  "  0 inf\n"
			+ "  2   0\n"
			+ "inf inf   0 inf\n"
			+ "inf inf   4   0\n");
		OctMatrix mStrongClosure = OctMatrix.parseBlockLowerTriangular(
			  "  0 inf\n"
			+ "  2   0\n"
			+ "inf inf   0 inf\n"
			+ "  3 inf   4   0\n");
		assertIsEqualTo(mStrongClosure, m.strongClosureNaiv());
		assertIsEqualTo(mStrongClosure, mStrongClosure.strongClosureNaiv());
	}

	@Test
	public void testTightClosure1() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular("0 5.2 \n 2.8 0"); // v_0 \in [-2.6, 1.4]
		OctMatrix t = OctMatrix.parseBlockLowerTriangular("0 4   \n 2   0");
		assertIsEqualTo(m, m.strongClosureNaiv());
		assertIsEqualTo(t, m.tightClosure());
	}
	
	@Test
	public void testClosuresSingeltonReals() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular("0 2.0000 \n -2 0"); // v_0 \in [-1, -1]
		Assert.assertFalse(m.strongClosureNaiv().hasNegativeSelfLoop());
		Assert.assertFalse(m.tightClosure().hasNegativeSelfLoop());
	}

	@Test
	public void testClosuresBottomReals() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular("0 2 \n -3 0");
		Assert.assertTrue(m.strongClosureNaiv().hasNegativeSelfLoop());
		Assert.assertTrue(m.tightClosure().hasNegativeSelfLoop());
	}
	
	@Test
	public void testClosuresBottomIntegers() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular(
			  "  0 inf\n"
			+ "inf   0\n"
			+ "inf inf   0  -3\n"
			+ "  3   0 inf   0\n");
		Assert.assertFalse(m.strongClosureNaiv().hasNegativeSelfLoop());
		Assert.assertTrue(m.tightClosure().hasNegativeSelfLoop());
	}
	
	@Test
	public void testSumMinMax() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular("-7 inf    1000000000000.0000000000000 inf");
		OctMatrix n = OctMatrix.parseBlockLowerTriangular(" 9 -2e308 0000000000000.0000000000001 inf");
		OctMatrix sum = OctMatrix.parseBlockLowerTriangular("2 inf 1000000000000.0000000000001 inf");
		OctMatrix min = OctMatrix.parseBlockLowerTriangular("-7 -2e308 0.0000000000001 inf");
		OctMatrix max = OctMatrix.parseBlockLowerTriangular("9 inf 1000000000000 inf");

		assertIsEqualTo(sum, m.add(n));
		assertIsEqualTo(sum, n.add(m));

		assertIsEqualTo(min, OctMatrix.min(m, n));
		assertIsEqualTo(min, OctMatrix.min(n, m));

		assertIsEqualTo(max, OctMatrix.max(m, n));
		assertIsEqualTo(max, OctMatrix.max(n, m));
	}
	
	@Test
	public void testRelations() {
		OctMatrix e1 = OctMatrix.parseBlockLowerTriangular("0 inf -2.5e80 9");
		OctMatrix e2 = OctMatrix.parseBlockLowerTriangular("-0e-1 inf -25e79  9.00000000000000000000");
		OctMatrix g1 = OctMatrix.parseBlockLowerTriangular("0 inf -2.5e80 9.000000000000000000001");
		OctMatrix g2 = OctMatrix.parseBlockLowerTriangular("inf inf inf inf");
		OctMatrix l1 = OctMatrix.parseBlockLowerTriangular("-0.000000000000000000001 inf -2.5e80 9");
		OctMatrix l2 = OctMatrix.parseBlockLowerTriangular("0 2e308 -2.5e80 9");
		
		Assert.assertTrue(e1.isEqualTo(e1));
		Assert.assertTrue(e1.isEqualTo(e2));
		Assert.assertTrue(e2.isEqualTo(e1));
		Assert.assertTrue(e1.isLessEqualThan(e1));
		Assert.assertTrue(e1.isLessEqualThan(e2));
		Assert.assertTrue(e2.isLessEqualThan(e1));
		
		Assert.assertTrue(e1.isLessEqualThan(g1) && !e1.isEqualTo(g1) && !g1.isEqualTo(e1));
		Assert.assertTrue(!g1.isLessEqualThan(e1));
		Assert.assertTrue(e1.isLessEqualThan(g2) && !e1.isEqualTo(g2) && !g2.isEqualTo(e1));
		Assert.assertTrue(!g2.isLessEqualThan(e1));
		
		Assert.assertTrue(l1.isLessEqualThan(e1) && !l1.isEqualTo(e1) && !e1.isEqualTo(l1));
		Assert.assertTrue(!e1.isLessEqualThan(l1));
		Assert.assertTrue(l2.isLessEqualThan(e1) && !l2.isEqualTo(e1) && !e1.isEqualTo(l2));
		Assert.assertTrue(!e1.isLessEqualThan(l2));
	}
	
	@Test
	public void testByComparingRandom() {
		for (int i = 0; i < 2000; ++i) {
			int variables = (int) (Math.random() * 10) + 1;
			OctMatrix m = OctMatrix.random(variables);
			OctMatrix cNaiv = m.strongClosureNaiv();
			OctMatrix cOther = m.strongClosurePerm();
			if (cNaiv.hasNegativeSelfLoop() && cOther.hasNegativeSelfLoop()) {
				// test passed
			} else if (!cNaiv.isEqualTo(cOther)) {
				System.out.println("original matrix");
				System.out.println(m);
				System.out.println("strong closure (naiv)");
				System.out.println(cNaiv);
				System.out.println("strong closure (full sparse)");
				System.out.println(cOther);
				Assert.fail();
			}
		}
	}
	
	private void assertIsEqualTo(OctMatrix expected, OctMatrix actual) {
		String msg = "expected:\n" + expected + "acutal:\n" + actual;
		Assert.assertTrue(msg, expected.isEqualTo(actual));
	}

}
