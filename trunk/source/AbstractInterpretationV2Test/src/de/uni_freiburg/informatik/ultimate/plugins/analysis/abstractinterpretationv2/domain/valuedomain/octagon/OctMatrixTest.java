package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.octagon;

import org.junit.Assert;
import org.junit.Test;

public class OctMatrixTest {
	
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
		assertEqualTo(mStrongClosure, m.strongClosure());
		assertEqualTo(mStrongClosure, mStrongClosure.strongClosure());
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
		assertEqualTo(mStrongClosure, m.strongClosure());
		assertEqualTo(mStrongClosure, mStrongClosure.strongClosure());
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
		assertEqualTo(mStrongClosure, m.strongClosure());
		assertEqualTo(mStrongClosure, mStrongClosure.strongClosure());
	}
	
	@Test
	public void testSingelton() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular("0 2.0000\n" + "-2 0");
		Assert.assertFalse(m.strongClosure().hasNegativeSelfLoop());
		Assert.assertFalse(m.tightClosure().hasNegativeSelfLoop());
	}
	
	@Test
	public void testBottomReals() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular("0 2 \n -3 0");
		Assert.assertTrue(m.strongClosure().hasNegativeSelfLoop());
		Assert.assertTrue(m.tightClosure().hasNegativeSelfLoop());
	}
	
	@Test
	public void testBottomIntegers() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular(
				  "  0 inf\n"
				+ "inf   0\n"
				+ "inf inf   0  -3\n"
				+ "  3   0 inf   0\n");
		Assert.assertFalse(m.strongClosure().hasNegativeSelfLoop());
		Assert.assertTrue(m.tightClosure().hasNegativeSelfLoop());
	}
	
	private void assertEqualTo(OctMatrix expected, OctMatrix actual) {
		String msg = "expected:\n" + expected + "acutal:\n" + actual;
		Assert.assertTrue(msg, expected.equalTo(actual));
	}
	
}
