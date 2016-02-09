package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctMatrix;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctMatrix.WideningStepSupplier;
import de.uni_freiburg.informatik.ultimate.util.BidirectionalMap;

public class OctMatrixTest {

	@Test
	public void testEmpty() {
		OctMatrix m = OctMatrix.NEW;
		assertIsEqualTo(m, m.cachedStrongClosure());
		assertIsEqualTo(m, m.cachedTightClosure());
		assertIsEqualTo(m, m.add(m));
		assertIsEqualTo(m, OctMatrix.min(m, m));
		assertIsEqualTo(m, OctMatrix.max(m, m));
	}

	// closure tests ///////////////////////////////////////////////////////////////////////////////////////////////////

	@Test
	public void testStrongClosure1() {
		 OctMatrix m = OctMatrix.parseBlockLowerTriangular(
				  "0 9 "
				+ "0 0 "
				+ "0 8 0 9 "
				+ "8 2 0 0 "
				+ "7 4 8 6 0 9 "
				+ "0 3 6 7 0 0 ");
		 OctMatrix mStrongClosure = OctMatrix.parseBlockLowerTriangular(
				  "0 7 "
				+ "0 0 "
				+ "0 7 0 7 "
				+ "0 2 0 0 "
				+ "4 4 4 4 0 8 "
				+ "0 3 0 3 0 0 ");
		assertIsEqualTo(mStrongClosure, m.cachedStrongClosure());
		assertIsEqualTo(mStrongClosure, mStrongClosure.cachedStrongClosure());
	}

	@Test
	public void testStrongClosure2() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular(
				  "0.6  inf "
				+ "inf  0.6 "
				+ "inf  1.3 inf inf "
				+ "inf -1.5 4.9 inf ");
		OctMatrix mStrongClosure = OctMatrix.parseBlockLowerTriangular(
				  "0.0 -0.2 "
				+ "inf  0.0 "
				+ "inf  1.3 0.0 inf "
				+ "inf -1.5 4.9 0.0 ");
		assertIsEqualTo(mStrongClosure, m.cachedStrongClosure());
		assertIsEqualTo(mStrongClosure, mStrongClosure.cachedStrongClosure());
	}

	@Test
	public void testStrongClosure3() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular(
				  "  0 inf "
				+ "  2   0 "
				+ "inf inf   0 inf "
				+ "inf inf   4   0 ");
		OctMatrix mStrongClosure = OctMatrix.parseBlockLowerTriangular(
				  "  0 inf "
				+ "  2   0 "
				+ "inf inf   0 inf "
				+ "  3 inf   4   0 ");
		assertIsEqualTo(mStrongClosure, m.cachedStrongClosure());
		assertIsEqualTo(mStrongClosure, mStrongClosure.cachedStrongClosure());
	}

	@Test
	public void testStrongClosure4() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular(
				  "  0 inf "
				+ "  2   0 "
				+ "inf inf   0 inf "
				+ "inf inf   4   0 ");
		OctMatrix mStrongClosure = OctMatrix.parseBlockLowerTriangular(
				  "  0 inf "
				+ "  2   0 "
				+ "inf inf   0 inf "
				+ "  3 inf   4   0 ");
		assertIsEqualTo(mStrongClosure, m.cachedStrongClosure());
		assertIsEqualTo(mStrongClosure, mStrongClosure.cachedStrongClosure());
	}

	@Test
	public void testTightClosure1() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular("0 5.2 \n 2.8 0"); // v_0 \in [-2.6, 1.4]
		OctMatrix t = OctMatrix.parseBlockLowerTriangular("0 4   \n 2   0");
		assertIsEqualTo(m, m.cachedStrongClosure());
		assertIsEqualTo(t, m.cachedTightClosure());
	}

	@Test
	public void testClosuresSingeltonReals() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular("0 2.0000 \n -2 0"); // v_0 \in [-1, -1]
		Assert.assertFalse(m.cachedStrongClosure().hasNegativeSelfLoop());
		Assert.assertFalse(m.cachedTightClosure().hasNegativeSelfLoop());
	}

	@Test
	public void testClosuresBottomReals() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular("0 2 \n -3 0");
		Assert.assertTrue(m.cachedStrongClosure().hasNegativeSelfLoop());
		Assert.assertTrue(m.cachedTightClosure().hasNegativeSelfLoop());
	}

	@Test
	public void testClosuresBottomIntegers() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular(
				  "  0 inf "
				+ "inf   0 "
				+ "inf inf   0  -3 "
				+ "  3   0 inf   0 ");
		Assert.assertFalse(m.cachedStrongClosure().hasNegativeSelfLoop());
		Assert.assertTrue(m.cachedTightClosure().hasNegativeSelfLoop());
	}

//	@Test
	public void testClosureByComparingRandom() {
		for (int i = 0; i < 2000; ++i) {
			int variables = (int) (Math.random() * 10) + 1;
			OctMatrix m = OctMatrix.random(variables);
			OctMatrix cNaiv = m.strongClosure(OctMatrix::shortestPathClosureNaiv);
			OctMatrix cOther = m.cachedStrongClosure();
			if (cNaiv.hasNegativeSelfLoop() != cOther.hasNegativeSelfLoop() || !cNaiv.isEqualTo(cOther)) {
				String msg = String.format("%s%n%s%n%s%n%s%n%s%n%s%n",
						"original matrix", m,
						"strong closure (naiv)", cNaiv,
						"strong closure (other)", cOther);
				Assert.fail(msg);
			}
			// else: test passed
		}
	}

	// widening tests //////////////////////////////////////////////////////////////////////////////////////////////////

	@Test
	public void testWidenSimple() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular("  4   7   3   1");
		OctMatrix n = OctMatrix.parseBlockLowerTriangular("  9   1   3.0 5");
		OctMatrix mWn = OctMatrix.parseBlockLowerTriangular("inf 7   3   inf");
		OctMatrix nWm = OctMatrix.parseBlockLowerTriangular("9   inf 3   5");
		assertIsEqualTo(mWn, m.widenSimple(n));
		assertIsEqualTo(nWm, n.widenSimple(m));
	}

	@Test
	public void testWidenExponential() {
		OctValue threshold = new OctValue(10);
		// no widening
		OctMatrix m = OctMatrix.parseBlockLowerTriangular("5  0 3   -7");
		OctMatrix n = OctMatrix.parseBlockLowerTriangular("3 -4 3.0 -7.1");
		assertIsEqualTo(m, m.widenExponential(n, threshold));

		m = OctMatrix.parseBlockLowerTriangular("-9 -9 -9 -9");
		// negative numbers
		n = OctMatrix.parseBlockLowerTriangular("-3 -2 -1.9999999999 0");
		OctMatrix mWn = OctMatrix.parseBlockLowerTriangular("-1.5 -1 0 0");
		assertIsEqualTo(mWn, m.widenExponential(n, threshold));
		// positive numbers
		n = OctMatrix.parseBlockLowerTriangular("0.49999999 0.5 1 1.5");
		mWn = OctMatrix.parseBlockLowerTriangular("1 1 2 3");
		assertIsEqualTo(mWn, m.widenExponential(n, threshold));
		// threshold
		n = OctMatrix.parseBlockLowerTriangular("5 10 6 11");
		mWn = OctMatrix.parseBlockLowerTriangular("10 10 10 inf");
		assertIsEqualTo(mWn, m.widenExponential(n, threshold));
	}

	@Test
	public void testWidenStepwise() {
		WideningStepSupplier wss = createWideningStepSupplier("-9 -5 -3.2 4 8");
		
		OctMatrix m = OctMatrix.parseBlockLowerTriangular(  "6 -4.2 1 0");
		OctMatrix n = OctMatrix.parseBlockLowerTriangular(  "5 -4   2 9");
		OctMatrix mWn = OctMatrix.parseBlockLowerTriangular("6 -3.2 4 inf");
		assertIsEqualTo(mWn, m.widenStepwise(n, wss));
		
		m = OctMatrix.parseBlockLowerTriangular(  "4 -9    2 1");
		n = OctMatrix.parseBlockLowerTriangular(  "4 -3.20 8 1");
		mWn = OctMatrix.parseBlockLowerTriangular("4 -3.2  8 1");
		assertIsEqualTo(mWn, m.widenStepwise(n, wss));

		m = OctMatrix.parseBlockLowerTriangular(  "inf 5   1.0 1");
		n = OctMatrix.parseBlockLowerTriangular(  "5   inf 1   1.0");
		mWn = OctMatrix.parseBlockLowerTriangular("inf inf 1   1");
		assertIsEqualTo(mWn, m.widenStepwise(n, wss));
	}
	
	private WideningStepSupplier createWideningStepSupplier(String steps) {
		TreeSet<OctValue> treeSet = new TreeSet<>();
		steps = steps.trim();
		if (steps.length() > 0) {
			for (String s : steps.split("\\s+")) {
				treeSet.add(OctValue.parse(s));
			}
		}
		return new WideningStepSupplier() {
			@Override
			public OctValue nextWideningStep(OctValue v) {
				OctValue ceil = treeSet.ceiling(v);
				return (ceil == null) ? OctValue.INFINITY : ceil;
			}
		};
	}
	
	// misc tests //////////////////////////////////////////////////////////////////////////////////////////////////////

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
	public void testAddVariables() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular(
				  " 0  1 "
				+ " 2  3 "
				+ " 4  5  6  7 "
				+ " 8  9 10 11 ");
		OctMatrix a1 = OctMatrix.parseBlockLowerTriangular(
				  "  0   1 "
				+ "  2   3 "
				+ "  4   5   6   7 "
				+ "  8   9  10  11 "
				+ "inf inf inf inf inf inf "
				+ "inf inf inf inf inf inf ");
		assertIsEqualTo(a1, m.addVariables(1));
	}

	@Test
	public void testRemoveVariables() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular(
				  " 0  1 "
				+ " 2  3 "
				+ " 4  5  6  7 "
				+ " 8  9 10 11 "
				+ "12 13 14 15 16 17 "
				+ "18 19 20 21 22 23 ");
		 OctMatrix r1 = OctMatrix.parseBlockLowerTriangular(
				  " 0  1 "
				+ " 2  3 "
				+ "12 13 16 17 "
				+ "18 19 22 23 ");
		OctMatrix r12 = OctMatrix.parseBlockLowerTriangular("0 1 2 3");
		OctMatrix r02 = OctMatrix.parseBlockLowerTriangular("6 7 10 11");
		OctMatrix r01 = OctMatrix.parseBlockLowerTriangular("16 17 22 23");
		OctMatrix r012 = OctMatrix.parseBlockLowerTriangular("");
		assertIsEqualTo(r1, m.removeVariable(1));
		assertIsEqualTo(r12, m.removeVariables(asSet(1, 2)));
		assertIsEqualTo(r02, m.removeVariables(asSet(0, 2)));
		assertIsEqualTo(r01, m.removeVariables(asSet(0, 1)));
		assertIsEqualTo(r012, m.removeVariables(asSet(0, 1, 2)));
	}
	
	@Test
	public void testAppendSelection() {
		OctMatrix a = OctMatrix.parseBlockLowerTriangular(
				  "-1 -2 "
				+ "-3 -4");
		OctMatrix b = OctMatrix.parseBlockLowerTriangular(
				  "1  7 "
				+ "2  8 "
				+ "3  9 15 21 "
				+ "4 10 16 22 "
				+ "5 11 17 23 29 35 "
				+ "6 12 18 24 30 36 ");
		OctMatrix expected = OctMatrix.parseBlockLowerTriangular(
				  " -1  -2 "
				+ " -3  -4 "
				+ "inf inf   1   7 "
				+ "inf inf   2   8 "
				+ "inf inf   5  11  29  35 "
				+ "inf inf   6  12  30  36 ");
		OctMatrix actual = a.appendSelection(b, asList(0, 2));
		assertIsEqualTo(expected, actual);
	}

	@Test
	public void testCopySelection() {
		OctMatrix a = OctMatrix.parseBlockLowerTriangular(
				  "  1   9 "
				+ "  2  10 "
				+ "  3  11  19  27 "
				+ "  4  12  20  28 "
				+ "  5  13  21  29  37  45 "
				+ "  6  14  22  30  38  46 ");
		OctMatrix b = OctMatrix.parseBlockLowerTriangular(
				  " .1  .9 "
				+ " .2 .10 "
				+ " .3 .11 .19 .27 "
				+ " .4 .12 .20 .28 "
				+ " .5 .13 .21 .29 .37 .45 "
				+ " .6 .14 .22 .30 .38 .46 "
				+ " .7 .15 .23 .31 .39 .47 .55 .63 "
				+ " .8 .16 .24 .32 .40 .48 .56 .64 ");
		OctMatrix expected = OctMatrix.parseBlockLowerTriangular(
				  ".55 .63 "
				+ ".56 .64 "
				+ "inf inf  19  27 "
				+ "inf inf  20  28 "
				+ ".32 .31 inf inf .19 .27 "
				+ ".24 .23 inf inf .20 .28 ");
		BidirectionalMap<Integer, Integer> mapSourceVarToTargetVar = new BidirectionalMap<>();
		mapSourceVarToTargetVar.put(1, 2);
		mapSourceVarToTargetVar.put(3, 0);
		a.copySelection(b, mapSourceVarToTargetVar);
		assertIsEqualTo(expected, a);
	}

	// post-operator operations ////////////////////////////////////////////////////////////////////////////////////////

	@Test
	public void testCopyVar() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular(
				  " 1  2 "
				+ " 3  4 "
				+ " 5  6  7  8 "
				+ " 9 10 11 12 "
				+ "13 14 15 16 17 18 "
				+ "19 20 21 22 23 24 ");
		m.copyVar(2, 0);
		OctMatrix expected = OctMatrix.parseBlockLowerTriangular(
				  " 0  2 "
				+ " 3  0 "
				+ " 5  6  7  8 "
				+ " 9 10 11 12 "
				+ " 0  2 10  6  0  2 "
				+ " 3  0  9  5  3  0 ");
		assertIsEqualTo(expected, m);

		m = OctMatrix.parseBlockLowerTriangular(
				  " 1  2 "
				+ " 3  4 "
				+ " 5  6  7  8 "
				+ " 9 10 11 12 "
				+ "13 14 15 16 17 18 "
				+ "19 20 21 22 23 24 ");
		m.copyVar(0, 2);
		expected = OctMatrix.parseBlockLowerTriangular(
				  " 0 18 "
				+ "23  0 "
				+ "22 16  7  8 "
				+ "21 15 11 12 "
				+ " 0 18 15 16  0 18 "
				+ "23  0 21 22 23  0 ");
		assertIsEqualTo(expected, m);
		
		m = OctMatrix.parseBlockLowerTriangular(
				  " 1  2 "
				+ " 3  4 "
				+ " 5  6  7  8 "
				+ " 9 10 11 12 "
				+ "13 14 15 16 17 18 "
				+ "19 20 21 22 23 24 "
				+ "25 26 27 28 29 30 31 32 "
				+ "33 34 35 36 37 38 39 40 ");
		m.copyVar(1, 2);
		expected = OctMatrix.parseBlockLowerTriangular(
				  " 1  2 "
				+ " 3  4 "
				+ "13 14  0 18 "
				+ "19 20 23  0 "
				+ "13 14  0 18  0 18 "
				+ "19 20 23  0 23  0 "
				+ "25 26 29 30 29 30 31 32 "
				+ "33 34 37 38 37 38 39 40 ");
		assertIsEqualTo(expected, m);

	}
	
	@Test
	public void testCopyVarBottom() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular(
				  " 1  2 "
				+ " 3 -3 "
				+ " 5  6  -1  8 "
				+ " 9 10 11 12 "
				+ "13 14 15 16 17 18 "
				+ "19 20 21 22 23 24 ");
		
		m.copyVar(2, 0);
		OctMatrix expected = OctMatrix.parseBlockLowerTriangular(
				  " 0  2 "
				+ " 3 -3 "
				+ " 5  6 -1  8 "
				+ " 9 10 11 12 "
				+ " 0  2 10  6  0  2 "   // it would also be OK, if the first 0 (in this line) ...
				+ " 3 -3  9  5  3 -3 "); // ... was swapped with the first -3 (in this line).
		assertIsEqualTo(expected, m);
	}
	
	@Test
	public void testCopyVarSelf() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular(
				  " 1  2 "
				+ " 3  4 "
				+ " 1  2  3  4 "
				+ " 5  6  7  8 "
				+ " 5  6  9 10  7  8 "
				+ " 9 10 11 12 13 14 ");
		OctMatrix expected = m.copy();
		m.copyVar(1, 1);
		assertIsEqualTo(expected, m);
	}
	
	@Test
	public void testNegateVar() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular(
				  " 1  2 "
				+ " 3  4 "
				+ " 1  2  3  4 "
				+ " 5  6  7  8 "
				+ " 5  6  9 10  7  8 "
				+ " 9 10 11 12 13 14 ");
		m.negateVar(1);
		OctMatrix expected = OctMatrix.parseBlockLowerTriangular(
				  " 1  2 "
				+ " 3  4 "
				+ " 5  6  8  7 "
				+ " 1  2  4  3 "
				+ " 5  6 10  9  7  8 "
				+ " 9 10 12 11 13 14 ");
		assertIsEqualTo(expected, m);
	}

	@Test
	public void testIncrementVar() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular(
				  "  0   2 "
				+ "  3  .2 "
				+ "  5 inf  .3   8 "
				+ "inf  10  11   0 ");
		m.incrementVar(0, new OctValue(1));
		OctMatrix expected = OctMatrix.parseBlockLowerTriangular(
				  "  0   0 "
				+ "  5  .2 "
				+ "  6 inf  .3   8 "
				+ "inf   9  11   0 ");
		assertIsEqualTo(expected, m);
		
		m.incrementVar(1, new OctValue(-2));
		expected = OctMatrix.parseBlockLowerTriangular(
				  "  0   0 "
				+ "  5  .2 "
				+ "  8 inf  .3  12 "
				+ "inf   7   7   0 ");
		assertIsEqualTo(expected, m);
	}
	
	@Test
	public void testAssignVarConstant() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular(
				  "  1   2 "
				+ "  3   4 "
				+ "  5   6   7   8 "
				+ "  9  10  11  12 ");
		m.assignVarConstant(0, new OctValue(-3));
		OctMatrix expected = OctMatrix.parseBlockLowerTriangular(
				  "  0   6 "
				+ " -6   0 "
				+ "inf inf  7   8 "
				+ "inf inf  11  12 ");
		assertIsEqualTo(expected, m);

		m = OctMatrix.parseBlockLowerTriangular(
				  "  1   2 "
				+ "  3   4 "
				+ "  5   6   7   8 "
				+ "  9  10  11  12 ");
		m.assignVarConstant(1, new OctValue(2));
		expected = OctMatrix.parseBlockLowerTriangular(
				  "  1   2 "
				+ "  3   4 "
				+ "inf inf  0  -4 "
				+ "inf inf  4   0 ");
		assertIsEqualTo(expected, m);
		
		try {
			m.incrementVar(0, OctValue.INFINITY);
			Assert.fail("Variable set to constant inf\n" + m); // actually, inf would be OK (but cannot be stored)
		} catch (Exception e) {
			// test passed
		}
	}
	

	@Test
	public void testAssignVarInterval() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular(
				  "  1   2 "
				+ "  3   4 "
				+ "  5   6   7   8 "
				+ "  9  10  11  12 ");
		m.assignVarInterval(0, new OctValue(-3), new OctValue(2));
		OctMatrix expected = OctMatrix.parseBlockLowerTriangular(
				  "  0   6 "
				+ "  4   0 "
				+ "inf inf  7   8 "
				+ "inf inf  11  12 ");
		assertIsEqualTo(expected, m);

		m = OctMatrix.parseBlockLowerTriangular(
				  "  1   2 "
				+ "  3   4 "
				+ "  5   6   7   8 "
				+ "  9  10  11  12 ");
		m.assignVarInterval(1, new OctValue(-4), new OctValue(-1));
		expected = OctMatrix.parseBlockLowerTriangular(
				  "  1   2 "
				+ "  3   4 "
				+ "inf inf   0   8 "
				+ "inf inf  -2   0 ");
		assertIsEqualTo(expected, m);
		
		m.assignVarInterval(0, OctValue.INFINITY, new OctValue(3));
		expected = OctMatrix.parseBlockLowerTriangular(
				  "  0 inf "
				+ "  6   0 "
				+ "inf inf   0   8 "
				+ "inf inf  -2   0 ");
		assertIsEqualTo(expected, m);
		
		m.assignVarInterval(0, new OctValue(3), OctValue.INFINITY);
		expected = OctMatrix.parseBlockLowerTriangular(
				  "  0  -6 "
				+ "inf   0 "
				+ "inf inf   0   8 "
				+ "inf inf  -2   0 ");
		assertIsEqualTo(expected, m);
		
	}

	@Test
	public void testHavocVar() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular(
				  "  1   2 "
				+ "  3   4 "
				+ "  5   6   7   8 "
				+ "  9  10  11  12 ");
		m.havocVar(0);
		OctMatrix expected = OctMatrix.parseBlockLowerTriangular(
				  "  0 inf "
				+ "inf   0 "
				+ "inf inf  7   8 "
				+ "inf inf  11  12 ");
		assertIsEqualTo(expected, m);

		m = OctMatrix.parseBlockLowerTriangular(
				  "  1   2 "
				+ "  3   4 "
				+ "  5   6   7   8 "
				+ "  9  10  11  12 ");
		m.havocVar(1);
		expected = OctMatrix.parseBlockLowerTriangular(
				  "  1   2 "
				+ "  3   4 "
				+ "inf inf   0 inf "
				+ "inf inf inf   0 ");
		assertIsEqualTo(expected, m);
	}
	
	// relations ///////////////////////////////////////////////////////////////////////////////////////////////////////

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
	public void testIsEqualTo() {
		OctMatrix m = OctMatrix.parseBlockLowerTriangular("");
		OctMatrix n = OctMatrix.parseBlockLowerTriangular("");
		Assert.assertTrue(m.isEqualTo(n));
		Assert.assertTrue(n.isEqualTo(m));

		OctMatrix m2 = OctMatrix.parseBlockLowerTriangular("4 -9 inf 3.0000");
		OctMatrix n2 = OctMatrix.parseBlockLowerTriangular("4 -9.0 inf 3");
		Assert.assertTrue(m2.isEqualTo(n2));
		Assert.assertTrue(n2.isEqualTo(m2));

		OctMatrix o = OctMatrix.parseBlockLowerTriangular("4 -9 inf 3.00001");
		Assert.assertFalse(m2.isEqualTo(o));
		Assert.assertFalse(o.isEqualTo(m2));

	}

	@Test
	public void testIsEqualToPermutation() {
		OctMatrix a = OctMatrix.parseBlockLowerTriangular(
				  " 0  1 "
				+ " 2  3 "
				+ " 4  5  6  7 "
				+ " 8  9 10 11 ");
		OctMatrix b = OctMatrix.parseBlockLowerTriangular(
				  " 6  7 "
				+ "10 11 "
				+ " 9  5  0  1 "
				+ " 8  4  2  3 ");
		int[] mapAVarIndexToBVarIndex = {1, 0};
		Assert.assertTrue(a.isEqualToPermutation(b, mapAVarIndexToBVarIndex));
	}

	@Test
	public void testIsBlockEqualTo() {
		OctMatrix a = OctMatrix.parseBlockLowerTriangular(
				  " 0  1 "
				+ " 2  3 "
				+ " 4  5  6  7 "
				+ " 8  9 10 11 ");
		OctMatrix b = OctMatrix.parseBlockLowerTriangular(
				  " 6  7 "
				+ "10 11 "
				+ " 9  5  0  1 "
				+ " 8  4  2  3 ");
		Assert.assertTrue(a.isBlockEqualTo(1, 0, a, 1, 0));
		Assert.assertTrue(a.isBlockEqualTo(0, 0, b, 1, 1));
		Assert.assertTrue(b.isBlockEqualTo(1, 1, a, 0, 0));
		Assert.assertTrue(a.isBlockEqualTo(1, 0, b, 0, 1));
		Assert.assertFalse(a.isBlockEqualTo(1, 0, b, 1, 0));
	}

	// utilities ///////////////////////////////////////////////////////////////////////////////////////////////////////

	private void assertIsEqualTo(OctMatrix expected, OctMatrix actual) {
		String msg = "expected:\n" + expected + "acutal:\n" + actual;
		Assert.assertTrue(msg, expected.isEqualTo(actual));
	}

	private Set<Integer> asSet(Integer... elements) {
		return new HashSet<Integer>(asList(elements));
	}

	private List<Integer> asList(Integer... elements) {
		return Arrays.asList(elements);
	}
}
