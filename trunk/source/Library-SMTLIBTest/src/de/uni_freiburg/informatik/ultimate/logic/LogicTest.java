/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.logic;

import static org.junit.Assert.assertTrue;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.Logics.Features;

@RunWith(JUnit4.class)
public class LogicTest {

	private class LogicCase {
		String mName;
		int mFeatures;

		public LogicCase(String name, int features) {
			mName = name;
			mFeatures = features;
		}
	}

	LogicCase[] standardLogics = {
		new LogicCase("CORE", 0),// Pure Boolean logic
		new LogicCase("ALL",       Features.QU + Features.NA + Features.IA + Features.RA +
				Features.BV + Features.UF + Features.AX + Features.FP + Features.DT + Features.S),
		new LogicCase("HORN",      Features.QU + Features.NA + Features.IA + Features.RA +
				Features.BV + Features.UF + Features.AX + Features.FP + Features.DT + Features.S),
		new LogicCase("QF_ABV",    Features.AX + Features.BV),
		new LogicCase("QF_ABVFP",  Features.AX + Features.BV + Features.FP),
		new LogicCase("QF_ABVFPLRA", Features.AX + Features.BV + Features.FP + Features.LA + Features.RA),
		new LogicCase("QF_ALIA", Features.AX + Features.LA + Features.IA),
		new LogicCase("QF_ANIA", Features.AX + Features.NA + Features.IA),
		new LogicCase("QF_AUFBV", Features.AX + Features.UF + Features.BV),
		new LogicCase("QF_AUFBVFP", Features.AX + Features.UF + Features.BV + Features.FP),
		new LogicCase("QF_AUFBVFPLRA", Features.AX + Features.UF + Features.BV + Features.FP + Features.LA + Features.RA),
		new LogicCase("QF_AUFBVLIA", Features.AX + Features.UF + Features.BV + Features.LA + Features.IA),
		new LogicCase("QF_AUFBVNIA", Features.AX + Features.UF + Features.BV + Features.NA + Features.IA),
		new LogicCase("QF_AUFLIA", Features.AX + Features.UF + Features.LA + Features.IA),
		new LogicCase("QF_AUFLIRA", Features.AX + Features.UF + Features.LA + Features.IA + Features.RA),
		new LogicCase("QF_AUFNIA", Features.AX + Features.UF + Features.NA + Features.IA),
		new LogicCase("QF_AUFNIRA", Features.AX + Features.UF + Features.NA + Features.IA + Features.RA),
		new LogicCase("QF_AX", Features.AX),
		new LogicCase("QF_BV", Features.BV),
		new LogicCase("QF_BVFP", Features.BV + Features.FP),
		new LogicCase("QF_BVFPLRA", Features.BV + Features.FP + Features.LA + Features.RA),
		new LogicCase("QF_BVLRA", Features.BV + Features.LA + Features.RA),
		new LogicCase("QF_DT", Features.DT),
		new LogicCase("QF_FP", Features.FP),
		new LogicCase("QF_FPLRA", Features.FP + Features.LA + Features.RA),
		new LogicCase("QF_IDL", Features.DL + Features.IA),
		new LogicCase("QF_LIA", Features.LA + Features.IA),
		new LogicCase("QF_LIRA", Features.LA + Features.RA + Features.IA),
		new LogicCase("QF_LRA", Features.LA + Features.RA),
		new LogicCase("QF_NIA", Features.NA + Features.IA),
		new LogicCase("QF_NIRA", Features.NA + Features.RA + Features.IA),
		new LogicCase("QF_NRA", Features.NA + Features.RA),
		new LogicCase("QF_RDL", Features.DL + Features.RA),
		new LogicCase("QF_S", Features.S),
		new LogicCase("QF_SLIA", Features.S + Features.LA + Features.IA),
		new LogicCase("QF_SNIA", Features.S + Features.NA + Features.IA),
		new LogicCase("QF_UF", Features.UF),
		new LogicCase("QF_UFBV", Features.UF + Features.BV),
		new LogicCase("QF_UFBVDT", Features.UF + Features.BV + Features.DT),
		new LogicCase("QF_UFBVFP", Features.UF + Features.BV + Features.FP),
		new LogicCase("QF_UFBVLIA", Features.UF + Features.BV + Features.LA + Features.IA),
		new LogicCase("QF_UFDT", Features.UF + Features.DT),
		new LogicCase("QF_UFDTNIA", Features.UF + Features.DT + Features.NA + Features.IA),
		new LogicCase("QF_UFDTLIA", Features.UF + Features.DT + Features.LA + Features.IA),
		new LogicCase("QF_UFDTLIRA", Features.UF + Features.DT + Features.LA + Features.IA + Features.RA),
		new LogicCase("QF_UFFP", Features.UF + Features.FP),
		new LogicCase("QF_UFFPDTLIRA", Features.UF + Features.FP + Features.DT + Features.LA + Features.IA + Features.RA),
		new LogicCase("QF_UFFPDTNIRA", Features.UF + Features.FP + Features.DT + Features.NA + Features.IA + Features.RA),
		new LogicCase("QF_UFIDL", Features.UF + Features.DL + Features.IA),
		new LogicCase("QF_UFLIA", Features.UF + Features.LA + Features.IA),
		new LogicCase("QF_UFLIRA", Features.UF + Features.LA + Features.IA + Features.RA),
		new LogicCase("QF_UFLRA", Features.UF + Features.LA + Features.RA),
		new LogicCase("QF_UFNIA", Features.UF + Features.NA + Features.IA),
		new LogicCase("QF_UFNIRA", Features.UF + Features.NA + Features.IA + Features.RA),
		new LogicCase("QF_UFNRA", Features.UF + Features.NA + Features.RA),

		new LogicCase("ABV", Features.QU + Features.AX + Features.BV),
		new LogicCase("ABVFP", Features.QU + Features.AX + Features.BV + Features.FP),
		new LogicCase("ABVFPLRA", Features.QU + Features.AX + Features.BV + Features.FP + Features.LA + Features.RA),
		new LogicCase("ALIA", Features.QU + Features.AX + Features.LA + Features.IA),
		new LogicCase("ANIA", Features.QU + Features.AX + Features.NA + Features.IA),
		new LogicCase("AUFBV", Features.QU + Features.AX + Features.UF + Features.BV),
		new LogicCase("AUFBVDTLIA", Features.QU + Features.AX + Features.UF + Features.BV + Features.DT + Features.LA + Features.IA),
		new LogicCase("AUFBVDTNIA", Features.QU + Features.AX + Features.UF + Features.BV + Features.DT + Features.NA + Features.IA),
		new LogicCase("AUFBVDTNIRA", Features.QU + Features.AX + Features.UF + Features.BV + Features.DT + Features.NA + Features.IA + Features.RA),
		new LogicCase("AUFBVFP", Features.QU + Features.AX + Features.UF + Features.BV + Features.FP),
		new LogicCase("AUFDTLIA", Features.QU + Features.AX + Features.UF + Features.DT + Features.LA + Features.IA),
		new LogicCase("AUFDTNIA", Features.QU + Features.AX + Features.UF + Features.DT + Features.NA + Features.IA),
		new LogicCase("AUFDTLIRA", Features.QU + Features.AX + Features.UF + Features.DT + Features.LA + Features.IA + Features.RA),
		new LogicCase("AUFDTNIRA", Features.QU + Features.AX + Features.UF + Features.DT + Features.NA + Features.IA + Features.RA),
		new LogicCase("AUFFPDTLIRA", Features.QU + Features.AX + Features.UF + Features.FP + Features.DT + Features.LA + Features.IA + Features.RA),
		new LogicCase("AUFFPDTNIRA", Features.QU + Features.AX + Features.UF + Features.FP + Features.DT + Features.NA + Features.IA + Features.RA),
		new LogicCase("AUFLIA", Features.QU + Features.AX + Features.UF + Features.LA + Features.IA),
		new LogicCase("AUFLIRA", Features.QU + Features.AX + Features.UF + Features.LA + Features.IA + Features.RA),
		new LogicCase("AUFNIA", Features.QU + Features.AX + Features.UF + Features.NA + Features.IA),
		new LogicCase("AUFNIRA", Features.QU + Features.AX + Features.UF + Features.NA + Features.IA + Features.RA),
		new LogicCase("BV", Features.QU + Features.BV),
		new LogicCase("BVFP", Features.QU + Features.BV + Features.FP),
		new LogicCase("BVFPLRA", Features.QU + Features.BV + Features.FP + Features.LA + Features.RA),
		new LogicCase("FP", Features.QU + Features.FP),
		new LogicCase("FPLRA", Features.QU + Features.FP + Features.LA + Features.RA),
		new LogicCase("LIA", Features.QU + Features.LA + Features.IA),
		new LogicCase("LRA", Features.QU + Features.LA + Features.RA),
		new LogicCase("NIA", Features.QU + Features.NA + Features.IA),
		new LogicCase("NRA", Features.QU + Features.NA + Features.RA),
		new LogicCase("UF", Features.QU + Features.UF),
		new LogicCase("UFBV", Features.QU + Features.UF + Features.BV),
		new LogicCase("UFBVDT", Features.QU + Features.UF + Features.BV + Features.DT),
		new LogicCase("UFBVFP", Features.QU + Features.UF + Features.BV + Features.FP),
		new LogicCase("UFBVLIA", Features.QU + Features.UF + Features.BV + Features.LA + Features.IA),
		new LogicCase("UFBVDTLIA", Features.QU + Features.UF + Features.BV + Features.DT + Features.LA + Features.IA),
		new LogicCase("UFBVDTNIA", Features.QU + Features.UF + Features.BV + Features.DT + Features.NA + Features.IA),
		new LogicCase("UFBVDTNIRA", Features.QU + Features.UF + Features.BV + Features.DT + Features.NA + Features.IA + Features.RA),
		new LogicCase("UFDT", Features.QU + Features.UF + Features.DT),
		new LogicCase("UFDTLIA", Features.QU + Features.DT + Features.UF + Features.LA + Features.IA),
		new LogicCase("UFDTLIRA", Features.QU + Features.DT + Features.UF + Features.LA + Features.IA + Features.RA),
		new LogicCase("UFDTNIA", Features.QU + Features.DT + Features.UF + Features.NA + Features.IA),
		new LogicCase("UFDTNIRA", Features.QU + Features.DT + Features.UF + Features.NA + Features.IA + Features.RA),
		new LogicCase("UFFPDTLIRA", Features.QU + Features.FP + Features.DT + Features.UF + Features.LA + Features.IA + Features.RA),
		new LogicCase("UFFPDTNIRA", Features.QU + Features.FP + Features.DT + Features.UF + Features.NA + Features.IA + Features.RA),
		new LogicCase("UFIDL", Features.QU + Features.UF + Features.DL + Features.IA),
		new LogicCase("UFLIA", Features.QU + Features.UF + Features.LA + Features.IA),
		new LogicCase("UFLRA", Features.QU + Features.UF + Features.LA + Features.RA),
		new LogicCase("UFNIA", Features.QU + Features.UF + Features.NA + Features.IA),
		new LogicCase("UFNIRA", Features.QU + Features.UF + Features.NA + Features.IA + Features.RA),
		new LogicCase("UFNRA", Features.QU + Features.UF + Features.NA + Features.RA)
	};

	@Test
	public void testStandardLogics() {
		for (int i = 0; i < standardLogics.length; i++) {
			final Logics logic = Logics.valueOf(standardLogics[i].mName);
			Assert.assertEquals(logic.getFeatures(), standardLogics[i].mFeatures);
		}
	}

	@Test
	public void testLIRA() {
		final Theory theory = new Theory(Logics.valueOf("AUFLIRA"));
		final Sort sortInt = theory.getSort("Int");
		final Sort sortReal = theory.getSort("Real");
		assertThrowsSMTLIBException(() -> theory.getFunction("-"));
		final FunctionSymbol minusInt1 = theory.getFunction("-", sortInt);
		final FunctionSymbol minusInt2 = theory.getFunction("-", sortInt, sortInt);
		Assert.assertNotNull(minusInt1);
		Assert.assertNotNull(minusInt2);
		Assert.assertSame(minusInt2, theory.getFunction("-", sortInt, sortInt, sortInt));
		assertThrowsSMTLIBException(() -> theory.getFunction("+"));
		assertThrowsSMTLIBException(() -> theory.getFunction("+", sortInt));
		final FunctionSymbol plusInt2 = theory.getFunction("+", sortInt, sortInt);
		Assert.assertNotNull(plusInt2);
		Assert.assertSame(plusInt2, theory.getFunction("+", sortInt, sortInt, sortInt));

		final FunctionSymbol minusReal1 = theory.getFunction("-", sortReal);
		final FunctionSymbol minusReal2 = theory.getFunction("-", sortReal, sortReal);
		Assert.assertNotNull(minusReal1);
		Assert.assertNotNull(minusReal2);
		Assert.assertSame(minusReal2, theory.getFunction("-", sortReal, sortReal, sortReal));

		assertThrowsSMTLIBException(() -> theory.getFunction("+", sortReal));
		final FunctionSymbol plusReal2 = theory.getFunction("+", sortReal, sortReal);
		Assert.assertNotNull(plusReal2);
		Assert.assertSame(plusReal2, theory.getFunction("+", sortReal, sortReal, sortReal));
		final FunctionSymbol plusRealIntReal = theory.getFunction("+", sortReal, sortInt, sortReal);
		final FunctionSymbol plusIntIntReal = theory.getFunction("+", sortInt, sortInt, sortReal);
		Assert.assertNotNull(plusRealIntReal);
		Assert.assertNotNull(plusIntIntReal);

		final Term x = theory.term(theory.declareFunction("x", new Sort[0], sortReal));
		final Term y = theory.term(theory.declareFunction("y", new Sort[0], sortReal));
		final Term i = theory.term(theory.declareFunction("i", new Sort[0], sortInt));
		final Term j = theory.term(theory.declareFunction("j", new Sort[0], sortInt));
		final Term sum = theory.term("+", x, y, i, j);
		final Term sum1 = theory.term("+", x, i, y);
		final Term sum2 = theory.term("+", i, j, x);
		Assert.assertSame(plusRealIntReal, ((ApplicationTerm) sum1).getFunction());
		Assert.assertSame(plusIntIntReal, ((ApplicationTerm) sum2).getFunction());
		final Term mul = theory.term("*", Rational.valueOf(-3, 7).toTerm(sortReal), i);
		Assert.assertEquals("(+ x y i j)", sum.toString());
		Assert.assertEquals("(+ x i y)", sum1.toString());
		Assert.assertEquals("(+ i j x)", sum2.toString());
		Assert.assertEquals("(* (/ (- 3.0) 7.0) i)", mul.toString());
	}

	private Sort bitvec(final Theory theory, final int len) {
		return theory.getSort("BitVec", new String[] { String.valueOf(len) });
	}

	@Test
	public void testBV() {
		final Theory theory = new Theory(Logics.valueOf("QF_BV"));
		final Term bvABCD = theory.hexadecimal("#xABCD");
		final Term bv1111 = theory.binary("#b1111");
		Assert.assertEquals(bitvec(theory, 16), bvABCD.getSort());// NOCHECKSTYLE
		Assert.assertEquals(bitvec(theory, 4), bv1111.getSort());// NOCHECKSTYLE
		final Term bv2 = theory.term("concat", bvABCD, bv1111);
		Assert.assertEquals(bitvec(theory, 20), bv2.getSort());// NOCHECKSTYLE
		final Term bv5 = theory.term("bv5", new String[] { String.valueOf(3) }, null);
		final Term bv3 = theory.term("bv3", new String[] { String.valueOf(5) }, null);
		Assert.assertEquals(bitvec(theory, 3), bv5.getSort());// NOCHECKSTYLE
		Assert.assertEquals(bitvec(theory, 5), bv3.getSort());// NOCHECKSTYLE
		Assert.assertEquals(bitvec(theory, 8), theory.term("concat", bv3, bv5).getSort());// NOCHECKSTYLE
	}

	private void assertThrowsSMTLIBException(Runnable code) {
		try {
			code.run();
			assertTrue(false);
		} catch (final SMTLIBException ex) {
			return;
		}
	}
}
