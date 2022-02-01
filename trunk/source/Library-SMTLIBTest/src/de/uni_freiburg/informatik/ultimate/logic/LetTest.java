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

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

@RunWith(JUnit4.class)
public class LetTest {

	@Test
	public void testNoLet() {
		final Theory theory = new Theory(Logics.AUFLIA);
		final Sort intSort = theory.getNumericSort();
		theory.declareFunction("i", Script.EMPTY_SORT_ARRAY, intSort);
		theory.declareFunction("j", Script.EMPTY_SORT_ARRAY, intSort);
		final Term i = theory.term("i");
		final FormulaLet let = new FormulaLet();
		final Term leti = let.let(i);
		Assert.assertSame(i, new FormulaUnLet().unlet(leti));
		Assert.assertSame(i, leti);
		final Term ij = theory.term("+", i, theory.term("j"));
		final Term letij = let.let(ij);
		Assert.assertSame(ij, new FormulaUnLet().unlet(letij));
		Assert.assertSame(ij, letij);
	}

	@Test
	public void testArith() {
		final Theory theory = new Theory(Logics.AUFLIA);
		final Sort intSort = theory.getNumericSort();
		theory.declareFunction("i", Script.EMPTY_SORT_ARRAY, intSort);
		theory.declareFunction("j", Script.EMPTY_SORT_ARRAY, intSort);
		final FormulaLet let = new FormulaLet();
		final Term toLet = theory.term("+", theory.term("i"), theory.term("j"));
		final Term input = theory.term("+", toLet, toLet);
		final Term output = let.let(input);
		Assert.assertSame(input, new FormulaUnLet().unlet(output));
		final TermVariable cse0 = theory.createTermVariable(".cse0", intSort);
		final Term expected = theory.let(cse0, toLet, theory.term("+", cse0, cse0));
		Assert.assertSame(expected, output);
	}

	@Test
	public void testLet() {
		final Theory theory = new Theory(Logics.AUFLIA);
		final Sort intSort = theory.getNumericSort();
		theory.declareFunction("i", Script.EMPTY_SORT_ARRAY, intSort);
		theory.declareFunction("j", Script.EMPTY_SORT_ARRAY, intSort);
		final Term ij = theory.term("+", theory.term("i"), theory.term("j"));
		final FormulaLet let = new FormulaLet();
		final TermVariable x = theory.createTermVariable("x", intSort);
		final Term toLet = theory.term("+", x, x);
		Term input = theory.let(x, ij, theory.term("+", toLet, toLet));
		Term output = let.let(input);
		Assert.assertSame(new FormulaUnLet().unlet(input), new FormulaUnLet().unlet(output));
		final TermVariable cse1 = theory.createTermVariable(".cse1", intSort);
		final TermVariable cse0 = theory.createTermVariable(".cse0", intSort);
		Term expected =
				theory.let(cse0, theory.let(cse1, ij, theory.term("+", cse1, cse1)), theory.term("+", cse0, cse0));
		Assert.assertSame(expected, output);
		final TermVariable y = theory.createTermVariable("y", intSort);
		final TermVariable z = theory.createTermVariable("z", intSort);
		final Term xz = theory.term("+", x, z);
		input = theory.let(y, ij, theory.let(x, theory.term("+", y, theory.numeral("1")),
				theory.let(z, theory.term("+", y, theory.numeral("1")), theory.term("+", xz, xz))));
		output = let.let(input);
		Assert.assertSame(new FormulaUnLet().unlet(input), new FormulaUnLet().unlet(output));
		expected = theory.let(cse0,
				theory.let(cse1, theory.term("+", ij, theory.numeral("1")), theory.term("+", cse1, cse1)),
				theory.term("+", cse0, cse0));
		Assert.assertSame(expected, output);
	}

	@Test
	public void testStuff() {
		final Theory theory = new Theory(Logics.QF_UF);
		theory.declareSort("U", 0);
		final Sort u = theory.getSort("U");
		final Sort[] unary = { u };
		final Sort[] binary = { u, u };
		theory.declareFunction("a", unary, u);
		theory.declareFunction("b", unary, u);
		theory.declareFunction("c", unary, u);
		theory.declareFunction("f", unary, u);
		theory.declareFunction("g", binary, u);
		theory.declareFunction("h", unary, u);
		theory.declareFunction("i", unary, u);
		theory.declareFunction("x", Script.EMPTY_SORT_ARRAY, u);
		theory.declareFunction("y", Script.EMPTY_SORT_ARRAY, u);
		theory.declareFunction("m", binary, u);
		theory.declareFunction("n", unary, u);
		final Term nx = theory.term("n", theory.term("x"));
		final Term mnx = theory.term("m", nx, nx);
		final Term y = theory.term("y");
		final Term big = theory.term("f", theory.term("g", theory.term("h", theory.term("i", mnx)), mnx));
		final Term small = theory.term("a", theory.term("b", theory.term("c", mnx)));
		final Term eq1 = theory.equals(big, y);
		final Term eq2 = theory.equals(small, nx);
		final Term andTerm = theory.and(eq1, eq2);
		final FormulaLet let = new FormulaLet();
		final Term output = let.let(andTerm);
		Assert.assertSame(andTerm, new FormulaUnLet().unlet(output));
		final TermVariable cse1 = theory.createTermVariable(".cse1", u);
		final TermVariable cse0 = theory.createTermVariable(".cse0", u);
		final Term expected =
				theory.let(
						cse1, nx, theory
								.let(cse0, theory.term("m", cse1, cse1),
										theory.and(
												theory.equals(theory.term("f",
														theory.term("g", theory.term("h", theory.term("i", cse0)),
																cse0)),
														y),
												theory.equals(
														theory.term("a", theory.term("b", theory.term("c", cse0))),
														cse1))));
		Assert.assertSame(expected, output);
	}

	@Test
	public void testScope() {
		final Theory theory = new Theory(Logics.AUFLIA);
		theory.declareSort("U", 0);
		final Sort u = theory.getSort("U");
		final Sort[] unary = { u };
		final Sort[] binary = { theory.getBooleanSort(), theory.getBooleanSort() };
		theory.declareFunction("P", unary, theory.getBooleanSort());
		theory.declareFunction("f", binary, theory.getBooleanSort());
		final TermVariable x = theory.createTermVariable("x", u);
		final TermVariable[] xarray = { x };
		final Term px = theory.term("P", x);
		final Term inner = theory.term("f", px, px);
		final Term quant = theory.forall(xarray, inner);
		final Term outer = theory.term("f", quant, quant);
		final FormulaLet let = new FormulaLet();
		final Term output = let.let(outer);
		Assert.assertSame(outer, new FormulaUnLet().unlet(output));
		final TermVariable cse0 = theory.createTermVariable(".cse0", theory.getBooleanSort());
		final TermVariable cse1 = theory.createTermVariable(".cse1", theory.getBooleanSort());
		final Term expected =
				theory.let(cse0, theory.forall(xarray, theory.let(cse1, px, theory.term("f", cse1, cse1))),
						theory.term("f", cse0, cse0));
		Assert.assertSame(expected, output);
	}

}
