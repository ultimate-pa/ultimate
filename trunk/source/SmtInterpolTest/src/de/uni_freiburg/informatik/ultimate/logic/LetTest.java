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

import junit.framework.TestCase;

public class LetTest extends TestCase {

	private final static Sort[] EMPTY_SORTS = {};
	
	public void testNoLet() {
		Theory theory = new Theory(Logics.AUFLIA);
		Sort intSort = theory.getNumericSort();
		theory.declareFunction("i", EMPTY_SORTS, intSort);
		theory.declareFunction("j", EMPTY_SORTS, intSort);
		Term i = theory.term("i");
		FormulaLet let = new FormulaLet();
		Term leti = let.let(i);
		assertSame(i, new FormulaUnLet().unlet(leti));
		assertSame(i, leti);
		Term ij = theory.term("+", i, theory.term("j"));
		Term letij = let.let(ij);
		assertSame(ij, new FormulaUnLet().unlet(letij));
		assertSame(ij, letij);
	}
	
	public void testArith() {
		Theory theory = new Theory(Logics.AUFLIA);
		Sort intSort = theory.getNumericSort();
		theory.declareFunction("i", EMPTY_SORTS, intSort);
		theory.declareFunction("j", EMPTY_SORTS, intSort);
		FormulaLet let = new FormulaLet();
		Term toLet = theory.term("+", theory.term("i"), theory.term("j"));
		Term input = theory.term("+", toLet, toLet);
		Term output = let.let(input);
		assertSame(input, new FormulaUnLet().unlet(output));
		TermVariable cse0 = theory.createTermVariable(".cse0", intSort);
		Term expected = theory.let(cse0, toLet, theory.term("+", cse0, cse0));
		assertSame(expected, output);
	}
	
	public void testLet() {
		Theory theory = new Theory(Logics.AUFLIA);
		Sort intSort = theory.getNumericSort();
		theory.declareFunction("i", EMPTY_SORTS, intSort);
		theory.declareFunction("j", EMPTY_SORTS, intSort);
		Term ij = theory.term("+", theory.term("i"), theory.term("j"));
		FormulaLet let = new FormulaLet();
		TermVariable x = theory.createTermVariable("x", intSort);
		Term toLet = theory.term("+", x, x);
		Term input = theory.let(x, ij, theory.term("+", toLet, toLet));
		Term output = let.let(input);
		assertSame(new FormulaUnLet().unlet(input), new FormulaUnLet().unlet(output));
		TermVariable cse1 = theory.createTermVariable(".cse1", intSort);
		TermVariable cse0 = theory.createTermVariable(".cse0", intSort);
		Term expected =  
				theory.let(cse0, theory.let(cse1, ij, theory.term("+", cse1, cse1)), 
						theory.term("+", cse0, cse0));
		assertSame(expected, output);
		TermVariable y = theory.createTermVariable("y", intSort);
		TermVariable z = theory.createTermVariable("z", intSort);
		Term xz = theory.term("+", x, z);
		input = theory.let(y, ij,
				theory.let(x, theory.term("+", y, theory.numeral("1")), 
						theory.let(z, theory.term("+", y, theory.numeral("1")),
								theory.term("+", xz, xz))));
		output = let.let(input);
		assertSame(new FormulaUnLet().unlet(input), new FormulaUnLet().unlet(output));
		expected = theory.let(cse0, 
				theory.let(cse1, theory.term("+", ij, theory.numeral("1")),
								theory.term("+", cse1, cse1)),
							theory.term("+", cse0, cse0));
		assertSame(expected, output);
	}
	
	public void testStuff() {
		Theory theory = new Theory(Logics.QF_UF);
		theory.declareSort("U", 0);
		Sort u = theory.getSort("U");
		Sort[] unary = { u };
		Sort[] binary = { u, u };
		theory.declareFunction("a", unary, u);
		theory.declareFunction("b", unary, u);
		theory.declareFunction("c", unary, u);
		theory.declareFunction("f", unary, u);
		theory.declareFunction("g", binary, u);
		theory.declareFunction("h", unary, u);
		theory.declareFunction("i", unary, u);
		theory.declareFunction("x", EMPTY_SORTS, u);
		theory.declareFunction("y", EMPTY_SORTS, u);
		theory.declareFunction("m", binary, u);
		theory.declareFunction("n", unary, u);
		Term nx = theory.term("n", theory.term("x"));
		Term mnx = theory.term("m", nx, nx);
		Term y = theory.term("y");
		Term big = theory.term("f", theory.term("g",
				theory.term("h", theory.term("i", mnx)), mnx));
		Term small = theory.term("a", theory.term("b", theory.term("c", mnx)));
		Term eq1 = theory.equals(big, y);
		Term eq2 = theory.equals(small, nx);
		Term andTerm = theory.and(eq1, eq2);
		FormulaLet let = new FormulaLet();
		Term output = let.let(andTerm);
		assertSame(andTerm, new FormulaUnLet().unlet(output));
		TermVariable cse1 = theory.createTermVariable(".cse1", u);
		TermVariable cse0 = theory.createTermVariable(".cse0", u);
		Term expected = theory.let(cse1, nx,
				theory.let(cse0, theory.term("m", cse1, cse1), theory.and(
					theory.equals(theory.term("f", 
							theory.term("g", 
									theory.term("h", 
											theory.term("i", cse0)),
									cse0)),
							y),
					theory.equals(
							theory.term("a", 
									theory.term("b",
											theory.term("c", cse0))),
							cse1))));
		assertSame(expected, output);
	}
	
	public void testScope() {
		Theory theory = new Theory(Logics.AUFLIA);
		theory.declareSort("U", 0);
		Sort u = theory.getSort("U");
		Sort[] unary = { u };
		Sort[] binary = { theory.getBooleanSort(), theory.getBooleanSort() };
		theory.declareFunction("P", unary, theory.getBooleanSort());
		theory.declareFunction("f", binary, theory.getBooleanSort());
		TermVariable x = theory.createTermVariable("x", u);
		TermVariable[] xarray = { x };
		Term px = theory.term("P", x);
		Term inner = theory.term("f", px, px);
		Term quant = theory.forall(xarray, inner);
		Term outer = theory.term("f", quant, quant);
		FormulaLet let = new FormulaLet();
		Term output = let.let(outer);
		assertSame(outer, new FormulaUnLet().unlet(output));
		TermVariable cse0 = theory.createTermVariable(".cse0", theory.getBooleanSort());
		TermVariable cse1 = theory.createTermVariable(".cse1", theory.getBooleanSort());
		Term expected = theory.let(cse0,
				theory.forall(xarray, 
						theory.let(cse1, px,
								theory.term("f", cse1, cse1))),
								theory.term("f", cse0, cse0));
		assertSame(expected, output);
	}
	
}
