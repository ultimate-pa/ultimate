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

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet.UnletType;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

import junit.framework.TestCase;

public class UnfletTest extends TestCase {
	Theory theory = new Theory(Logics.AUFLIRA);
	
	Sort intSort = theory.getSort("Int");
	Sort[] int2 = arr(intSort, intSort);
	TermVariable x = theory.createTermVariable("x", intSort);
	TermVariable y = theory.createTermVariable("y", intSort);
	TermVariable z = theory.createTermVariable("z", intSort);
	
	Term num1 = theory.numeral("1");
	Term num2 = theory.numeral("2");
	FunctionSymbol plus = theory.getFunction("+", int2); 
	
	Term sublet = theory.let(x, num1, x);

	FormulaUnLet unletter = new FormulaUnLet();
	FormulaUnLet unletterLazy = new FormulaUnLet(UnletType.LAZY);
	FormulaUnLet unletterExpand = new FormulaUnLet(UnletType.EXPAND_DEFINITIONS);
	
	private final <E> E[] arr(E... vals) { return vals; }
	
	public void test() {
		Term letTerm = theory.let(arr(x, y), arr(num1, num2),
				theory.term(plus, x, y));
		assertEquals("(let ((x 1) (y 2)) (+ x y))", letTerm.toStringDirect());
		assertEquals("(+ 1 2)", unletter.unlet(letTerm).toStringDirect());
	}
	
	public void testScope() {
		Term letTerm = theory.let(x, num2, 
				theory.term(plus, theory.let(x, num1, x), x));
		assertEquals("(let ((x 2)) (+ (let ((x 1)) x) x))", letTerm.toStringDirect());
		assertEquals("(+ 1 2)", unletter.unlet(letTerm).toStringDirect());
		assertEquals("(+ 1 x)", unletter.unlet(((LetTerm) letTerm).getSubTerm()).toStringDirect());
		assertTrue(Arrays.equals(new TermVariable[] {x}, 
				unletter.unlet(((LetTerm) letTerm).getSubTerm()).getFreeVars()));
		
		letTerm = theory.let(arr(x, y), arr(y, x), theory.term(plus, x, y));
		assertEquals("(let ((x y) (y x)) (+ x y))", letTerm.toStringDirect());
		assertEquals("(+ y x)", unletter.unlet(letTerm).toStringDirect());

		letTerm = theory.let(x, y, theory.let(y, x, theory.term(plus, x, y)));
		assertEquals("(let ((x y)) (let ((y x)) (+ x y)))", letTerm.toStringDirect());
		assertEquals("(+ y y)", unletter.unlet(letTerm).toStringDirect());
		// This test is broken: the lazy semantics would require non-termination
		//assertEquals("(+ x y)", unletterLazy.unlet(letTerm).toStringDirect());
	}
	
	public void testLazy() {
		Term letTerm = theory.let(x, y, theory.let(y, num1, x));
		assertEquals("(let ((x y)) (let ((y 1)) x))", letTerm.toStringDirect());
		assertEquals("y", unletter.unlet(letTerm).toStringDirect());
		assertEquals("1", unletterLazy.unlet(letTerm).toStringDirect());
	}
	
	public void testQuant() {
		Term letTerm = theory.let(x, y, theory.exists(arr(x), theory.equals(x, y)));
		assertEquals("(let ((x y)) (exists ((x Int)) (= x y)))", 
				letTerm.toStringDirect());
		assertEquals("(exists ((x Int)) (= x y))", 
				unletter.unlet(letTerm).toStringDirect());

		letTerm = theory.let(arr(x,y), arr(y,z), 
				theory.exists(arr(x), theory.equals(x, y)));
		assertEquals("(let ((x y) (y z)) (exists ((x Int)) (= x y)))", 
				letTerm.toStringDirect());
		assertEquals("(exists ((x Int)) (= x z))", 
				unletter.unlet(letTerm).toStringDirect());
	
		letTerm = theory.let(y, x, theory.exists(arr(x), theory.equals(x, y)));
		assertEquals("(let ((y x)) (exists ((x Int)) (= x y)))", 
				letTerm.toStringDirect());
		assertEquals("(exists ((.unlet.0 Int)) (= .unlet.0 x))", 
				unletter.unlet(letTerm).toStringDirect());

		letTerm = theory.let(arr(x,y), arr(y,z), 
				theory.exists(arr(y), theory.equals(x, y)));
		assertEquals("(let ((x y) (y z)) (exists ((y Int)) (= x y)))", 
				letTerm.toStringDirect());
		Term unlet = unletter.unlet(letTerm);
		String varname = ((QuantifiedFormula) unlet).getVariables()[0].toStringDirect();
		assertEquals(".unlet.", varname.substring(0, 7));
		assertEquals("(exists (("+varname+" Int)) (= y "+varname+"))", 
				unlet.toStringDirect());
	}

	public void testAnnotation() {
		Term letTerm = theory.let(x, y, 
				theory.annotatedTerm(arr(new Annotation(":named", "foo")), x));
		assertEquals("(let ((x y)) (! x :named foo))", 
				letTerm.toStringDirect());
		assertEquals("(! y :named foo)", 
				unletter.unlet(letTerm).toStringDirect());
		
		letTerm = theory.let(x, z, 
				theory.exists(arr(y), 
					theory.annotatedTerm(arr(new Annotation(":pattern", theory.term(plus, x, y))), 
							theory.equals(theory.term(plus, x, y), num2))));
		assertEquals("(let ((x z)) (exists ((y Int)) (! (= (+ x y) 2) :pattern (+ x y))))", 
				letTerm.toStringDirect());
		assertEquals("(exists ((y Int)) (! (= (+ z y) 2) :pattern (+ z y)))", 
				unletter.unlet(letTerm).toStringDirect());

		letTerm = theory.let(x, z, 
				theory.exists(arr(y), 
					theory.annotatedTerm(arr(new Annotation(":pattern", 
							arr(theory.term(plus, x, y), theory.term(plus, y, x)))), 
							theory.equals(theory.term(plus, x, y), num2))));
		assertEquals("(let ((x z)) (exists ((y Int)) (! (= (+ x y) 2) :pattern ((+ x y) (+ y x)))))", 
				letTerm.toStringDirect());
		assertEquals("(exists ((y Int)) (! (= (+ z y) 2) :pattern ((+ z y) (+ y z))))", 
				unletter.unlet(letTerm).toStringDirect());
	}

	public void testCache() {
		Term[] deepTerm = new Term[100];
		deepTerm[0] = x;
		for (int i = 1; i < 100; i++)
			deepTerm[i] = theory.term(plus, deepTerm[i-1], deepTerm[i-1]);
		int depth = 0;
		Term unlet = unletter.unlet(theory.let(x, y, deepTerm[99]));
		// do not even think of calling toStringDirect here...
		while ((unlet instanceof ApplicationTerm)) {
			ApplicationTerm app = (ApplicationTerm) unlet; 
			assertEquals(plus, app.getFunction());
			assertEquals(app.getParameters()[0], app.getParameters()[1]);
			unlet = app.getParameters()[0];
			depth++;
		}
		assertEquals(y, unlet);
		assertEquals(99, depth);

		Term plusxy = theory.term(plus, x, y);
		
		Term letTerm = theory.let(x, z, theory.equals(plusxy, theory.let(x, y, plusxy)));
		assertEquals("(let ((x z)) (= (+ x y) (let ((x y)) (+ x y))))", 
				letTerm.toStringDirect());
		assertEquals("(= (+ z y) (+ y y))", 
				unletter.unlet(letTerm).toStringDirect());
		letTerm = theory.equals(theory.let(x, z, plusxy), theory.let(x, y, plusxy));
		assertEquals("(= (let ((x z)) (+ x y)) (let ((x y)) (+ x y)))", 
				letTerm.toStringDirect());
		assertEquals("(= (+ z y) (+ y y))", 
				unletter.unlet(letTerm).toStringDirect());
		letTerm = theory.equals(plusxy, theory.let(x, y, plusxy));
		assertEquals("(= (+ x y) (let ((x y)) (+ x y)))", 
				letTerm.toStringDirect());
		assertEquals("(= (+ x y) (+ y y))", 
				unletter.unlet(letTerm).toStringDirect());
	}
	
	public void testExpand() {
		Term def = theory.term(plus, x, y);
		FunctionSymbol plusdef = theory.defineFunction("plus", arr(x, y), def);
		Term defed = theory.term(plusdef, num1, num2);
		assertEquals("(plus 1 2)", defed.toStringDirect());
		assertEquals("(+ 1 2)", unletterExpand.unlet(defed).toStringDirect());
	}
}
