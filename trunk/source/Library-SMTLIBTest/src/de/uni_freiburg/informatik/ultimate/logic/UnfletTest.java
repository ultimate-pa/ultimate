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

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet.UnletType;

@RunWith(JUnit4.class)
public class UnfletTest {

	Theory mTheory = new Theory(Logics.AUFLIRA);

	Sort mIntSort = mTheory.getSort("Int");
	Sort[] mInt2 = arr(mIntSort, mIntSort);
	TermVariable mX = mTheory.createTermVariable("x", mIntSort);
	TermVariable mY = mTheory.createTermVariable("y", mIntSort);
	TermVariable mZ = mTheory.createTermVariable("z", mIntSort);

	Term mNum1 = mTheory.numeral("1");
	Term mNum2 = mTheory.numeral("2");
	FunctionSymbol mPlus = mTheory.getFunction("+", mInt2);

	Term mSublet = mTheory.let(mX, mNum1, mX);

	FormulaUnLet mUnletter = new FormulaUnLet();
	FormulaUnLet mUnletterLazy = new FormulaUnLet(UnletType.LAZY);
	FormulaUnLet mUnletterExpand = new FormulaUnLet(UnletType.EXPAND_DEFINITIONS);

	@SafeVarargs
	private final <E> E[] arr(final E... vals) {
		return vals;
	} // NOCHECKSTYLE

	@Test
	public void test() {
		final Term letTerm = mTheory.let(arr(mX, mY), arr(mNum1, mNum2), mTheory.term(mPlus, mX, mY));
		Assert.assertEquals("(let ((x 1) (y 2)) (+ x y))", letTerm.toStringDirect());
		Assert.assertEquals("(+ 1 2)", mUnletter.unlet(letTerm).toStringDirect());
	}

	@Test
	public void testScope() {
		Term letTerm = mTheory.let(mX, mNum2, mTheory.term(mPlus, mTheory.let(mX, mNum1, mX), mX));
		Assert.assertEquals("(let ((x 2)) (+ (let ((x 1)) x) x))", letTerm.toStringDirect());
		Assert.assertEquals("(+ 1 2)", mUnletter.unlet(letTerm).toStringDirect());
		Assert.assertEquals("(+ 1 x)", mUnletter.unlet(((LetTerm) letTerm).getSubTerm()).toStringDirect());
		Assert.assertTrue(Arrays.equals(new TermVariable[] { mX },
				mUnletter.unlet(((LetTerm) letTerm).getSubTerm()).getFreeVars()));

		letTerm = mTheory.let(arr(mX, mY), arr(mY, mX), mTheory.term(mPlus, mX, mY));
		Assert.assertEquals("(let ((x y) (y x)) (+ x y))", letTerm.toStringDirect());
		Assert.assertEquals("(+ y x)", mUnletter.unlet(letTerm).toStringDirect());

		letTerm = mTheory.let(mX, mY, mTheory.let(mY, mX, mTheory.term(mPlus, mX, mY)));
		Assert.assertEquals("(let ((x y)) (let ((y x)) (+ x y)))", letTerm.toStringDirect());
		Assert.assertEquals("(+ y y)", mUnletter.unlet(letTerm).toStringDirect());
		// This test is broken: the lazy semantics would require non-termination
		// Assert.assertEquals("(+ x y)", unletterLazy.unlet(letTerm).toStringDirect());
	}

	@Test
	public void testLazy() {
		final Term letTerm = mTheory.let(mX, mY, mTheory.let(mY, mNum1, mX));
		Assert.assertEquals("(let ((x y)) (let ((y 1)) x))", letTerm.toStringDirect());
		Assert.assertEquals("y", mUnletter.unlet(letTerm).toStringDirect());
		Assert.assertEquals("1", mUnletterLazy.unlet(letTerm).toStringDirect());
	}

	@Test
	public void testQuant() {
		Term letTerm = mTheory.let(mX, mY, mTheory.exists(arr(mX), mTheory.equals(mX, mY)));
		Assert.assertEquals("(let ((x y)) (exists ((x Int)) (= x y)))", letTerm.toStringDirect());
		Assert.assertEquals("(exists ((x Int)) (= x y))", mUnletter.unlet(letTerm).toStringDirect());

		letTerm = mTheory.let(arr(mX, mY), arr(mY, mZ), mTheory.exists(arr(mX), mTheory.equals(mX, mY)));
		Assert.assertEquals("(let ((x y) (y z)) (exists ((x Int)) (= x y)))", letTerm.toStringDirect());
		Assert.assertEquals("(exists ((x Int)) (= x z))", mUnletter.unlet(letTerm).toStringDirect());

		letTerm = mTheory.let(mY, mX, mTheory.exists(arr(mX), mTheory.equals(mX, mY)));
		Assert.assertEquals("(let ((y x)) (exists ((x Int)) (= x y)))", letTerm.toStringDirect());
		Assert.assertEquals("(exists ((.unlet.0 Int)) (= .unlet.0 x))", mUnletter.unlet(letTerm).toStringDirect());

		letTerm = mTheory.let(arr(mX, mY), arr(mY, mZ), mTheory.exists(arr(mY), mTheory.equals(mX, mY)));
		Assert.assertEquals("(let ((x y) (y z)) (exists ((y Int)) (= x y)))", letTerm.toStringDirect());
		final Term unlet = mUnletter.unlet(letTerm);
		final String varname = ((QuantifiedFormula) unlet).getVariables()[0].toStringDirect();
		Assert.assertEquals(".unlet.", varname.substring(0, 7));// NOCHECKSTYLE
		Assert.assertEquals("(exists ((" + varname + " Int)) (= y " + varname + "))", unlet.toStringDirect());
	}

	@Test
	public void testAnnotation() {
		Term letTerm = mTheory.let(mX, mY, mTheory.annotatedTerm(arr(new Annotation(":named", "foo")), mX));
		Assert.assertEquals("(let ((x y)) (! x :named foo))", letTerm.toStringDirect());
		Assert.assertEquals("(! y :named foo)", mUnletter.unlet(letTerm).toStringDirect());

		letTerm = mTheory.let(mX, mZ,
				mTheory.exists(arr(mY),
						mTheory.annotatedTerm(arr(new Annotation(":pattern", mTheory.term(mPlus, mX, mY))),
								mTheory.equals(mTheory.term(mPlus, mX, mY), mNum2))));
		Assert.assertEquals("(let ((x z)) (exists ((y Int)) (! (= (+ x y) 2) :pattern (+ x y))))", // NOCHECKSTYLE
				letTerm.toStringDirect());
		Assert.assertEquals("(exists ((y Int)) (! (= (+ z y) 2) :pattern (+ z y)))",
				mUnletter.unlet(letTerm).toStringDirect());

		letTerm = mTheory.let(mX, mZ,
				mTheory.exists(arr(mY), mTheory.annotatedTerm(
						arr(new Annotation(":pattern", arr(mTheory.term(mPlus, mX, mY), mTheory.term(mPlus, mY, mX)))),
						mTheory.equals(mTheory.term(mPlus, mX, mY), mNum2))));
		Assert.assertEquals("(let ((x z)) (exists ((y Int)) (! (= (+ x y) 2) :pattern ((+ x y) (+ y x)))))", // NOCHECKSTYLE
				letTerm.toStringDirect());
		Assert.assertEquals("(exists ((y Int)) (! (= (+ z y) 2) :pattern ((+ z y) (+ y z))))", // NOCHECKSTYLE
				mUnletter.unlet(letTerm).toStringDirect());
	}

	@Test
	public void testCache() {
		final Term[] deepTerm = new Term[100];// NOCHECKSTYLE
		deepTerm[0] = mX;
		for (int i = 1; i < 100; i++) {
			deepTerm[i] = mTheory.term(mPlus, deepTerm[i - 1], deepTerm[i - 1]);
		}
		int depth = 0;
		Term unlet = mUnletter.unlet(mTheory.let(mX, mY, deepTerm[99]));// NOCHECKSTYLE
		// do not even think of calling toStringDirect here...
		while ((unlet instanceof ApplicationTerm)) {
			final ApplicationTerm app = (ApplicationTerm) unlet;
			Assert.assertEquals(mPlus, app.getFunction());
			Assert.assertEquals(app.getParameters()[0], app.getParameters()[1]);
			unlet = app.getParameters()[0];
			depth++;
		}
		Assert.assertEquals(mY, unlet);
		Assert.assertEquals(99, depth);// NOCHECKSTYLE

		final Term plusxy = mTheory.term(mPlus, mX, mY);

		Term letTerm = mTheory.let(mX, mZ, mTheory.equals(plusxy, mTheory.let(mX, mY, plusxy)));
		Assert.assertEquals("(let ((x z)) (= (+ x y) (let ((x y)) (+ x y))))", letTerm.toStringDirect());
		Assert.assertEquals("(= (+ z y) (+ y y))", mUnletter.unlet(letTerm).toStringDirect());
		letTerm = mTheory.equals(mTheory.let(mX, mZ, plusxy), mTheory.let(mX, mY, plusxy));
		Assert.assertEquals("(= (let ((x z)) (+ x y)) (let ((x y)) (+ x y)))", letTerm.toStringDirect());
		Assert.assertEquals("(= (+ z y) (+ y y))", mUnletter.unlet(letTerm).toStringDirect());
		letTerm = mTheory.equals(plusxy, mTheory.let(mX, mY, plusxy));
		Assert.assertEquals("(= (+ x y) (let ((x y)) (+ x y)))", letTerm.toStringDirect());
		Assert.assertEquals("(= (+ x y) (+ y y))", mUnletter.unlet(letTerm).toStringDirect());
	}

	@Test
	public void testExpand() {
		final Term def = mTheory.term(mPlus, mX, mY);
		final FunctionSymbol plusdef = mTheory.defineFunction("plus", arr(mX, mY), def);
		final Term defed = mTheory.term(plusdef, mNum1, mNum2);
		Assert.assertEquals("(plus 1 2)", defed.toStringDirect());
		Assert.assertEquals("(+ 1 2)", mUnletterExpand.unlet(defed).toStringDirect());
	}
}
