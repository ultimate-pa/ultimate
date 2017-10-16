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
package de.uni_freiburg.informatik.ultimate.smtinterpol.model;

import java.math.BigInteger;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 * Tests for the model production of SMTInterpol.
 * 
 * @author Juergen Christ
 */
@RunWith(JUnit4.class)
public class ModelTest {

	private final String[] mBooleanNames = { "P", "Q", "R", "S" };

	private final String[] mVarNames = { "u", "v", "w", "x", "y", "z" };

	private ConstantTerm getConstantTerm(final Model model, final Term term) {
		return (ConstantTerm) model.evaluate(term);
	}

	private Script setupScript(final Logics logic) {
		final Script res = new SMTInterpol(new DefaultLogger());
		res.setOption(":produce-models", true);
		res.setLogic(logic);
		return res;
	}

	@Test
	public void testBoolean() {
		final Script script = setupScript(Logics.QF_UF);
		final Term[] boolTerms = new Term[mBooleanNames.length];
		final Sort bool = script.sort("Bool");
		int p = -1;
		for (final String name : mBooleanNames) {
			script.declareFun(name, Script.EMPTY_SORT_ARRAY, bool);
			boolTerms[++p] = script.term(name);
		}
		script.declareFun("Pred", new Sort[] { bool }, bool);
		script.declareFun("Unused", new Sort[] { bool }, bool);
		// Test single Boolean terms
		boolean pos = true;
		// All even indices are of positive, all odd are of negative polarity.
		for (final Term bt : boolTerms) {
			script.assertTerm(pos ? bt : script.term("not", bt));
			pos ^= true;
		}
		final Term trueTerm = script.term("true");
		final Term falseTerm = script.term("false");
		script.assertTerm(script.term("Pred", trueTerm));
		script.assertTerm(script.term("not", script.term("Pred", falseTerm)));
		final LBool isSat = script.checkSat();
		Assert.assertEquals(LBool.SAT, isSat);
		final Model model = script.getModel();
		pos = true;
		for (final Term bt : boolTerms) {
			final Term val = model.evaluate(bt);
			Assert.assertEquals(pos ? trueTerm : falseTerm, val);
			pos ^= true;
		}
		// True test
		Assert.assertEquals(trueTerm, model.evaluate(trueTerm));
		// False test
		Assert.assertEquals(falseTerm, model.evaluate(falseTerm));
		// Simple not test
		Assert.assertEquals(falseTerm, model.evaluate(script.term("not", boolTerms[0])));
		Assert.assertEquals(trueTerm, model.evaluate(script.term("not", boolTerms[1])));
		// Simple implies tests
		// true implies false
		Assert.assertEquals(falseTerm, model.evaluate(script.term("=>", boolTerms[0], boolTerms[1])));
		// false implies true
		Assert.assertEquals(trueTerm, model.evaluate(script.term("=>", boolTerms[1], boolTerms[2])));
		// true implies true
		Assert.assertEquals(trueTerm, model.evaluate(script.term("=>", boolTerms[0], boolTerms[2])));
		// right associativity: (=> true false true false) == true
		// (=> true (=> false (=> true false)))
		Assert.assertEquals(trueTerm, model.evaluate(script.term("=>", boolTerms)));
		// right associativity: (=> true true true false) == false
		// (=> true (=> true (=> true false)))
		Assert.assertEquals(falseTerm, model.evaluate(
				script.term("=>", boolTerms[0], script.term("not", boolTerms[1]), boolTerms[2], boolTerms[3])));// NOCHECKSTYLE
		// Simple and tests
		Assert.assertEquals(trueTerm, model.evaluate(script.term("and", boolTerms[0], boolTerms[2])));
		Assert.assertEquals(falseTerm, model.evaluate(script.term("and", boolTerms[0], boolTerms[1])));
		Assert.assertEquals(falseTerm, model.evaluate(script.term("and", boolTerms[1], boolTerms[2])));
		Assert.assertEquals(falseTerm, model.evaluate(script.term("and", boolTerms[1], boolTerms[3])));// NOCHECKSTYLE
		// left associativity
		Assert.assertEquals(falseTerm, model.evaluate(script.term("and", boolTerms)));
		Assert.assertEquals(trueTerm, model.evaluate(script.term("and", boolTerms[0], boolTerms[2],
				script.term("not", boolTerms[1]), script.term("not", boolTerms[3]))));// NOCHECKSTYLE
		// Simple or tests
		Assert.assertEquals(trueTerm, model.evaluate(script.term("or", boolTerms[0], boolTerms[2])));
		Assert.assertEquals(trueTerm, model.evaluate(script.term("or", boolTerms[0], boolTerms[1])));
		Assert.assertEquals(trueTerm, model.evaluate(script.term("or", boolTerms[1], boolTerms[2])));
		Assert.assertEquals(falseTerm, model.evaluate(script.term("or", boolTerms[1], boolTerms[3])));// NOCHECKSTYLE
		// left associativity
		Assert.assertEquals(trueTerm, model.evaluate(script.term("or", boolTerms)));
		Assert.assertEquals(falseTerm, model.evaluate(script.term("and", boolTerms[1], boolTerms[3], // NOCHECKSTYLE
				script.term("not", boolTerms[0]), script.term("not", boolTerms[2]))));
		// simple xor tests
		Assert.assertEquals(trueTerm, model.evaluate(script.term("xor", boolTerms[0], boolTerms[1])));
		Assert.assertEquals(falseTerm, model.evaluate(script.term("xor", boolTerms[0], boolTerms[2])));
		// left associativity: (xor true false true false) == false
		Assert.assertEquals(falseTerm, model.evaluate(script.term("xor", boolTerms)));
		// left associativity: (xor true false false) == true
		Assert.assertEquals(trueTerm, model.evaluate(script.term("xor", boolTerms[0], boolTerms[1], boolTerms[3])));// NOCHECKSTYLE
		// simple = tests
		Assert.assertEquals(trueTerm, model.evaluate(script.term("=", boolTerms[0], boolTerms[2])));
		Assert.assertEquals(falseTerm, model.evaluate(script.term("=", boolTerms[0], boolTerms[1])));
		// chainable
		Assert.assertEquals(falseTerm, model.evaluate(script.term("=", boolTerms)));
		Assert.assertEquals(trueTerm,
				model.evaluate(script.term("=", boolTerms[0], boolTerms[2], script.term("not", boolTerms[1]))));
		// simple distinct tests
		Assert.assertEquals(trueTerm, model.evaluate(script.term("distinct", boolTerms[0], boolTerms[1])));
		Assert.assertEquals(falseTerm, model.evaluate(script.term("distinct", boolTerms[0], boolTerms[2])));
		// pairwise does not make sense for Booleans!!!
		// simple ite tests
		Assert.assertEquals(trueTerm, model.evaluate(script.term("ite", boolTerms[0], boolTerms[2], boolTerms[1])));
		Assert.assertEquals(falseTerm, model.evaluate(script.term("ite", boolTerms[0], boolTerms[1], boolTerms[2])));
		Assert.assertEquals(trueTerm, model.evaluate(script.term("ite", boolTerms[1], boolTerms[3], boolTerms[0])));// NOCHECKSTYLE
		Assert.assertEquals(falseTerm, model.evaluate(script.term("ite", boolTerms[1], boolTerms[0], boolTerms[3])));// NOCHECKSTYLE
		Assert.assertEquals(trueTerm, model.evaluate(script.term("Pred", trueTerm)));
		Assert.assertEquals(falseTerm, model.evaluate(script.term("Pred", falseTerm)));
		// Unconstrained Booleans should be mapped to false
		Assert.assertEquals(falseTerm, model.evaluate(script.term("Unused", trueTerm)));
		Assert.assertEquals(falseTerm, model.evaluate(script.term("Unused", falseTerm)));
	}

	@Test
	public void testLIA() {
		final Script script = setupScript(Logics.QF_LIA);
		final Term[] intTerms = new Term[mVarNames.length];
		final Sort intSort = script.sort("Int");
		int p = -1;
		for (final String name : mVarNames) {
			script.declareFun(name, Script.EMPTY_SORT_ARRAY, intSort);
			intTerms[++p] = script.term(name);
		}
		script.assertTerm(script.term("<", intTerms));
		LBool isSat = script.checkSat();
		Assert.assertEquals(LBool.SAT, isSat);
		final Term trueTerm = script.term("true");
		final Term falseTerm = script.term("false");
		Model model = script.getModel();
		Assert.assertEquals(Rational.ONE, getConstantTerm(model, script.numeral(BigInteger.ONE)).getValue());
		final ConstantTerm uval = getConstantTerm(model, intTerms[0]);
		final ConstantTerm vval = getConstantTerm(model, intTerms[1]);
		final Rational diff = ((Rational) uval.getValue()).sub((Rational) vval.getValue());
		// We have u < v ==> u - v < 0
		Assert.assertTrue(diff.compareTo(Rational.ZERO) < 0);
		// u < v ?
		Assert.assertEquals(trueTerm, model.evaluate(script.term("<", intTerms[0], intTerms[1])));
		// u > v ?
		Assert.assertEquals(falseTerm, model.evaluate(script.term(">", intTerms[0], intTerms[1])));
		// u <= v ?
		Assert.assertEquals(trueTerm, model.evaluate(script.term("<=", intTerms[0], intTerms[1])));
		// u >= v ?
		Assert.assertEquals(falseTerm, model.evaluate(script.term(">=", intTerms[0], intTerms[1])));
		// u = v ?
		Assert.assertEquals(falseTerm, model.evaluate(script.term("=", intTerms[0], intTerms[1])));
		// u != v ?
		Assert.assertEquals(trueTerm, model.evaluate(script.term("distinct", intTerms[0], intTerms[1])));
		// associativity: v < w < u ?
		Assert.assertEquals(falseTerm, model.evaluate(script.term("<", intTerms[1], intTerms[2], intTerms[0])));
		// associativity: u < v < w
		Assert.assertEquals(trueTerm, model.evaluate(script.term("<", intTerms[0], intTerms[1], intTerms[2])));
		// associativity: v > w > u ?
		Assert.assertEquals(falseTerm, model.evaluate(script.term(">", intTerms[1], intTerms[2], intTerms[0])));
		// associativity: w > v > u
		Assert.assertEquals(trueTerm, model.evaluate(script.term(">", intTerms[2], intTerms[1], intTerms[0])));
		// associativity: v <= w <= u ?
		Assert.assertEquals(falseTerm, model.evaluate(script.term("<=", intTerms[1], intTerms[2], intTerms[0])));
		// associativity: u <= v <= w
		Assert.assertEquals(trueTerm, model.evaluate(script.term("<=", intTerms[0], intTerms[1], intTerms[2])));
		// associativity: v >= w >= u ?
		Assert.assertEquals(falseTerm, model.evaluate(script.term(">=", intTerms[1], intTerms[2], intTerms[0])));
		// associativity: w >= v >= u
		Assert.assertEquals(trueTerm, model.evaluate(script.term(">=", intTerms[2], intTerms[1], intTerms[0])));
		final ConstantTerm wwal = getConstantTerm(model, intTerms[2]);
		// Test for math operations
		// + (simple)
		Rational expected =
				((Rational) uval.getValue()).add((Rational) vval.getValue()).add((Rational) wwal.getValue());
		ConstantTerm got = getConstantTerm(model, script.term("+", intTerms[0], intTerms[1], intTerms[2]));
		Assert.assertEquals(expected, got.getValue());
		// - (simple)
		expected = ((Rational) uval.getValue()).sub((Rational) vval.getValue()).sub((Rational) wwal.getValue());
		got = getConstantTerm(model, script.term("-", intTerms[0], intTerms[1], intTerms[2]));
		Assert.assertEquals(expected, got.getValue());
		// * (simple)
		expected = ((Rational) uval.getValue()).mul(BigInteger.TEN);
		got = getConstantTerm(model, script.term("*", script.numeral(BigInteger.TEN), intTerms[0]));
		Assert.assertEquals(expected, got.getValue());
		// * (non-linear)
		expected = ((Rational) uval.getValue()).mul((Rational) vval.getValue());
		got = getConstantTerm(model, script.term("*", intTerms[0], intTerms[1]));
		Assert.assertEquals(expected, got.getValue());
		// Now, I fix the value of a variable to compute the values of div, mod,
		// (_ divisible n), abs
		final Term xvar = intTerms[4];// NOCHECKSTYLE
		final Term tten = script.numeral(BigInteger.TEN);
		final Term tnine = script.numeral(BigInteger.valueOf(9));// NOCHECKSTYLE
		final Term tmnine = script.numeral(BigInteger.valueOf(-9));// NOCHECKSTYLE
		script.assertTerm(script.term("=", xvar, tten));
		isSat = script.checkSat();
		Assert.assertEquals(LBool.SAT, isSat);
		model = script.getModel();
		final Rational ten = Rational.valueOf(10, 1);// NOCHECKSTYLE
		Assert.assertEquals(ten, getConstantTerm(model, xvar).getValue());
		// div
		Assert.assertEquals(Rational.ONE, getConstantTerm(model, script.term("div", xvar, tten)).getValue());
		// Test rounding according to standard
		Assert.assertEquals(Rational.ONE, getConstantTerm(model, script.term("div", xvar, tnine)).getValue());
		Assert.assertEquals(Rational.MONE, getConstantTerm(model, script.term("div", xvar, tmnine)).getValue());
		// mod
		Assert.assertEquals(Rational.ZERO, getConstantTerm(model, script.term("mod", xvar, tten)).getValue());
		// Test rounding according to standard
		Assert.assertEquals(Rational.ONE, getConstantTerm(model, script.term("mod", xvar, tnine)).getValue());
		Assert.assertEquals(Rational.ONE, getConstantTerm(model, script.term("mod", xvar, tmnine)).getValue());
		// divisible
		Assert.assertEquals(trueTerm,
				model.evaluate(script.term("divisible", new BigInteger[] { BigInteger.TEN }, null, xvar)));
		Assert.assertEquals(falseTerm,
				model.evaluate(script.term("divisible", new BigInteger[] { BigInteger.valueOf(9) }, null, xvar)));// NOCHECKSTYLE
		// abs
		Assert.assertEquals(model.evaluate(xvar), model.evaluate(script.term("abs", script.term("-", xvar))));
	}

	@Test
	public void testLIRA() {
		final Script script = setupScript(Logics.QF_UFLIRA);
		final LBool isSat = script.checkSat();
		Assert.assertEquals(LBool.SAT, isSat);
		final Model model = script.getModel();
		// Test to_int floor
		Assert.assertEquals(Rational.ZERO,
				getConstantTerm(model,
						script.term("to_int", script.term("/", script.decimal("1.0"), script.decimal("2.0"))))
								.getValue());
		// Test to_real noop
		Assert.assertEquals(Rational.ZERO,
				getConstantTerm(model, script.term("to_real", script.numeral("0"))).getValue());
		// Test is_int
		Assert.assertEquals(script.term("true"), model.evaluate(script.term("is_int", script.decimal("1"))));
		Assert.assertEquals(script.term("false"), model.evaluate(script.term("is_int", script.decimal("1.1"))));
	}

	@Test
	public void testLRA() {
		// since we have testLIA and the internals of the model tester do not
		// care about the types, we don't have to repeat the simple tests here
		// New tests needed for /, infinitesimal elements, and tableau
		// simplification
		final Script script = setupScript(Logics.QF_LRA);
		final Term[] realTerms = new Term[mVarNames.length];
		final Sort realSort = script.sort("Real");
		int p = -1;
		for (final String name : mVarNames) {
			script.declareFun(name, Script.EMPTY_SORT_ARRAY, realSort);
			realTerms[++p] = script.term(name);
		}
		// Keep realTerms[1] unconstrained => simplifier test
		script.assertTerm(script.term("=", realTerms[0], realTerms[1]));
		script.assertTerm(script.term("=", realTerms[0], script.term("*", script.numeral("2"), realTerms[2])));
		script.assertTerm(script.term("=", realTerms[0], script.numeral(BigInteger.TEN)));
		// w < x
		script.assertTerm(script.term("<", realTerms[3], realTerms[4]));// NOCHECKSTYLE
		// Make either w or x non-integer
		script.assertTerm(script.term("<", realTerms[4], // NOCHECKSTYLE
				script.term("+", realTerms[3], // NOCHECKSTYLE
						script.numeral(BigInteger.ONE))));
		final LBool isSat = script.checkSat();
		Assert.assertEquals(LBool.SAT, isSat);
		final Model model = script.getModel();
		final Rational ten = Rational.valueOf(10, 1);// NOCHECKSTYLE
		final Rational five = Rational.valueOf(5, 1);// NOCHECKSTYLE
		Assert.assertEquals(ten, getConstantTerm(model, realTerms[0]).getValue());
		Assert.assertEquals(ten, getConstantTerm(model, realTerms[1]).getValue());
		Assert.assertEquals(five, getConstantTerm(model, realTerms[2]).getValue());
		// Tests for /
		Assert.assertEquals(Rational.ONE,
				getConstantTerm(model, script.term("/", realTerms[0], realTerms[1])).getValue());
		Assert.assertEquals(Rational.ONE,
				getConstantTerm(model, script.term("/", realTerms[0], realTerms[1])).getValue());
		Assert.assertEquals(Rational.TWO,
				getConstantTerm(model, script.term("/", realTerms[0], realTerms[2])).getValue());
		// Infinitesimal test
		final Rational wval = (Rational) getConstantTerm(model, realTerms[3]).getValue();// NOCHECKSTYLE
		final Rational xval = (Rational) getConstantTerm(model, realTerms[4]).getValue();// NOCHECKSTYLE
		Assert.assertTrue(wval.compareTo(xval) < 0);
		Assert.assertTrue(!wval.isIntegral() || !xval.isIntegral());
		// Unused rational variable test
		final Rational unusedVal = (Rational) getConstantTerm(model, script.term("@0", null, realSort)).getValue();
		Assert.assertEquals(unusedVal, getConstantTerm(model, realTerms[5]).getValue());// NOCHECKSTYLE
	}

	@Test
	public void testShared() {
		final Script script = setupScript(Logics.QF_UFLIA);
		final Sort intSort = script.sort("Int");
		script.declareFun("f", new Sort[] { intSort }, intSort);
		script.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		final Term x = script.term("x");
		final Term y = script.term("y");
		final Term fx5 = script.term("f", script.term("+", x, script.numeral("5")));
		final Rational five = Rational.valueOf(5, 1);// NOCHECKSTYLE
		script.assertTerm(script.term("=", fx5, x));
		script.assertTerm(script.term("=", x, script.numeral("5")));
		script.assertTerm(script.term(">", y, script.numeral(BigInteger.ZERO)));
		final LBool isSat = script.checkSat();
		Assert.assertEquals(LBool.SAT, isSat);
		final Model model = script.getModel();
		Assert.assertEquals(five, getConstantTerm(model, x).getValue());
		Assert.assertEquals(five, getConstantTerm(model, fx5).getValue());
		final Rational yval = (Rational) getConstantTerm(model, y).getValue();
		// Evaluate f at position x - y + (y+5)
		final Rational yvalminus5 = yval.add(five);
		Assert.assertEquals(five,
				getConstantTerm(model,
						script.term("f", script.term("+", x, script.term("-", y), yvalminus5.toTerm(intSort))))
								.getValue());
		Assert.assertEquals(five, getConstantTerm(model, script.term("f", script.numeral(BigInteger.TEN))).getValue());
		final TermVariable[] args = new TermVariable[] { script.variable("@x", intSort) };
		Assert.assertEquals("(ite (= @x 10) 5 0)", model.getFunctionDefinition("f", args).toString());
	}

	@Test
	public void testTermITE() {
		final Script script = setupScript(Logics.QF_UF);
		final Term[] boolTerms = new Term[mBooleanNames.length];
		final Sort bool = script.sort("Bool");
		int p = -1;
		for (final String name : mBooleanNames) {
			script.declareFun(name, Script.EMPTY_SORT_ARRAY, bool);
			boolTerms[++p] = script.term(name);
		}
		boolean pos = true;
		// All even indices are of positive, all odd are of negative polarity.
		for (final Term bt : boolTerms) {
			script.assertTerm(pos ? bt : script.term("not", bt));
			pos ^= true;
		}
		final Term ite1 = script.term("ite", boolTerms[0], boolTerms[1], boolTerms[2]);
		final Term ite2 = script.term("ite", boolTerms[3], boolTerms[2], boolTerms[1]);// NOCHECKSTYLE
		script.assertTerm(script.term("=", ite1, ite2));
		final LBool isSat = script.checkSat();
		Assert.assertEquals(LBool.SAT, isSat);
		final Term trueTerm = script.term("true");
		final Term falseTerm = script.term("false");
		final Model model = script.getModel();
		pos = true;
		for (final Term bt : boolTerms) {
			final Term val = model.evaluate(bt);
			Assert.assertEquals(pos ? trueTerm : falseTerm, val);
			pos ^= true;
		}
		Assert.assertEquals(falseTerm, model.evaluate(ite1));
		Assert.assertEquals(falseTerm, model.evaluate(ite2));
	}

	@Test
	public void testUF() {
		final Script script = setupScript(Logics.QF_UF);
		script.declareSort("U", 0);
		final Sort u = script.sort("U");
		script.declareSort("V", 0);
		final Sort v = script.sort("V");
		script.declareFun("f", new Sort[] { u }, u);
		script.declareFun("g", new Sort[] { u }, u);
		script.declareFun("x", Script.EMPTY_SORT_ARRAY, u);
		script.declareFun("y", Script.EMPTY_SORT_ARRAY, u);
		script.declareFun("z1", Script.EMPTY_SORT_ARRAY, v);
		script.declareFun("z2", Script.EMPTY_SORT_ARRAY, v);
		final Term x = script.term("x");
		final Term fx = script.term("f", x);
		script.assertTerm(script.term("=", x, fx));
		final LBool isSat = script.checkSat();
		Assert.assertEquals(LBool.SAT, isSat);
		final Model model = script.getModel();
		Term val = model.evaluate(x);
		Assert.assertEquals(val, model.evaluate(fx));
		Assert.assertEquals(val, model.evaluate(script.term("f", fx)));
		// Test for stack overflows in the evaluation
		Term testTerm = fx;
		for (int i = 0; i < 1000000; ++i) {
			testTerm = script.term("f", testTerm);
		}
		Assert.assertEquals(val, model.evaluate(testTerm));
		// Dynamic completion check
		// 1. U already has an element in the domain (val)
		// => all unconstrained elements are mapped to val
		Assert.assertEquals(val, model.evaluate(script.term("y")));
		Assert.assertEquals(val, model.evaluate(script.term("f", script.term("y"))));
		// 2. V does not have any constrained elements
		// => all unconstrained elements will map to default (as @0 V)
		val = script.term("@0", null, v);
		final Term z1 = script.term("z1");
		Assert.assertEquals(val, model.evaluate(z1));
		final Term z2 = script.term("z2");
		Assert.assertEquals(val, model.evaluate(z2));
		final TermVariable[] args = new TermVariable[] { script.variable("@x", u) };
		final Set<FunctionSymbol> funcs = new HashSet<>();
		funcs.add(((ApplicationTerm) fx).getFunction());
		funcs.add(((ApplicationTerm) script.term("g", x)).getFunction());
		funcs.add(((ApplicationTerm) x).getFunction());
		funcs.add(((ApplicationTerm) script.term("y")).getFunction());
		funcs.add(((ApplicationTerm) z1).getFunction());
		funcs.add(((ApplicationTerm) z2).getFunction());
		Assert.assertEquals(funcs, model.getDefinedFunctions());
		Assert.assertEquals("(as @0 U)", model.getFunctionDefinition("x", new TermVariable[0]).toString());
		Assert.assertEquals("(as @0 U)", model.getFunctionDefinition("f", args).toString());
		Assert.assertEquals("(as @0 U)", model.getFunctionDefinition("g", args).toString());
	}

	@Test
	public void testValuation() {
		final Script script = setupScript(Logics.QF_LIA);
		final Term[] intTerms = new Term[mVarNames.length];
		final Sort intSort = script.sort("Int");
		int p = -1;
		for (final String name : mVarNames) {
			script.declareFun(name, Script.EMPTY_SORT_ARRAY, intSort);
			intTerms[++p] = script.term(name);
		}
		for (int i = 0; i < intTerms.length; ++i) {
			script.assertTerm(script.term("=", intTerms[i], script.numeral(BigInteger.valueOf(i))));
		}
		final LBool isSat = script.checkSat();
		Assert.assertEquals(LBool.SAT, isSat);
		final Model model = script.getModel();
		final Map<Term, Term> valuation = script.getValue(intTerms);
		final Map<Term, Term> modeleval = model.evaluate(intTerms);
		for (int i = 0; i < intTerms.length; ++i) {
			final Rational val = Rational.valueOf(i, 1);
			final Term expected = val.toTerm(intSort);
			Assert.assertEquals(expected, valuation.get(intTerms[i]));
			Assert.assertEquals(expected, modeleval.get(intTerms[i]));
			Assert.assertEquals(expected, model.evaluate(intTerms[i]));
		}
	}

}
