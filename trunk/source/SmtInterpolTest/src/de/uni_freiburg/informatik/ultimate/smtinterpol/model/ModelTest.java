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
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.TestCaseWithLogger;

/**
 * Tests for the model production of SMTInterpol.
 * @author Juergen Christ
 */
public class ModelTest extends TestCaseWithLogger {
	
	private String[] m_BooleanNames = {
			"P", "Q", "R", "S"
	};
	
	private String[] m_VarNames = {
			"u", "v", "w", "x", "y", "z"
	};
	
	private static final Sort[] EMPTY_SORT_ARRAY = new Sort[0];
	
	private Script setupScript(Logics logic) {
		Script res = new SMTInterpol(Logger.getRootLogger(), false);
		res.setOption(":produce-models", true);
		res.setLogic(logic);
		return res;
	}
	
	private ConstantTerm getConstantTerm(Model model, Term term) {
		return (ConstantTerm) model.evaluate(term);
	}
	
	public void testBoolean() {
		Script script = setupScript(Logics.QF_UF);
		Term[] boolTerms = new Term[m_BooleanNames.length];
		Sort bool = script.sort("Bool");
		int p = -1;
		for (String name : m_BooleanNames) {
			script.declareFun(name, EMPTY_SORT_ARRAY, bool);
			boolTerms[++p] = script.term(name);
		}
		script.declareFun("Pred", new Sort[] {bool}, bool);
		script.declareFun("Unused", new Sort[] {bool}, bool);
		// Test single Boolean terms
		boolean pos = true;
		// All even indices are of positive, all odd are of negative polarity.
		for (Term bt : boolTerms) {
			script.assertTerm(pos ? bt : script.term("not", bt));
			pos = !pos;
		}
		Term trueTerm = script.term("true");
		Term falseTerm = script.term("false");
		script.assertTerm(script.term("Pred", trueTerm));
		script.assertTerm(script.term("not", script.term("Pred", falseTerm)));
		LBool isSat = script.checkSat();
		assertEquals(LBool.SAT, isSat);
		Model model = script.getModel();
		pos = true;
		for (Term bt : boolTerms) {
			Term val = model.evaluate(bt);
			assertEquals(pos ? trueTerm : falseTerm, val);
			pos = !pos;
		}
		// True test
		assertEquals(trueTerm, model.evaluate(trueTerm));
		// False test
		assertEquals(falseTerm, model.evaluate(falseTerm));
		// Simple not test
		assertEquals(falseTerm, model.evaluate(
				script.term("not", boolTerms[0])));
		assertEquals(trueTerm, model.evaluate(
				script.term("not", boolTerms[1])));
		// Simple implies tests
		// true implies false
		assertEquals(falseTerm, model.evaluate(
				script.term("=>", boolTerms[0], boolTerms[1])));
		// false implies true
		assertEquals(trueTerm, model.evaluate(
				script.term("=>", boolTerms[1], boolTerms[2])));
		// true implies true
		assertEquals(trueTerm, model.evaluate(
				script.term("=>", boolTerms[0], boolTerms[2])));
		// left associativity: (=> true false true false) == false
		assertEquals(falseTerm, model.evaluate(script.term("=>", boolTerms)));
		// left associativity: (=> true false true true) == true
		assertEquals(trueTerm, model.evaluate(
				script.term("=>", boolTerms[0], boolTerms[1], boolTerms[2],
						script.term("not", boolTerms[3]))));
		// Simple and tests
		assertEquals(trueTerm, model.evaluate(
				script.term("and", boolTerms[0], boolTerms[2])));
		assertEquals(falseTerm, model.evaluate(
				script.term("and", boolTerms[0], boolTerms[1])));
		assertEquals(falseTerm, model.evaluate(
				script.term("and", boolTerms[1], boolTerms[2])));
		assertEquals(falseTerm, model.evaluate(
				script.term("and", boolTerms[1], boolTerms[3])));
		// left associativity
		assertEquals(falseTerm, model.evaluate(script.term("and", boolTerms)));
		assertEquals(trueTerm, model.evaluate(
				script.term("and", boolTerms[0], boolTerms[2], 
						script.term("not", boolTerms[1]),
						script.term("not", boolTerms[3]))));
		// Simple or tests
		assertEquals(trueTerm, model.evaluate(
				script.term("or", boolTerms[0], boolTerms[2])));
		assertEquals(trueTerm, model.evaluate(
				script.term("or", boolTerms[0], boolTerms[1])));
		assertEquals(trueTerm, model.evaluate(
				script.term("or", boolTerms[1], boolTerms[2])));
		assertEquals(falseTerm, model.evaluate(
				script.term("or", boolTerms[1], boolTerms[3])));
		// left associativity
		assertEquals(trueTerm, model.evaluate(script.term("or", boolTerms)));
		assertEquals(falseTerm, model.evaluate(
				script.term("and", boolTerms[1], boolTerms[3], 
						script.term("not", boolTerms[0]),
						script.term("not", boolTerms[2]))));
		// simple xor tests
		assertEquals(trueTerm, model.evaluate(
				script.term("xor", boolTerms[0], boolTerms[1])));
		assertEquals(falseTerm, model.evaluate(
				script.term("xor", boolTerms[0], boolTerms[2])));
		// left associativity: (xor true false true false) == false
		assertEquals(falseTerm, model.evaluate(script.term("xor", boolTerms)));
		// left associativity: (xor true false false) == true
		assertEquals(trueTerm, model.evaluate(
				script.term("xor", boolTerms[0], boolTerms[1], boolTerms[3])));
		// simple = tests
		assertEquals(trueTerm, model.evaluate(script.term("=",
				boolTerms[0], boolTerms[2])));
		assertEquals(falseTerm, model.evaluate(script.term("=",
				boolTerms[0], boolTerms[1])));
		// chainable
		assertEquals(falseTerm, model.evaluate(script.term("=", boolTerms)));
		assertEquals(trueTerm, model.evaluate(script.term("=",
				boolTerms[0], boolTerms[2], script.term("not", boolTerms[1]))));
		// simple distinct tests
		assertEquals(trueTerm, model.evaluate(
				script.term("distinct", boolTerms[0], boolTerms[1])));
		assertEquals(falseTerm, model.evaluate(
				script.term("distinct", boolTerms[0], boolTerms[2])));
		// pairwise does not make sense for Booleans!!!
		// simple ite tests
		assertEquals(trueTerm, model.evaluate(
				script.term("ite", boolTerms[0], boolTerms[2], boolTerms[1])));
		assertEquals(falseTerm, model.evaluate(
				script.term("ite", boolTerms[0], boolTerms[1], boolTerms[2])));
		assertEquals(trueTerm, model.evaluate(
				script.term("ite", boolTerms[1], boolTerms[3], boolTerms[0])));
		assertEquals(falseTerm, model.evaluate(
				script.term("ite", boolTerms[1], boolTerms[0], boolTerms[3])));
		assertEquals(trueTerm, model.evaluate(script.term("Pred", trueTerm)));
		assertEquals(falseTerm, model.evaluate(script.term("Pred", falseTerm)));
		// Unconstrained Booleans should be mapped to false
		assertEquals(falseTerm, model.evaluate(script.term("Unused", trueTerm)));
		assertEquals(falseTerm, model.evaluate(script.term("Unused", falseTerm)));
	}
	
	public void testTermITE() {
		Script script = setupScript(Logics.QF_UF);
		Term[] boolTerms = new Term[m_BooleanNames.length];
		Sort bool = script.sort("Bool");
		int p = -1;
		for (String name : m_BooleanNames) {
			script.declareFun(name, EMPTY_SORT_ARRAY, bool);
			boolTerms[++p] = script.term(name);
		}
		boolean pos = true;
		// All even indices are of positive, all odd are of negative polarity.
		for (Term bt : boolTerms) {
			script.assertTerm(pos ? bt : script.term("not", bt));
			pos = !pos;
		}
		Term ite1 = script.term("ite", boolTerms[0], boolTerms[1], boolTerms[2]);
		Term ite2 = script.term("ite", boolTerms[3], boolTerms[2], boolTerms[1]);
		script.assertTerm(script.term("=", ite1, ite2));
		LBool isSat = script.checkSat();
		assertEquals(LBool.SAT, isSat);
		Term trueTerm = script.term("true");
		Term falseTerm = script.term("false");
		Model model = script.getModel();
		pos = true;
		for (Term bt : boolTerms) {
			Term val = model.evaluate(bt);
			assertEquals(pos ? trueTerm : falseTerm, val);
			pos = !pos;
		}
		assertEquals(falseTerm, model.evaluate(ite1));
		assertEquals(falseTerm, model.evaluate(ite2));
	}
	
	public void testLIA() {
		Script script = setupScript(Logics.QF_LIA);
		Term[] intTerms = new Term[m_VarNames.length];
		Sort intSort = script.sort("Int");
		int p = -1;
		for (String name : m_VarNames) {
			script.declareFun(name, EMPTY_SORT_ARRAY, intSort);
			intTerms[++p] = script.term(name);
		}
		script.assertTerm(script.term("<", intTerms));
		LBool isSat = script.checkSat();
		assertEquals(LBool.SAT, isSat);
		Term trueTerm = script.term("true");
		Term falseTerm = script.term("false");
		Model model = script.getModel();
		assertEquals(Rational.ONE,
				getConstantTerm(model, script.numeral(BigInteger.ONE)).
					getValue());
		ConstantTerm uval = getConstantTerm(model, intTerms[0]);
		ConstantTerm vval = getConstantTerm(model, intTerms[1]);
		Rational diff = ((Rational) uval.getValue()).sub(
				(Rational) vval.getValue());
		// We have u < v ==> u - v < 0
		assertTrue(diff.compareTo(Rational.ZERO) < 0);
		// u < v ?
		assertEquals(trueTerm, model.evaluate(
				script.term("<", intTerms[0], intTerms[1])));
		// u > v ?
		assertEquals(falseTerm, model.evaluate(
				script.term(">", intTerms[0], intTerms[1])));
		// u <= v ?
		assertEquals(trueTerm, model.evaluate(
				script.term("<=", intTerms[0], intTerms[1])));
		// u >= v ?
		assertEquals(falseTerm, model.evaluate(
				script.term(">=", intTerms[0], intTerms[1])));
		// u = v ?
		assertEquals(falseTerm, model.evaluate(
				script.term("=", intTerms[0], intTerms[1])));
		// u != v ?
		assertEquals(trueTerm, model.evaluate(
				script.term("distinct", intTerms[0], intTerms[1])));
		// associativity: v < w < u ?
		assertEquals(falseTerm, model.evaluate(
				script.term("<", intTerms[1], intTerms[2], intTerms[0])));
		// associativity: u < v < w
		assertEquals(trueTerm, model.evaluate(
				script.term("<", intTerms[0], intTerms[1], intTerms[2])));
		// associativity: v > w > u ?
		assertEquals(falseTerm, model.evaluate(
				script.term(">", intTerms[1], intTerms[2], intTerms[0])));
		// associativity: w > v > u
		assertEquals(trueTerm, model.evaluate(
				script.term(">", intTerms[2], intTerms[1], intTerms[0])));
		// associativity: v <= w <= u ?
		assertEquals(falseTerm, model.evaluate(
				script.term("<=", intTerms[1], intTerms[2], intTerms[0])));
		// associativity: u <= v <= w
		assertEquals(trueTerm, model.evaluate(
				script.term("<=", intTerms[0], intTerms[1], intTerms[2])));
		// associativity: v >= w >= u ?
		assertEquals(falseTerm, model.evaluate(
				script.term(">=", intTerms[1], intTerms[2], intTerms[0])));
		// associativity: w >= v >= u
		assertEquals(trueTerm, model.evaluate(
				script.term(">=", intTerms[2], intTerms[1], intTerms[0])));
		ConstantTerm wwal = getConstantTerm(model, intTerms[2]);
		// Test for math operations
		// + (simple)
		Rational expected = ((Rational) uval.getValue()).add(
				(Rational) vval.getValue()).add((Rational) wwal.getValue());
		ConstantTerm got = getConstantTerm(model, script.term(
				"+", intTerms[0], intTerms[1], intTerms[2]));
		assertEquals(expected, got.getValue());
		// - (simple)
		expected = ((Rational) uval.getValue()).sub(
				(Rational) vval.getValue()).sub((Rational) wwal.getValue());
		got = getConstantTerm(model, script.term(
				"-", intTerms[0], intTerms[1], intTerms[2]));
		assertEquals(expected, got.getValue());
		// * (simple)
		expected = ((Rational) uval.getValue()).mul(BigInteger.TEN);
		got = getConstantTerm(model, script.term(
				"*", script.numeral(BigInteger.TEN), intTerms[0]));
		assertEquals(expected, got.getValue());
		// * (non-linear)
		expected = ((Rational) uval.getValue()).mul((Rational) vval.getValue());
		got = getConstantTerm(model, script.term(
				"*", intTerms[0], intTerms[1]));
		assertEquals(expected, got.getValue());
		// Now, I fix the value of a variable to compute the values of div, mod,
		// (_ divisible n), abs
		Term xvar = intTerms[4];
		Term tten = script.numeral(BigInteger.TEN);
		Term tnine = script.numeral(BigInteger.valueOf(9));
		Term tmnine = script.numeral(BigInteger.valueOf(-9));
		script.assertTerm(script.term("=", xvar, tten));
		isSat = script.checkSat();
		assertEquals(LBool.SAT, isSat);
		model = script.getModel();
		Rational ten = Rational.valueOf(10, 1);
		assertEquals(ten, getConstantTerm(model, xvar).getValue());
		// div
		assertEquals(Rational.ONE, getConstantTerm(model,
				script.term("div", xvar, tten)).getValue());
		// Test rounding according to standard
		assertEquals(Rational.ONE, getConstantTerm(model,
				script.term("div", xvar, tnine)).getValue());
		assertEquals(Rational.MONE, getConstantTerm(model,
				script.term("div", xvar, tmnine)).getValue());
		// mod
		assertEquals(Rational.ZERO, getConstantTerm(model,
				script.term("mod", xvar, tten)).getValue());
		// Test rounding according to standard
		assertEquals(Rational.ONE, getConstantTerm(model,
				script.term("mod", xvar, tnine)).getValue());
		assertEquals(Rational.ONE, getConstantTerm(model,
				script.term("mod", xvar, tmnine)).getValue());
		// divisible
		assertEquals(trueTerm, model.evaluate(
				script.term("divisible", new BigInteger[]{BigInteger.TEN}, null,
						xvar)));
		assertEquals(falseTerm, model.evaluate(
				script.term("divisible",
						new BigInteger[]{BigInteger.valueOf(9)}, null, xvar)));
		// abs
		assertEquals(model.evaluate(xvar), model.evaluate(script.term("abs",
				script.term("-", xvar))));
	}
	
	public void testLRA() {
		// since we have testLIA and the internals of the model tester do not
		// care about the types, we don't have to repeat the simple tests here
		// New tests needed for /, infinitesimal elements, and tableau
		// simplification
		Script script = setupScript(Logics.QF_LRA);
		Term[] realTerms = new Term[m_VarNames.length];
		Sort realSort = script.sort("Real");
		int p = -1;
		for (String name : m_VarNames) {
			script.declareFun(name, EMPTY_SORT_ARRAY, realSort);
			realTerms[++p] = script.term(name);
		}
		// Keep realTerms[1] unconstrained => simplifier test
		script.assertTerm(script.term("=", realTerms[0], realTerms[1]));
		script.assertTerm(script.term("=", realTerms[0],
				script.term("*", script.numeral("2"), realTerms[2])));
		script.assertTerm(script.term("=", realTerms[0],
				script.numeral(BigInteger.TEN)));
		// w < x
		script.assertTerm(script.term("<", realTerms[3], realTerms[4]));
		// Make either w or x non-integer
		script.assertTerm(script.term("<", realTerms[4],
				script.term("+", realTerms[3],
						script.numeral(BigInteger.ONE))));
		LBool isSat = script.checkSat();
		assertEquals(LBool.SAT, isSat);
		Model model = script.getModel();
		Rational ten = Rational.valueOf(10, 1);
		Rational five = Rational.valueOf(5, 1);
		assertEquals(ten, getConstantTerm(model, realTerms[0]).getValue());
		assertEquals(ten, getConstantTerm(model, realTerms[1]).getValue());
		assertEquals(five, getConstantTerm(model, realTerms[2]).getValue());
		// Tests for /
		assertEquals(Rational.ONE, getConstantTerm(model,
				script.term("/", realTerms[0], realTerms[1])).getValue());
		assertEquals(Rational.ONE, getConstantTerm(model,
				script.term("/", realTerms[0], realTerms[1])).getValue());
		assertEquals(Rational.TWO, getConstantTerm(model,
				script.term("/", realTerms[0], realTerms[2])).getValue());
		// Infinitesimal test
		Rational wval =
			(Rational) getConstantTerm(model, realTerms[3]).getValue();
		Rational xval =
			(Rational) getConstantTerm(model, realTerms[4]).getValue();
		assertTrue(wval.compareTo(xval) < 0);
		assertTrue(!wval.isIntegral() || ! xval.isIntegral());
		// Unused rational variable test
		assertEquals(Rational.ZERO,
				getConstantTerm(model, realTerms[5]).getValue());
	}
	
	public void testLIRA() {
		Script script = setupScript(Logics.QF_UFLIRA);
		LBool isSat = script.checkSat();
		assertEquals(LBool.SAT, isSat);
		Model model = script.getModel();
		// Test to_int floor
		assertEquals(Rational.ZERO, getConstantTerm(model, script.term("to_int",
				script.term("/", script.decimal("1.0"),
						script.decimal("2.0")))).getValue());
		// Test to_real noop
		assertEquals(Rational.ZERO, getConstantTerm(model, script.term(
				"to_real", script.numeral("0"))).getValue());
		// Test is_int
		assertEquals(script.term("true"),
				model.evaluate(script.term("is_int", script.decimal("1"))));
		assertEquals(script.term("false"),
				model.evaluate(script.term("is_int", script.decimal("1.1"))));
	}
	
	public void testUF() {
		Script script = setupScript(Logics.QF_UF);
		script.declareSort("U", 0);
		Sort u = script.sort("U");
		script.declareSort("V", 0);
		Sort v = script.sort("V");
		script.declareFun("f", new Sort[] {u}, u);
		script.declareFun("g", new Sort[] {u}, u);
		script.declareFun("x", EMPTY_SORT_ARRAY, u);
		script.declareFun("y", EMPTY_SORT_ARRAY, u);
		script.declareFun("z1", EMPTY_SORT_ARRAY, v);
		script.declareFun("z2", EMPTY_SORT_ARRAY, v);
		Term x = script.term("x");
		Term fx = script.term("f", x);
		script.assertTerm(script.term("=", x, fx));
		LBool isSat = script.checkSat();
		assertEquals(LBool.SAT, isSat);
		Model model = script.getModel();
		Term val = model.evaluate(x);
		assertEquals(val, model.evaluate(fx));
		assertEquals(val, model.evaluate(script.term("f", fx)));
		// Test for stack overflows in the evaluation
		Term testTerm = fx;
		for (int i = 0; i < 1000000; ++i)
			testTerm = script.term("f", testTerm);
		assertEquals(val, model.evaluate(testTerm));
		// Dynamic completion check
		// 1. U already has an element in the domain (val)
		// => all unconstrained elements are mapped to val
		assertEquals(val, model.evaluate(script.term("y")));
		assertEquals(val, model.evaluate(script.term("f", script.term("y"))));
		// 2. V does not have any constrained elements
		// => first element will describe the singleton value of this sort
		Term z1 = script.term("z1");
		assertEquals(z1, model.evaluate(z1));
		Term z2 = script.term("z2");
		assertEquals(z1, model.evaluate(z2));
	}
	
	public void testShared() {
		Script script = setupScript(Logics.QF_UFLIA);
		Sort intSort = script.sort("Int");
		script.declareFun("f", new Sort[] {intSort}, intSort);
		script.declareFun("x", EMPTY_SORT_ARRAY, intSort);
		script.declareFun("y", EMPTY_SORT_ARRAY, intSort);
		Term x = script.term("x");
		Term y = script.term("y");
		Term fx5 = script.term("f", script.term("+", x, script.numeral("5")));
		Rational five = Rational.valueOf(5, 1);
		script.assertTerm(script.term("=", fx5, x));
		script.assertTerm(script.term("=", x, script.numeral("5")));
		script.assertTerm(script.term(">", y, script.numeral(BigInteger.ZERO)));
		LBool isSat = script.checkSat();
		assertEquals(LBool.SAT, isSat);
		Model model = script.getModel();
		assertEquals(five, getConstantTerm(model, x).getValue());
		assertEquals(five, getConstantTerm(model, fx5).getValue());
		Rational yval = (Rational) getConstantTerm(model, y).getValue();
		// Evaluate f at position x - y + (y+5)
		Rational yvalminus5 = yval.add(five);
		assertEquals(five,
				getConstantTerm(model,
						script.term("f", script.term("+", x,
								script.term("-", y),
								yvalminus5.toSMTLIB(intSort.getTheory())))).
								getValue());
		assertEquals(five, getConstantTerm(model,
				script.term("f", script.numeral(BigInteger.TEN))).getValue());
	}
	
	public void testValuation() {
		Script script = setupScript(Logics.QF_LIA);
		Term[] intTerms = new Term[m_VarNames.length];
		Sort intSort = script.sort("Int");
		int p = -1;
		for (String name : m_VarNames) {
			script.declareFun(name, EMPTY_SORT_ARRAY, intSort);
			intTerms[++p] = script.term(name);
		}
		for (int i = 0; i < intTerms.length; ++i)
			script.assertTerm(script.term("=",
					intTerms[i], script.numeral(BigInteger.valueOf(i))));
		LBool isSat = script.checkSat();
		assertEquals(LBool.SAT, isSat);
		Model model = script.getModel();
		Map<Term, Term> valuation = script.getValue(intTerms);
		Map<Term, Term> modeleval = model.evaluate(intTerms);
		for (int i = 0; i < intTerms.length; ++i) {
			Rational val = Rational.valueOf(i, 1);
			Term expected = val.toTerm(intSort);
			assertEquals(expected, valuation.get(intTerms[i]));
			assertEquals(expected, modeleval.get(intTerms[i]));
			assertEquals(expected, model.evaluate(intTerms[i]));
		}
	}
	
}
