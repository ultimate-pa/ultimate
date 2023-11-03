/*
 * Copyright (C) 2020 Leonard Fichtner
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Random;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.NamedAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.muses.MusEnumerationScript.HeuristicsType;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.SMTInterpolConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol.ProofMode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.TerminationRequest;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.TimeoutHandler;

/**
 * Tests for everything that has to do with MUSes.
 *
 * @author LeonardFichtner
 *
 */
public class MusesTest {

	private Script setupScript(final Logics logic) {
		final Script script = new SMTInterpol();
		script.setOption(SMTLIBConstants.PRODUCE_MODELS, true);
		script.setOption(SMTLIBConstants.PRODUCE_PROOFS, true);
		script.setOption(SMTLIBConstants.INTERACTIVE_MODE, true);
		script.setOption(SMTLIBConstants.PRODUCE_UNSAT_CORES, true);
		script.setOption(SMTInterpolConstants.PROOF_LEVEL, ProofMode.FULL);
		script.setLogic(logic);
		return script;
	}

	private Script setupScript(final Logics logic, final TerminationRequest request, final LogProxy logger) {
		final Script script = new SMTInterpol(logger, request);
		script.setOption(SMTLIBConstants.PRODUCE_MODELS, true);
		script.setOption(SMTLIBConstants.PRODUCE_PROOFS, true);
		script.setOption(SMTLIBConstants.INTERACTIVE_MODE, true);
		script.setOption(SMTLIBConstants.PRODUCE_UNSAT_CORES, true);
		script.setOption(SMTInterpolConstants.PROOF_LEVEL, ProofMode.FULL);
		script.setLogic(logic);
		return script;
	}

	private MusEnumerationScript setupMusEnumerationScript(final Logics logic) {
		final SMTInterpol smtInterpol = new SMTInterpol();
		smtInterpol.setOption(SMTInterpolConstants.PRODUCE_INTERPOLANTS, true);
		smtInterpol.setOption(SMTLIBConstants.PRODUCE_PROOFS, true);
		smtInterpol.setOption(SMTLIBConstants.PRODUCE_UNSAT_CORES, true);
		smtInterpol.setOption(SMTInterpolConstants.PROOF_LEVEL, ProofMode.FULL);
		smtInterpol.setLogic(logic);
		return new MusEnumerationScript(smtInterpol);
	}

	/**
	 * Note that the constraints should be declared in the solver, but no
	 * constraints should be asserted!
	 */
	private void checkWhetherSetIsMus(final BitSet supposedMus, final ConstraintAdministrationSolver solver) {
		checkUnsat(supposedMus, solver);
		checkMinimality(supposedMus, solver);
	}

	/**
	 * Note that the constraints should be declared in the solver, but no
	 * constraints should be asserted!
	 */
	private void checkUnsat(final BitSet supposedMus, final ConstraintAdministrationSolver solver) {
		solver.pushRecLevel();
		for (int i = supposedMus.nextSetBit(0); i >= 0; i = supposedMus.nextSetBit(i + 1)) {
			solver.assertCriticalConstraint(i);
		}
		Assert.assertTrue(solver.checkSat() == LBool.UNSAT);
		solver.popRecLevel();
	}

	/**
	 * Note that the constraints should be declared in the solver, but no
	 * constraints should be asserted!
	 */
	private void checkMinimality(final BitSet supposedMus, final ConstraintAdministrationSolver solver) {
		solver.pushRecLevel();
		for (int i = supposedMus.nextSetBit(0); i >= 0; i = supposedMus.nextSetBit(i + 1)) {
			solver.pushRecLevel();
			for (int j = supposedMus.nextSetBit(0); j >= 0; j = supposedMus.nextSetBit(j + 1)) {
				if (i == j) {
					continue;
				}
				solver.assertCriticalConstraint(i);
			}
			Assert.assertTrue(solver.checkSat() == LBool.SAT || solver.checkSat() == LBool.UNKNOWN);
			solver.popRecLevel();
		}
		solver.popRecLevel();
	}

	private void setupUnsatSet1(final Script script, final Translator translator, final DPLLEngine engine) {
		final ArrayList<String> names = new ArrayList<>();
		final ArrayList<Annotation> annots = new ArrayList<>();
		for (int i = 0; i < 5; i++) {
			names.add("c" + String.valueOf(i));
		}
		for (int i = 0; i < names.size(); i++) {
			annots.add(new Annotation(":named", names.get(i)));
		}
		final Sort intSort = script.sort("Int");
		script.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("z", Script.EMPTY_SORT_ARRAY, intSort);
		final Term x = script.term("x");
		final Term y = script.term("y");
		final Term z = script.term("z");
		final Term c0 = script.term(">=", x, script.numeral("30"));
		final Term c1 = script.term(">=", x, script.numeral("101"));
		final Term c2 = script.term("<", x, z);
		final Term c3 = script.term("<=", z, script.numeral("101"));
		final Term c4 = script.term("=", y, script.numeral("2"));
		declareConstraint(script, translator, engine, c0, annots.get(0));
		declareConstraint(script, translator, engine, c1, annots.get(1));
		declareConstraint(script, translator, engine, c2, annots.get(2));
		declareConstraint(script, translator, engine, c3, annots.get(3));
		declareConstraint(script, translator, engine, c4, annots.get(4));
	}

	private void setupUnsatSet2(final Script script, final Translator translator, final DPLLEngine engine) {
		final ArrayList<String> names = new ArrayList<>();
		final ArrayList<Annotation> annots = new ArrayList<>();
		for (int i = 0; i < 10; i++) {
			names.add("c" + String.valueOf(i));
		}
		for (int i = 0; i < names.size(); i++) {
			annots.add(new Annotation(":named", names.get(i)));
		}
		final Sort intSort = script.sort("Int");
		script.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("z", Script.EMPTY_SORT_ARRAY, intSort);
		final Term x = script.term("x");
		final Term y = script.term("y");
		final Term z = script.term("z");
		final Term c0 = script.term("=", x, script.numeral("53"));
		final Term c1 = script.term(">", x, script.numeral("23"));
		final Term c2 = script.term("<", x, z);
		final Term c3 = script.term("=", x, script.numeral("535"));
		final Term c4 = script.term("=", y, script.numeral("1234"));
		final Term c5 = script.term("<=", z, script.numeral("23"));
		final Term c6 = script.term(">=", x, script.numeral("34"));
		final Term c7 = script.term("=", y, script.numeral("4321"));
		final Term c8 = script.term("=", x, script.numeral("23"));
		final Term c9 = script.term("=", x, script.numeral("5353"));
		declareConstraint(script, translator, engine, c0, annots.get(0));
		declareConstraint(script, translator, engine, c1, annots.get(1));
		declareConstraint(script, translator, engine, c2, annots.get(2));
		declareConstraint(script, translator, engine, c3, annots.get(3));
		declareConstraint(script, translator, engine, c4, annots.get(4));
		declareConstraint(script, translator, engine, c5, annots.get(5));
		declareConstraint(script, translator, engine, c6, annots.get(6));
		declareConstraint(script, translator, engine, c7, annots.get(7));
		declareConstraint(script, translator, engine, c8, annots.get(8));
		declareConstraint(script, translator, engine, c9, annots.get(9));
	}

	private void setupUnsatSet2AssertSomeAsAxioms1(final Script script, final Translator translator,
			final DPLLEngine engine) {
		final ArrayList<String> names = new ArrayList<>();
		final ArrayList<Annotation> annots = new ArrayList<>();
		for (int i = 0; i < 10; i++) {
			names.add("c" + String.valueOf(i));
		}
		for (int i = 0; i < names.size(); i++) {
			annots.add(new Annotation(":named", names.get(i)));
		}
		final Sort intSort = script.sort("Int");
		script.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("z", Script.EMPTY_SORT_ARRAY, intSort);
		final Term x = script.term("x");
		final Term y = script.term("y");
		final Term z = script.term("z");
		final Term c0 = script.term("=", x, script.numeral("53"));
		final Term c1 = script.term(">", x, script.numeral("23"));
		final Term c2 = script.term("<", x, z);
		final Term c3 = script.term("=", x, script.numeral("535"));
		final Term c4 = script.term("=", y, script.numeral("1234"));
		final Term c5 = script.term("<=", z, script.numeral("23"));
		final Term c6 = script.term(">=", x, script.numeral("34"));
		final Term c7 = script.term("=", y, script.numeral("4321"));
		final Term c8 = script.term("=", x, script.numeral("23"));
		final Term c9 = script.term("=", x, script.numeral("5353"));
		script.assertTerm(c0);
		declareConstraint(script, translator, engine, c1, annots.get(1));
		declareConstraint(script, translator, engine, c2, annots.get(2));
		declareConstraint(script, translator, engine, c3, annots.get(3));
		script.assertTerm(c4);
		declareConstraint(script, translator, engine, c5, annots.get(5));
		declareConstraint(script, translator, engine, c6, annots.get(6));
		declareConstraint(script, translator, engine, c7, annots.get(7));
		declareConstraint(script, translator, engine, c8, annots.get(8));
		declareConstraint(script, translator, engine, c9, annots.get(9));
	}

	private void setupUnsatSet2AssertSomeAsAxioms2(final Script script, final Translator translator,
			final DPLLEngine engine) {
		final ArrayList<String> names = new ArrayList<>();
		final ArrayList<Annotation> annots = new ArrayList<>();
		for (int i = 0; i < 10; i++) {
			names.add("c" + String.valueOf(i));
		}
		for (int i = 0; i < names.size(); i++) {
			annots.add(new Annotation(":named", names.get(i)));
		}
		final Sort intSort = script.sort("Int");
		script.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("z", Script.EMPTY_SORT_ARRAY, intSort);
		final Term x = script.term("x");
		final Term y = script.term("y");
		final Term z = script.term("z");
		final Term c0 = script.term("=", x, script.numeral("53"));
		final Term c1 = script.term(">", x, script.numeral("23"));
		final Term c2 = script.term("<", x, z);
		final Term c3 = script.term("=", x, script.numeral("535"));
		final Term c4 = script.term("=", y, script.numeral("1234"));
		final Term c5 = script.term("<=", z, script.numeral("23"));
		final Term c6 = script.term(">=", x, script.numeral("34"));
		final Term c7 = script.term("=", y, script.numeral("4321"));
		final Term c8 = script.term("=", x, script.numeral("23"));
		final Term c9 = script.term("=", x, script.numeral("5353"));
		declareConstraint(script, translator, engine, c0, annots.get(0));
		declareConstraint(script, translator, engine, c1, annots.get(1));
		script.assertTerm(c2);
		declareConstraint(script, translator, engine, c3, annots.get(3));
		declareConstraint(script, translator, engine, c4, annots.get(4));
		declareConstraint(script, translator, engine, c5, annots.get(5));
		declareConstraint(script, translator, engine, c6, annots.get(6));
		declareConstraint(script, translator, engine, c7, annots.get(7));
		declareConstraint(script, translator, engine, c8, annots.get(8));
		declareConstraint(script, translator, engine, c9, annots.get(9));
	}

	private void setupUnsatSet3(final Script script, final Translator translator, final DPLLEngine engine) {
		final ArrayList<String> names = new ArrayList<>();
		final ArrayList<Annotation> annots = new ArrayList<>();
		for (int i = 0; i < 3; i++) {
			names.add("c" + String.valueOf(i));
		}
		for (int i = 0; i < names.size(); i++) {
			annots.add(new Annotation(":named", names.get(i)));
		}
		final Sort intSort = script.sort("Int");
		script.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("z", Script.EMPTY_SORT_ARRAY, intSort);
		final Term x = script.term("x");
		final Term z = script.term("z");
		final Term c0 = script.term(">=", x, script.numeral("101"));
		final Term c1 = script.term("<", x, z);
		final Term c2 = script.term("<=", z, script.numeral("101"));
		declareConstraint(script, translator, engine, c0, annots.get(0));
		declareConstraint(script, translator, engine, c1, annots.get(1));
		declareConstraint(script, translator, engine, c2, annots.get(2));
	}

	/**
	 * This is really just unsat set 2, but with different order.
	 */
	private void setupUnsatSet4(final Script script, final Translator translator, final DPLLEngine engine) {
		final ArrayList<String> names = new ArrayList<>();
		final ArrayList<Annotation> annots = new ArrayList<>();
		for (int i = 0; i < 10; i++) {
			names.add("c" + String.valueOf(i));
		}
		for (int i = 0; i < names.size(); i++) {
			annots.add(new Annotation(":named", names.get(i)));
		}
		final Sort intSort = script.sort("Int");
		script.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("z", Script.EMPTY_SORT_ARRAY, intSort);
		final Term x = script.term("x");
		final Term y = script.term("y");
		final Term z = script.term("z");
		final Term c0 = script.term(">", x, script.numeral("23"));
		final Term c1 = script.term("=", x, script.numeral("5353"));
		final Term c2 = script.term("<", x, z);
		final Term c3 = script.term("=", x, script.numeral("535"));
		final Term c4 = script.term("=", y, script.numeral("1234"));
		final Term c5 = script.term("=", x, script.numeral("53"));
		final Term c6 = script.term(">=", x, script.numeral("34"));
		final Term c7 = script.term("=", y, script.numeral("4321"));
		final Term c8 = script.term("=", x, script.numeral("23"));
		final Term c9 = script.term("<=", z, script.numeral("23"));
		declareConstraint(script, translator, engine, c0, annots.get(0));
		declareConstraint(script, translator, engine, c1, annots.get(1));
		declareConstraint(script, translator, engine, c2, annots.get(2));
		declareConstraint(script, translator, engine, c3, annots.get(3));
		declareConstraint(script, translator, engine, c4, annots.get(4));
		declareConstraint(script, translator, engine, c5, annots.get(5));
		declareConstraint(script, translator, engine, c6, annots.get(6));
		declareConstraint(script, translator, engine, c7, annots.get(7));
		declareConstraint(script, translator, engine, c8, annots.get(8));
		declareConstraint(script, translator, engine, c9, annots.get(9));
	}

	private void setupUnsatSet5(final Script script, final Translator translator, final DPLLEngine engine) {
		final ArrayList<String> names = new ArrayList<>();
		final ArrayList<Annotation> annots = new ArrayList<>();
		for (int i = 0; i < 10; i++) {
			names.add("c" + String.valueOf(i));
		}
		for (int i = 0; i < names.size(); i++) {
			annots.add(new Annotation(":named", names.get(i)));
		}
		final Sort intSort = script.sort("Int");
		script.declareFun("v", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("w", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("z", Script.EMPTY_SORT_ARRAY, intSort);
		final Term v = script.term("v");
		final Term w = script.term("w");
		final Term x = script.term("x");
		final Term y = script.term("y");
		final Term z = script.term("z");
		final Term c0 = script.term("<", v, w);
		final Term c1 = script.term("<", w, x);
		final Term c2 = script.term("<", x, y);
		final Term c3 = script.term("<", y, z);
		final Term c4 = script.term("=", v, script.numeral("2000"));
		final Term c5 = script.term("=", z, script.numeral("5"));
		final Term c6 = script.term("=", x, script.numeral("1000"));
		final Term c7 = script.term("=", x, script.numeral("1001"));
		final Term c8 = script.term("=", w, script.numeral("1500"));
		final Term c9 = script.term("=", y, script.numeral("100"));
		declareConstraint(script, translator, engine, c0, annots.get(0));
		declareConstraint(script, translator, engine, c1, annots.get(1));
		declareConstraint(script, translator, engine, c2, annots.get(2));
		declareConstraint(script, translator, engine, c3, annots.get(3));
		declareConstraint(script, translator, engine, c4, annots.get(4));
		declareConstraint(script, translator, engine, c5, annots.get(5));
		declareConstraint(script, translator, engine, c6, annots.get(6));
		declareConstraint(script, translator, engine, c7, annots.get(7));
		declareConstraint(script, translator, engine, c8, annots.get(8));
		declareConstraint(script, translator, engine, c9, annots.get(9));
	}

	/**
	 * Version of UnsatSet5 with a constraint that should be UNKNOWN.
	 */
	private void setupUnknownSet1(final Script script, final Translator translator, final DPLLEngine engine) {
		final ArrayList<String> names = new ArrayList<>();
		final ArrayList<Annotation> annots = new ArrayList<>();
		for (int i = 0; i < 11; i++) {
			names.add("c" + String.valueOf(i));
		}
		for (int i = 0; i < names.size(); i++) {
			annots.add(new Annotation(":named", names.get(i)));
		}
		final Sort intSort = script.sort("Int");
		final Sort[] intSortArray = new Sort[1];
		intSortArray[0] = intSort;
		script.declareFun("v", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("w", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("z", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("f", intSortArray, intSort);
		final Term v = script.term("v");
		final Term w = script.term("w");
		final Term x = script.term("x");
		final Term y = script.term("y");
		final Term z = script.term("z");

		final TermVariable u = script.variable("u", intSort);
		final Term fOfu = script.term("f", u);

		final Term c0 = script.term("<", v, w);
		final Term c1 = script.term("<", w, x);
		final Term c2 = script.term("<", x, y);
		final Term c3 = script.term("<", y, z);
		final Term c4 = script.term("=", v, script.numeral("2000"));
		final Term c5 = script.term("=", z, script.numeral("5"));
		final Term c6 = script.term("=", x, script.numeral("1000"));
		final Term c7 = script.term("=", x, script.numeral("1001"));
		final Term c8 = script.term("=", w, script.numeral("1500"));
		final Term c9 = script.term("=", y, script.numeral("100"));
		final Term fOfuEqu = script.term("=", fOfu, u);
		final Term c10 = script.quantifier(Script.FORALL, new TermVariable[] { u }, fOfuEqu);

		declareConstraint(script, translator, engine, c0, annots.get(0));
		declareConstraint(script, translator, engine, c1, annots.get(1));
		declareConstraint(script, translator, engine, c2, annots.get(2));
		declareConstraint(script, translator, engine, c3, annots.get(3));
		declareConstraint(script, translator, engine, c4, annots.get(4));
		declareConstraint(script, translator, engine, c5, annots.get(5));
		declareConstraint(script, translator, engine, c6, annots.get(6));
		declareConstraint(script, translator, engine, c7, annots.get(7));
		declareConstraint(script, translator, engine, c8, annots.get(8));
		declareConstraint(script, translator, engine, c9, annots.get(9));
		declareConstraint(script, translator, engine, c10, annots.get(10));
	}

	/**
	 * Version of UnsatSet5 with three constraints c10, c11. C10, c11 are
	 * LBool.UNKNOWN and could be determined unsat with a third constraint c12
	 * (despite of c10, c11 being unsat on together already).
	 */
	private void setupUnknownSet2(final Script script, final Translator translator, final DPLLEngine engine) {
		final ArrayList<String> names = new ArrayList<>();
		final ArrayList<Annotation> annots = new ArrayList<>();
		for (int i = 0; i < 13; i++) {
			names.add("c" + String.valueOf(i));
		}
		for (int i = 0; i < names.size(); i++) {
			annots.add(new Annotation(":named", names.get(i)));
		}
		final Sort intSort = script.sort("Int");
		final Sort[] intSortArray = new Sort[1];
		intSortArray[0] = intSort;
		script.declareFun("v", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("w", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("z", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("a", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("b", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("f", intSortArray, intSort);
		script.declareFun("g", intSortArray, intSort);
		final Term v = script.term("v");
		final Term w = script.term("w");
		final Term x = script.term("x");
		final Term y = script.term("y");
		final Term z = script.term("z");
		final Term a = script.term("a");
		final Term b = script.term("b");

		final TermVariable t = script.variable("t", intSort);
		final TermVariable u = script.variable("u", intSort);

		final Term gOfu = script.term("g", u);
		final Term fOfgOfu = script.term("f", gOfu);
		final Term fOfgOfuEqu = script.term("=", fOfgOfu, u);

		final Term fOft = script.term("f", t);
		final Term fOftEqa = script.term("=", fOft, a);
		final Term fOftNeqa = script.term("not", fOftEqa);

		final Term gOfa = script.term("g", a);
		final Term fOfgOfa = script.term("f", gOfa);

		final Term c0 = script.term("<", v, w);
		final Term c1 = script.term("<", w, x);
		final Term c2 = script.term("<", x, y);
		final Term c3 = script.term("<", y, z);
		final Term c4 = script.term("=", v, script.numeral("2000"));
		final Term c5 = script.term("=", z, script.numeral("5"));
		final Term c6 = script.term("=", x, script.numeral("1000"));
		final Term c7 = script.term("=", x, script.numeral("1001"));
		final Term c8 = script.term("=", w, script.numeral("1500"));
		final Term c9 = script.term("=", y, script.numeral("100"));
		final Term c10 = script.quantifier(Script.FORALL, new TermVariable[] { u }, fOfgOfuEqu);
		final Term c11 = script.quantifier(Script.FORALL, new TermVariable[] { t }, fOftNeqa);
		final Term c12 = script.term("=", fOfgOfa, b);

		declareConstraint(script, translator, engine, c0, annots.get(0));
		declareConstraint(script, translator, engine, c1, annots.get(1));
		declareConstraint(script, translator, engine, c2, annots.get(2));
		declareConstraint(script, translator, engine, c3, annots.get(3));
		declareConstraint(script, translator, engine, c4, annots.get(4));
		declareConstraint(script, translator, engine, c5, annots.get(5));
		declareConstraint(script, translator, engine, c6, annots.get(6));
		declareConstraint(script, translator, engine, c7, annots.get(7));
		declareConstraint(script, translator, engine, c8, annots.get(8));
		declareConstraint(script, translator, engine, c9, annots.get(9));
		declareConstraint(script, translator, engine, c10, annots.get(10));
		declareConstraint(script, translator, engine, c11, annots.get(11));
		declareConstraint(script, translator, engine, c12, annots.get(12));
	}

	/**
	 * Version of UnsatSet5 with three constraints c10, c11. C10, c11 are
	 * LBool.UNKNOWN and could be determined unsat with a third constraint c12
	 * (despite of c10, c11 being unsat on together already). But c12 is not in
	 * this set.
	 */
	private void setupUnknownSet3(final Script script, final Translator translator, final DPLLEngine engine) {
		final ArrayList<String> names = new ArrayList<>();
		final ArrayList<Annotation> annots = new ArrayList<>();
		for (int i = 0; i < 13; i++) {
			names.add("c" + String.valueOf(i));
		}
		for (int i = 0; i < names.size(); i++) {
			annots.add(new Annotation(":named", names.get(i)));
		}
		final Sort intSort = script.sort("Int");
		final Sort[] intSortArray = new Sort[1];
		intSortArray[0] = intSort;
		script.declareFun("v", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("w", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("z", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("a", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("b", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("f", intSortArray, intSort);
		script.declareFun("g", intSortArray, intSort);
		final Term v = script.term("v");
		final Term w = script.term("w");
		final Term x = script.term("x");
		final Term y = script.term("y");
		final Term z = script.term("z");
		final Term a = script.term("a");
		final Term b = script.term("b");

		final TermVariable t = script.variable("t", intSort);
		final TermVariable u = script.variable("u", intSort);

		final Term gOfu = script.term("g", u);
		final Term fOfgOfu = script.term("f", gOfu);
		final Term fOfgOfuEqu = script.term("=", fOfgOfu, u);

		final Term fOft = script.term("f", t);
		final Term fOftEqa = script.term("=", fOft, a);
		final Term fOftNeqa = script.term("not", fOftEqa);

		final Term c0 = script.term("<", v, w);
		final Term c1 = script.term("<", w, x);
		final Term c2 = script.term("<", x, y);
		final Term c3 = script.term("<", y, z);
		final Term c4 = script.term("=", v, script.numeral("2000"));
		final Term c5 = script.term("=", z, script.numeral("5"));
		final Term c6 = script.term("=", x, script.numeral("1000"));
		final Term c7 = script.term("=", x, script.numeral("1001"));
		final Term c8 = script.term("=", w, script.numeral("1500"));
		final Term c9 = script.term("=", y, script.numeral("100"));
		final Term c10 = script.quantifier(Script.FORALL, new TermVariable[] { u }, fOfgOfuEqu);
		final Term c11 = script.quantifier(Script.FORALL, new TermVariable[] { t }, fOftNeqa);

		declareConstraint(script, translator, engine, c0, annots.get(0));
		declareConstraint(script, translator, engine, c1, annots.get(1));
		declareConstraint(script, translator, engine, c2, annots.get(2));
		declareConstraint(script, translator, engine, c3, annots.get(3));
		declareConstraint(script, translator, engine, c4, annots.get(4));
		declareConstraint(script, translator, engine, c5, annots.get(5));
		declareConstraint(script, translator, engine, c6, annots.get(6));
		declareConstraint(script, translator, engine, c7, annots.get(7));
		declareConstraint(script, translator, engine, c8, annots.get(8));
		declareConstraint(script, translator, engine, c9, annots.get(9));
		declareConstraint(script, translator, engine, c10, annots.get(10));
		declareConstraint(script, translator, engine, c11, annots.get(11));
	}

	private void declareConstraint(final Script script, final Translator translator, final DPLLEngine engine,
			final Term constraint, final Annotation... annotation) throws SMTLIBException {
		final AnnotatedTerm annotatedConstraint = (AnnotatedTerm) script.annotate(constraint, annotation);
		final NamedAtom atom = new NamedAtom(annotatedConstraint, 0);
		atom.setPreferredStatus(atom.getAtom());
		atom.lockPreferredStatus();
		engine.addAtom(atom);
		translator.declareConstraint(atom);
	}

	private void setupUnsatSet2(final MusEnumerationScript script) {
		final ArrayList<String> names = new ArrayList<>();
		final ArrayList<Annotation> annots = new ArrayList<>();
		for (int i = 0; i < 10; i++) {
			names.add("c" + String.valueOf(i));
		}
		for (int i = 0; i < names.size(); i++) {
			annots.add(new Annotation(":named", names.get(i)));
		}
		final Sort intSort = script.sort("Int");
		script.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("z", Script.EMPTY_SORT_ARRAY, intSort);
		final Term x = script.term("x");
		final Term y = script.term("y");
		final Term z = script.term("z");
		final Term c0 = script.term("=", x, script.numeral("53"));
		final Term c1 = script.term(">", x, script.numeral("23"));
		final Term c2 = script.term("<", x, z);
		final Term c3 = script.term("=", x, script.numeral("535"));
		final Term c4 = script.term("=", y, script.numeral("1234"));
		final Term c5 = script.term("<=", z, script.numeral("23"));
		final Term c6 = script.term(">=", x, script.numeral("34"));
		final Term c7 = script.term("=", y, script.numeral("4321"));
		final Term c8 = script.term("=", x, script.numeral("23"));
		final Term c9 = script.term("=", x, script.numeral("5353"));
		final Term c0Anno = script.annotate(c0, annots.get(0));
		final Term c1Anno = script.annotate(c1, annots.get(1));
		final Term c2Anno = script.annotate(c2, annots.get(2));
		final Term c3Anno = script.annotate(c3, annots.get(3));
		final Term c4Anno = script.annotate(c4, annots.get(4));
		final Term c5Anno = script.annotate(c5, annots.get(5));
		final Term c6Anno = script.annotate(c6, annots.get(6));
		final Term c7Anno = script.annotate(c7, annots.get(7));
		final Term c8Anno = script.annotate(c8, annots.get(8));
		final Term c9Anno = script.annotate(c9, annots.get(9));
		script.assertTerm(c0Anno);
		script.assertTerm(c1Anno);
		script.assertTerm(c2Anno);
		script.assertTerm(c3Anno);
		script.assertTerm(c4Anno);
		script.assertTerm(c5Anno);
		script.assertTerm(c6Anno);
		script.assertTerm(c7Anno);
		script.assertTerm(c8Anno);
		script.assertTerm(c9Anno);
	}

	private void setupUnsatSet2WithUnnamedTerms1(final MusEnumerationScript script) {
		final ArrayList<String> names = new ArrayList<>();
		final ArrayList<Annotation> annots = new ArrayList<>();
		for (int i = 0; i < 10; i++) {
			names.add("c" + String.valueOf(i));
		}
		for (int i = 0; i < names.size(); i++) {
			annots.add(new Annotation(":named", names.get(i)));
		}
		final Sort intSort = script.sort("Int");
		script.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("z", Script.EMPTY_SORT_ARRAY, intSort);
		final Term x = script.term("x");
		final Term y = script.term("y");
		final Term z = script.term("z");
		final Term c0 = script.term("=", x, script.numeral("53"));
		final Term c1 = script.term(">", x, script.numeral("23"));
		final Term c2 = script.term("<", x, z);
		final Term c3 = script.term("=", x, script.numeral("535"));
		final Term c4 = script.term("=", y, script.numeral("1234"));
		final Term c5 = script.term("<=", z, script.numeral("23"));
		final Term c6 = script.term(">=", x, script.numeral("34"));
		final Term c7 = script.term("=", y, script.numeral("4321"));
		final Term c8 = script.term("=", x, script.numeral("23"));
		final Term c9 = script.term("=", x, script.numeral("5353"));
		final Term c1Anno = script.annotate(c1, annots.get(1));
		final Term c2Anno = script.annotate(c2, annots.get(2));
		final Term c3Anno = script.annotate(c3, annots.get(3));
		final Term c5Anno = script.annotate(c5, annots.get(5));
		final Term c6Anno = script.annotate(c6, annots.get(6));
		final Term c7Anno = script.annotate(c7, annots.get(7));
		final Term c8Anno = script.annotate(c8, annots.get(8));
		final Term c9Anno = script.annotate(c9, annots.get(9));
		script.assertTerm(c0);
		script.assertTerm(c1Anno);
		script.assertTerm(c2Anno);
		script.assertTerm(c3Anno);
		script.assertTerm(c4);
		script.assertTerm(c5Anno);
		script.assertTerm(c6Anno);
		script.assertTerm(c7Anno);
		script.assertTerm(c8Anno);
		script.assertTerm(c9Anno);
	}

	private void setupUnsatSet2WithUnnamedTerms2(final MusEnumerationScript script) {
		final ArrayList<String> names = new ArrayList<>();
		final ArrayList<Annotation> annots = new ArrayList<>();
		for (int i = 0; i < 10; i++) {
			names.add("c" + String.valueOf(i));
		}
		for (int i = 0; i < names.size(); i++) {
			annots.add(new Annotation(":named", names.get(i)));
		}
		final Sort intSort = script.sort("Int");
		script.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("z", Script.EMPTY_SORT_ARRAY, intSort);
		final Term x = script.term("x");
		final Term y = script.term("y");
		final Term z = script.term("z");
		final Term c0 = script.term("=", x, script.numeral("53"));
		final Term c1 = script.term(">", x, script.numeral("23"));
		final Term c2 = script.term("<", x, z);
		final Term c3 = script.term("=", x, script.numeral("535"));
		final Term c4 = script.term("=", y, script.numeral("1234"));
		final Term c5 = script.term("<=", z, script.numeral("23"));
		final Term c6 = script.term(">=", x, script.numeral("34"));
		final Term c7 = script.term("=", y, script.numeral("4321"));
		final Term c8 = script.term("=", x, script.numeral("23"));
		final Term c9 = script.term("=", x, script.numeral("5353"));
		final Term c0Anno = script.annotate(c0, annots.get(0));
		final Term c1Anno = script.annotate(c1, annots.get(1));
		final Term c3Anno = script.annotate(c3, annots.get(3));
		final Term c4Anno = script.annotate(c4, annots.get(4));
		final Term c5Anno = script.annotate(c5, annots.get(5));
		final Term c6Anno = script.annotate(c6, annots.get(6));
		final Term c7Anno = script.annotate(c7, annots.get(7));
		final Term c8Anno = script.annotate(c8, annots.get(8));
		final Term c9Anno = script.annotate(c9, annots.get(9));
		script.assertTerm(c0Anno);
		script.assertTerm(c1Anno);
		script.assertTerm(c2);
		script.assertTerm(c3Anno);
		script.assertTerm(c4Anno);
		script.assertTerm(c5Anno);
		script.assertTerm(c6Anno);
		script.assertTerm(c7Anno);
		script.assertTerm(c8Anno);
		script.assertTerm(c9Anno);
	}

	private void setupUnsatSet5(final MusEnumerationScript script) {
		final ArrayList<String> names = new ArrayList<>();
		final ArrayList<Annotation> annots = new ArrayList<>();
		for (int i = 0; i < 10; i++) {
			names.add("c" + String.valueOf(i));
		}
		for (int i = 0; i < names.size(); i++) {
			annots.add(new Annotation(":named", names.get(i)));
		}
		final Sort intSort = script.sort("Int");
		script.declareFun("v", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("w", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("z", Script.EMPTY_SORT_ARRAY, intSort);
		final Term v = script.term("v");
		final Term w = script.term("w");
		final Term x = script.term("x");
		final Term y = script.term("y");
		final Term z = script.term("z");
		final Term c0 = script.term("<", v, w);
		final Term c1 = script.term("<", w, x);
		final Term c2 = script.term("<", x, y);
		final Term c3 = script.term("<", y, z);
		final Term c4 = script.term("=", v, script.numeral("2000"));
		final Term c5 = script.term("=", z, script.numeral("5"));
		final Term c6 = script.term("=", x, script.numeral("1000"));
		final Term c7 = script.term("=", x, script.numeral("1001"));
		final Term c8 = script.term("=", w, script.numeral("1500"));
		final Term c9 = script.term("=", y, script.numeral("100"));
		final Term c0Anno = script.annotate(c0, annots.get(0));
		final Term c1Anno = script.annotate(c1, annots.get(1));
		final Term c2Anno = script.annotate(c2, annots.get(2));
		final Term c3Anno = script.annotate(c3, annots.get(3));
		final Term c4Anno = script.annotate(c4, annots.get(4));
		final Term c5Anno = script.annotate(c5, annots.get(5));
		final Term c6Anno = script.annotate(c6, annots.get(6));
		final Term c7Anno = script.annotate(c7, annots.get(7));
		final Term c8Anno = script.annotate(c8, annots.get(8));
		final Term c9Anno = script.annotate(c9, annots.get(9));
		script.assertTerm(c0Anno);
		script.assertTerm(c1Anno);
		script.assertTerm(c2Anno);
		script.assertTerm(c3Anno);
		script.assertTerm(c4Anno);
		script.assertTerm(c5Anno);
		script.assertTerm(c6Anno);
		script.assertTerm(c7Anno);
		script.assertTerm(c8Anno);
		script.assertTerm(c9Anno);
	}

	/**
	 * Version of UnsatSet5 with a constraint that should be UNKNOWN.
	 */
	private void setupUnknownSet(final MusEnumerationScript script) {
		final ArrayList<String> names = new ArrayList<>();
		final ArrayList<Annotation> annots = new ArrayList<>();
		for (int i = 0; i < 11; i++) {
			names.add("c" + String.valueOf(i));
		}
		for (int i = 0; i < names.size(); i++) {
			annots.add(new Annotation(":named", names.get(i)));
		}
		final Sort intSort = script.sort("Int");
		final Sort[] intSortArray = new Sort[1];
		intSortArray[0] = intSort;
		script.declareFun("v", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("w", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("z", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("f", intSortArray, intSort);
		final Term v = script.term("v");
		final Term w = script.term("w");
		final Term x = script.term("x");
		final Term y = script.term("y");
		final Term z = script.term("z");

		final TermVariable u = script.variable("u", intSort);
		final Term fOfu = script.term("f", u);
		final Term fOfuEqu = script.term("=", fOfu, u);

		final Term c0 = script.term("<", v, w);
		final Term c1 = script.term("<", w, x);
		final Term c2 = script.term("<", x, y);
		final Term c3 = script.term("<", y, z);
		final Term c4 = script.term("=", v, script.numeral("2000"));
		final Term c5 = script.term("=", z, script.numeral("5"));
		final Term c6 = script.term("=", x, script.numeral("1000"));
		final Term c7 = script.term("=", x, script.numeral("1001"));
		final Term c8 = script.term("=", w, script.numeral("1500"));
		final Term c9 = script.term("=", y, script.numeral("100"));
		final Term c10 = script.quantifier(Script.FORALL, new TermVariable[] { u }, fOfuEqu);

		final Term c0Anno = script.annotate(c0, annots.get(0));
		final Term c1Anno = script.annotate(c1, annots.get(1));
		final Term c2Anno = script.annotate(c2, annots.get(2));
		final Term c3Anno = script.annotate(c3, annots.get(3));
		final Term c4Anno = script.annotate(c4, annots.get(4));
		final Term c5Anno = script.annotate(c5, annots.get(5));
		final Term c6Anno = script.annotate(c6, annots.get(6));
		final Term c7Anno = script.annotate(c7, annots.get(7));
		final Term c8Anno = script.annotate(c8, annots.get(8));
		final Term c9Anno = script.annotate(c9, annots.get(9));
		final Term c10Anno = script.annotate(c10, annots.get(10));
		script.assertTerm(c0Anno);
		script.assertTerm(c1Anno);
		script.assertTerm(c2Anno);
		script.assertTerm(c3Anno);
		script.assertTerm(c4Anno);
		script.assertTerm(c5Anno);
		script.assertTerm(c6Anno);
		script.assertTerm(c7Anno);
		script.assertTerm(c8Anno);
		script.assertTerm(c9Anno);
		script.assertTerm(c10Anno);
	}

	@Test
	public void testShrinkerNormal() {
		final Script script = setupScript(Logics.AUFLIRA);
		final DPLLEngine engine = new DPLLEngine(new DefaultLogger(), null);
		final Translator translator = new Translator();
		setupUnsatSet2(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet();
		workingSet.flip(0, 10);
		final MusContainer container = Shrinking.shrink(solver, workingSet, map, new Random(1337), false);

		System.out.println("Shrinker returned: " + container.getMus().toString());
		checkWhetherSetIsMus(container.getMus(), solver);
	}

	@Test
	public void testShrinkerRestrictedSet() {
		final Script script = setupScript(Logics.AUFLIRA);
		final DPLLEngine engine = new DPLLEngine(new DefaultLogger(), null);
		final Translator translator = new Translator();
		setupUnsatSet2(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet();
		workingSet.set(0);
		workingSet.set(1);
		workingSet.set(3);
		workingSet.set(8);
		workingSet.set(9);
		workingSet.flip(0, 10);
		final MusContainer container = Shrinking.shrink(solver, workingSet, map, new Random(1337), false);

		System.out.println("Shrinker returned: " + container.getMus().toString());
		checkWhetherSetIsMus(container.getMus(), solver);
	}

	@Test
	public void testShrinkerWorkingSetIsMus() {
		final Script script = setupScript(Logics.AUFLIRA);
		final DPLLEngine engine = new DPLLEngine(new DefaultLogger(), null);
		final Translator translator = new Translator();
		setupUnsatSet2(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet();
		workingSet.set(1);
		workingSet.set(2);
		workingSet.set(5);
		final MusContainer container = Shrinking.shrink(solver, workingSet, map, new Random(1337), false);

		System.out.println("Shrinker returned: " + container.getMus().toString());
		checkWhetherSetIsMus(container.getMus(), solver);
	}

	@Test
	public void testShrinkerMusAssertedBefore() {
		final Script script = setupScript(Logics.AUFLIRA);
		final DPLLEngine engine = new DPLLEngine(new DefaultLogger(), null);
		final Translator translator = new Translator();
		setupUnsatSet2(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		solver.pushRecLevel();
		solver.assertCriticalConstraint(4);
		solver.assertCriticalConstraint(7);
		final BitSet workingSet = new BitSet();
		workingSet.set(1);
		workingSet.set(2);
		workingSet.set(4);
		workingSet.set(7);
		final MusContainer container = Shrinking.shrink(solver, workingSet, map, new Random(1337), false);

		System.out.println("Shrinker returned: " + container.getMus().toString());
		Assert.assertTrue(solver.checkSat() == LBool.UNSAT);
		solver.popRecLevel();
		checkWhetherSetIsMus(container.getMus(), solver);
	}

	@Test
	public void testShrinkerSatSetAssertedBefore() {
		final Script script = setupScript(Logics.AUFLIRA);
		final DPLLEngine engine = new DPLLEngine(new DefaultLogger(), null);
		final Translator translator = new Translator();
		setupUnsatSet2(script, translator, engine);

		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final UnexploredMap map = new UnexploredMap(engine, translator);
		solver.pushRecLevel();
		solver.assertCriticalConstraint(1);
		solver.assertCriticalConstraint(2);
		final BitSet workingSet = new BitSet();
		workingSet.set(5);
		workingSet.set(1);
		workingSet.set(2);
		final MusContainer container = Shrinking.shrink(solver, workingSet, map, new Random(1337), false);

		System.out.println("Shrinker returned: " + container.getMus().toString());
		solver.popRecLevel();
		checkWhetherSetIsMus(container.getMus(), solver);
		Assert.assertTrue(solver.checkSat() == LBool.SAT);
	}

	@Test(expected = SMTLIBException.class)
	public void testShrinkerWorkingSetDoesNotContainCrits() {
		final Script script = setupScript(Logics.AUFLIRA);
		final DPLLEngine engine = new DPLLEngine(new DefaultLogger(), null);
		final Translator translator = new Translator();
		setupUnsatSet2(script, translator, engine);

		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final UnexploredMap map = new UnexploredMap(engine, translator);
		solver.pushRecLevel();
		solver.assertCriticalConstraint(1);
		solver.assertCriticalConstraint(2);
		final BitSet workingSet = new BitSet();
		workingSet.set(5);
		final MusContainer container = Shrinking.shrink(solver, workingSet, map, new Random(1337), false);

		System.out.println("Shrinker returned: " + container.getMus().toString());
		solver.popRecLevel();
		checkWhetherSetIsMus(container.getMus(), solver);
		Assert.assertTrue(solver.checkSat() == LBool.SAT);
	}

	@Test(expected = SMTLIBException.class)
	public void testShrinkerEmptySet() {
		final Script script = setupScript(Logics.AUFLIRA);
		final DPLLEngine engine = new DPLLEngine(new DefaultLogger(), null);
		final Translator translator = new Translator();
		setupUnsatSet2(script, translator, engine);

		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final UnexploredMap map = new UnexploredMap(engine, translator);
		final BitSet workingSet = new BitSet();
		Shrinking.shrink(solver, workingSet, map, new Random(1337), false);
	}

	@Test(expected = SMTLIBException.class)
	public void testShrinkerSatSet() {
		final Script script = setupScript(Logics.AUFLIRA);
		final DPLLEngine engine = new DPLLEngine(new DefaultLogger(), null);
		final Translator translator = new Translator();
		setupUnsatSet2(script, translator, engine);

		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final UnexploredMap map = new UnexploredMap(engine, translator);
		final BitSet workingSet = new BitSet();
		workingSet.set(0);
		workingSet.set(1);
		workingSet.set(7);
		workingSet.set(5);
		Shrinking.shrink(solver, workingSet, map, new Random(1337), false);
	}

	@Test
	public void testExtensionLightDemand() {
		final Script script = setupScript(Logics.AUFLIRA);
		final DPLLEngine engine = new DPLLEngine(new DefaultLogger(), null);
		final Translator translator = new Translator();
		setupUnsatSet1(script, translator, engine);

		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		solver.assertUnknownConstraint(1);
		final BitSet extension = solver.getSatExtension(new TimeoutHandler(null));

		System.out.println(extension.toString());
		Assert.assertTrue(extension.get(0));
	}

	@Test
	public void testExtensionMediumDemand() {
		final Script script = setupScript(Logics.AUFLIRA);
		final DPLLEngine engine = new DPLLEngine(new DefaultLogger(), null);
		final Translator translator = new Translator();
		setupUnsatSet1(script, translator, engine);

		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet extension = solver.getSatExtensionMoreDemanding();

		System.out.println(extension.toString());
		Assert.assertTrue(extension.get(0));
		Assert.assertTrue(extension.get(1));
		Assert.assertTrue(extension.get(2));
		Assert.assertFalse(extension.get(3));
		Assert.assertFalse(extension.get(4));
	}

	@Test
	public void testExtensionHeavyDemand() {
		final Script script = setupScript(Logics.AUFLIRA);
		final DPLLEngine engine = new DPLLEngine(new DefaultLogger(), null);
		final Translator translator = new Translator();
		setupUnsatSet1(script, translator, engine);

		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet extension = solver.getSatExtensionMaximalDemanding();

		System.out.println(extension.toString());
		Assert.assertTrue(extension.get(0));
		Assert.assertTrue(extension.get(1));
		Assert.assertTrue(extension.get(2));
		Assert.assertFalse(extension.get(3));
		Assert.assertTrue(extension.get(4));
	}

	@Test
	public void testMapBlockDown() {
		final Script script = setupScript(Logics.AUFLIRA);
		final DPLLEngine engine = new DPLLEngine(new DefaultLogger(), new TimeoutHandler(null));
		final Translator translator = new Translator();
		setupUnsatSet3(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final BitSet set1 = new BitSet(3);
		final BitSet set2 = new BitSet(3);
		final BitSet set3 = new BitSet(3);
		final BitSet workingSet = new BitSet(3);
		workingSet.set(0, 3);
		set1.set(0);
		set1.set(1);
		set2.set(0);
		set2.set(2);
		set3.set(1);
		set3.set(2);
		map.BlockDown(set1);
		map.BlockDown(set2);
		map.BlockDown(set3);
		final BitSet unexplored = map.findMaximalUnexploredSubsetOf(workingSet);
		final BitSet crits = map.findImpliedCritsOf(workingSet);

		Assert.assertTrue(unexplored.cardinality() == 3);
		Assert.assertTrue(crits.cardinality() == 3);
	}

	@Test
	public void testMapBlockUp() {
		final Script script = setupScript(Logics.AUFLIRA);
		final DPLLEngine engine = new DPLLEngine(new DefaultLogger(), new TimeoutHandler(null));
		;
		final Translator translator = new Translator();
		setupUnsatSet3(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final BitSet set1 = new BitSet(3);
		final BitSet set2 = new BitSet(3);
		final BitSet set3 = new BitSet(3);
		final BitSet workingSet = new BitSet(3);
		workingSet.set(0, 3);
		set1.set(0);
		set1.set(1);
		set2.set(0);
		set2.set(2);
		set3.set(1);
		set3.set(2);
		map.BlockUp(set1);
		map.BlockUp(set2);
		map.BlockUp(set3);
		final BitSet crits = map.findImpliedCritsOf(workingSet);
		final BitSet unexplored = map.findMaximalUnexploredSubsetOf(workingSet);

		Assert.assertTrue(unexplored.cardinality() == 1);
		Assert.assertTrue(crits.cardinality() == 0);
	}

	@Test
	public void testMapWorkingSet() {
		final Script script = setupScript(Logics.AUFLIRA);
		final DPLLEngine engine = new DPLLEngine(new DefaultLogger(), new TimeoutHandler(null));
		final Translator translator = new Translator();
		setupUnsatSet3(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final BitSet workingSet = new BitSet(3);
		workingSet.set(1);
		workingSet.set(2);
		final BitSet crits = map.findImpliedCritsOf(workingSet);
		final BitSet unexplored = map.findMaximalUnexploredSubsetOf(workingSet);

		Assert.assertTrue(unexplored.get(1) == true);
		Assert.assertTrue(unexplored.get(2) == true);
		Assert.assertTrue(crits.cardinality() == 0);
	}

	@Test
	public void testMapNoUnexploredSet() {
		final Script script = setupScript(Logics.AUFLIRA);
		final DPLLEngine engine = new DPLLEngine(new DefaultLogger(), new TimeoutHandler(null));
		final Translator translator = new Translator();
		setupUnsatSet3(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final BitSet set1 = new BitSet(3);
		final BitSet workingSet = new BitSet(3);
		workingSet.set(0);
		workingSet.set(2);
		set1.set(0);
		set1.set(2);
		map.BlockDown(set1);
		final BitSet unexplored = map.findMaximalUnexploredSubsetOf(workingSet);
		final BitSet crits = map.findImpliedCritsOf(workingSet);

		Assert.assertTrue(unexplored.cardinality() == 0);
		Assert.assertTrue(crits.cardinality() == 0);
	}

	@Test
	public void testMapExplicitlyForFindCrits() {
		final Script script = setupScript(Logics.AUFLIRA);
		final DPLLEngine engine = new DPLLEngine(new DefaultLogger(), new TimeoutHandler(null));
		final Translator translator = new Translator();
		setupUnsatSet3(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final BitSet set1 = new BitSet(3);
		final BitSet set2 = new BitSet(3);
		final BitSet workingSet = new BitSet(3);
		set1.set(0);
		set1.set(1);
		set2.set(0);
		set2.set(2);
		workingSet.set(0);
		workingSet.set(1);
		map.BlockUp(set1);
		map.BlockDown(set2);
		final BitSet crits = map.findImpliedCritsOf(workingSet);
		final BitSet unexplored = map.findMaximalUnexploredSubsetOf(workingSet);

		Assert.assertFalse(crits.get(0));
		Assert.assertTrue(crits.get(1));
		Assert.assertFalse(crits.get(2));
		Assert.assertTrue(unexplored.cardinality() == 1);
	}

	@Test
	public void testReMusSet1() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnsatSet1(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(5);
		workingSet.flip(0, 5);
		solver.pushRecLevel();
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
		solver.popRecLevel();

		for (final MusContainer container : muses) {
			checkWhetherSetIsMus(container.getMus(), solver);
		}
		Assert.assertTrue(muses.size() == 1);
	}

	@Test
	public void testReMusSet2() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnsatSet2(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(10);
		workingSet.flip(0, 10);
		solver.pushRecLevel();
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
		solver.popRecLevel();

		for (final MusContainer container : muses) {
			checkWhetherSetIsMus(container.getMus(), solver);
		}
		Assert.assertTrue(muses.size() == 15);
	}

	@Test
	public void testReMusSet2AssertSomeAsAxioms1() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnsatSet2AssertSomeAsAxioms1(script, translator, engine);

		script.push(1);
		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(8);
		workingSet.flip(0, 8);

		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
		solver.reset();

		for (final MusContainer container : muses) {
			checkWhetherSetIsMus(container.getMus(), solver);
		}
		Assert.assertTrue(muses.size() == 5);
	}

	@Test
	public void testReMusSet2AssertSomeAsAxioms2() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnsatSet2AssertSomeAsAxioms2(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(9);
		workingSet.flip(0, 9);
		solver.pushRecLevel();
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
		solver.popRecLevel();

		for (final MusContainer container : muses) {
			checkWhetherSetIsMus(container.getMus(), solver);
		}
		Assert.assertTrue(muses.size() == 15);
	}

	@Test
	public void testReMusSet5() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnsatSet5(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(10);
		workingSet.flip(0, 10);
		solver.pushRecLevel();
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
		solver.popRecLevel();

		for (final MusContainer container : muses) {
			checkWhetherSetIsMus(container.getMus(), solver);
		}
		Assert.assertTrue(muses.size() == 15);
	}

	@Test(expected = SMTLIBException.class)
	public void testReMusUnknownSetTestFailIfUnknownAllowedTurnedOff() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnknownSet1(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(11);
		workingSet.flip(0, 11);
		solver.pushRecLevel();
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
	}

	/**
	 * Example, where a constraint, for which the solver returns LBool.UNKNOWN
	 * causes no problems (all MUSes are found, all MUSes are minimal).
	 */
	@Test
	public void testReMusUnknownSet1() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnknownSet1(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(11);
		workingSet.flip(0, 11);
		solver.pushRecLevel();
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), true, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
		solver.popRecLevel();

		for (final MusContainer container : muses) {
			checkWhetherSetIsMus(container.getMus(), solver);
			Assert.assertFalse(container.getMus().get(10));
		}
		Assert.assertTrue(muses.size() == 15);
	}

	/**
	 * This previously was an example, that MUSes might not be minimal anymore,
	 * if the solver can return LBool.UNKNOWN upon checkSat() call. The
	 * not-minimal MUS would've been the constraints c10, c11, c12. But there
	 * are certain circumstances, where the shrinker is still able to find the
	 * real (minimal) MUS c10, c11. Through some changes in the code, these
	 * circumstances now occur and I cannot reproduce the old circumstances
	 * without undoing the changes in the code. Therefore, this test has been
	 * degenerated to a normal "does ReMus work with UNKNOWN-Constraints" test.
	 * However, through possible future changes, circumstances, where the other
	 * case arises, could again occur. Therefore, I allow both cases here (case
	 * 1: ReMUS finds c10, c11, c12 ; case2: ReMus finds c10, c11).
	 */
	@Test
	public void testReMusUnknownSet2() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnknownSet2(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(13);
		workingSet.flip(0, 13);
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), true, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
		solver.reset();

		boolean foundSpecialMus = false;
		for (final MusContainer container : muses) {
			System.out.println(container.getMus().toString());
			if (container.getMus().get(10) && container.getMus().get(11) && container.getMus().cardinality() == 2) {
				// don't check whether it is a MUS, since the solver cannot
				// confirm this MUS without constraint 12.
			} else {
				checkWhetherSetIsMus(container.getMus(), solver);
			}
			if (container.getMus().get(10) || container.getMus().get(11) || container.getMus().get(12)) {
				Assert.assertTrue((container.getMus().get(10) && container.getMus().get(11)
						&& container.getMus().get(12) && container.getMus().cardinality() == 3)
						|| (container.getMus().get(10) && container.getMus().get(11)
								&& container.getMus().cardinality() == 2));
				foundSpecialMus = true;
			}
		}
		Assert.assertTrue(foundSpecialMus);
		Assert.assertTrue(muses.size() == 16);
	}

	/**
	 * Example, that not all MUSes might be found anymore, if the solver can
	 * return LBool.UNKNOWN upon checkSat() call. (It does not find the MUS c10,
	 * c11)
	 */
	@Test
	public void testReMusUnknownSet3() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnknownSet3(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(12);
		workingSet.flip(0, 12);
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), true, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
		solver.reset();

		for (final MusContainer container : muses) {
			checkWhetherSetIsMus(container.getMus(), solver);
			Assert.assertTrue(!container.getMus().get(10) && !container.getMus().get(11));
		}
		Assert.assertTrue(muses.size() == 15);
	}

	@Test
	public void testReMusEmptySet() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnsatSet2(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(10);

		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();

		Assert.assertTrue(muses.size() == 0);
	}

	@Test(expected = SMTLIBException.class)
	public void testReMusWorkingSetTooBig() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnsatSet2(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(11);
		workingSet.set(11);
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		remus.enumerate();
	}

	@Test
	public void testReMusSet2WithTimeout() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnsatSet2(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(10);
		workingSet.flip(0, 10);

		final ReMus remus = new ReMus(solver, map, workingSet, handler, 1, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();

		Assert.assertTrue(muses.size() == 0 || muses.size() == 1 || muses.size() == 2);
		Assert.assertFalse(remus.hasNext());
	}

	@Test
	public void testHeuristicSmallest01() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnsatSet2(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(10);
		workingSet.flip(0, 10);

		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();

		final Random rnd = new Random(1337);
		Assert.assertTrue(Heuristics.chooseSmallestMus(muses, rnd, handler).getMus().cardinality() == 2);
	}

	@Test
	public void testHeuristicSmallest02() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnsatSet5(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(10);
		workingSet.flip(0, 10);
		solver.pushRecLevel();
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
		solver.popRecLevel();

		final Random rnd = new Random(1337);
		Assert.assertTrue(Heuristics.chooseSmallestMus(muses, rnd, handler).getMus().cardinality() == 2);
	}

	@Test
	public void testHeuristicBiggest01() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnsatSet2(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(10);
		workingSet.flip(0, 10);
		solver.pushRecLevel();
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
		solver.popRecLevel();

		final Random rnd = new Random(1337);
		Assert.assertTrue(Heuristics.chooseBiggestMus(muses, rnd, handler).getMus().cardinality() == 3);
	}

	@Test
	public void testHeuristicBiggest02() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnsatSet5(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(10);
		workingSet.flip(0, 10);
		solver.pushRecLevel();
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
		solver.popRecLevel();

		final Random rnd = new Random(1337);
		Assert.assertTrue(Heuristics.chooseBiggestMus(muses, rnd, handler).getMus().cardinality() == 6);
	}

	@Test
	public void testHeuristicLowestLexOrder() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnsatSet2(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(10);
		workingSet.flip(0, 10);
		solver.pushRecLevel();
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
		solver.popRecLevel();

		final Random rnd = new Random(1337);
		final BitSet lowLexMus = Heuristics.chooseMusWithLowestLexicographicalOrder(muses, rnd, handler).getMus();
		for (int i = lowLexMus.nextSetBit(0); i >= 0; i = lowLexMus.nextSetBit(i + 1)) {
			Assert.assertTrue(i == 0 || i == 2 || i == 5);
		}
	}

	@Test
	public void testHeuristicHighestLexOrder() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnsatSet2(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(10);
		workingSet.flip(0, 10);
		solver.pushRecLevel();
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
		solver.popRecLevel();

		final Random rnd = new Random(1337);
		final BitSet highLexMus = Heuristics.chooseMusWithHighestLexicographicalOrder(muses, rnd, handler).getMus();
		for (int i = highLexMus.nextSetBit(0); i >= 0; i = highLexMus.nextSetBit(i + 1)) {
			Assert.assertTrue(i == 8 || i == 9);
		}
	}

	@Test
	public void testHeuristicShallowest() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnsatSet2(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(10);
		workingSet.flip(0, 10);
		solver.pushRecLevel();
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
		solver.popRecLevel();

		final Random rnd = new Random(1337);
		final BitSet shallowestMus = Heuristics.chooseShallowestMus(muses, rnd, handler).getMus();
		Assert.assertTrue(shallowestMus.get(0));
	}

	@Test
	public void testHeuristicDeepest() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnsatSet2(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(10);
		workingSet.flip(0, 10);
		solver.pushRecLevel();
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
		solver.popRecLevel();

		final Random rnd = new Random(1337);
		final BitSet deepestMus = Heuristics.chooseDeepestMus(muses, rnd, handler).getMus();
		Assert.assertTrue(deepestMus.get(8));
	}

	@Test
	public void testHeuristicNarrowest() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnsatSet2(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(10);
		workingSet.flip(0, 10);
		solver.pushRecLevel();
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
		solver.popRecLevel();

		final Random rnd = new Random(1337);
		final BitSet narrowestMus = Heuristics.chooseNarrowestMus(muses, rnd, handler).getMus();
		final int width = narrowestMus.length() - narrowestMus.nextSetBit(0);
		Assert.assertTrue(width == 2);
	}

	@Test
	public void testHeuristicWidest() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnsatSet2(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(10);
		workingSet.flip(0, 10);
		solver.pushRecLevel();
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
		solver.popRecLevel();

		final Random rnd = new Random(1337);
		final BitSet widestMus = Heuristics.chooseWidestMus(muses, rnd, handler).getMus();
		final int width = widestMus.length() - widestMus.nextSetBit(0);
		Assert.assertTrue(width == 10);
	}

	@Test
	public void testHeuristicSmallestAmongWide01() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		// We use set 4 here, because in set 2 the widest mus is also one of the
		// smallest.
		setupUnsatSet4(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(10);
		workingSet.flip(0, 10);
		solver.pushRecLevel();
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
		solver.pushRecLevel();

		final Random rnd = new Random(1337);
		final BitSet smallestAmongWidestMus = Heuristics.chooseSmallestAmongWideMuses(muses, 0.1, rnd, handler)
				.getMus();
		final int width = smallestAmongWidestMus.length() - smallestAmongWidestMus.nextSetBit(0);
		Assert.assertTrue(width == 9);
		Assert.assertTrue(smallestAmongWidestMus.cardinality() == 2);
	}

	@Test
	public void testHeuristicSmallestAmongWide02() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		// We use set 4 here, because in set 2 the widest mus is also one of the
		// smallest.
		setupUnsatSet4(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(10);
		workingSet.flip(0, 10);
		solver.pushRecLevel();
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
		solver.pushRecLevel();

		final Random rnd = new Random(1337);
		final BitSet smallestAmongWidestMus = Heuristics.chooseSmallestAmongWideMuses(muses, 0, rnd, handler).getMus();
		final int width = smallestAmongWidestMus.length() - smallestAmongWidestMus.nextSetBit(0);
		Assert.assertTrue(width == 10);
		Assert.assertTrue(smallestAmongWidestMus.cardinality() == 3);
	}

	@Test
	public void testHeuristicWidestAmongSmall01() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(new DefaultLogger(), handler);
		final Translator translator = new Translator();
		// We use set 4 here, because in set 2 the widest mus is also one of the
		// smallest.
		setupUnsatSet4(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(10);
		workingSet.flip(0, 10);
		solver.pushRecLevel();
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
		solver.popRecLevel();

		final Random rnd = new Random(1337);
		final BitSet widestAmongSmallestMus = Heuristics.chooseWidestAmongSmallMuses(muses, 0.5, rnd, handler).getMus();
		final int width = widestAmongSmallestMus.length() - widestAmongSmallestMus.nextSetBit(0);
		Assert.assertTrue(width == 10);
		Assert.assertTrue(widestAmongSmallestMus.cardinality() == 3);
	}

	@Test
	public void testHeuristicWidestAmongSmall02() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		// We use set 4 here, because in set 2 the widest mus is also one of the
		// smallest.
		setupUnsatSet4(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(10);
		workingSet.flip(0, 10);
		solver.pushRecLevel();
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
		solver.popRecLevel();

		final Random rnd = new Random(1337);
		final BitSet widestAmongSmallestMus = Heuristics.chooseWidestAmongSmallMuses(muses, 0.4, rnd, handler).getMus();
		final int width = widestAmongSmallestMus.length() - widestAmongSmallestMus.nextSetBit(0);
		Assert.assertTrue(width == 9);
		Assert.assertTrue(widestAmongSmallestMus.cardinality() == 2);
	}

	@Test
	public void testMusEnumerationScriptFirst() {
		final MusEnumerationScript script = setupMusEnumerationScript(Logics.AUFLIRA);
		script.setOption(MusOptions.INTERPOLATION_HEURISTIC, HeuristicsType.FIRST);
		script.setOption(SMTLIBConstants.RANDOM_SEED, 1337);
		script.setOption(MusOptions.LOG_ADDITIONAL_INFORMATION, true);
		script.setOption(MusOptions.ENUMERATION_TIMEOUT, 1000);

		script.push(1);
		setupUnsatSet5(script);
		Assert.assertTrue(LBool.UNSAT == script.checkSat());
		// Just make sure the internal asserts don't throw exceptions and the
		// log looks good, the interpolant makes no
		// sense
		final Term[] core = script.getUnsatCore();
		for (final Term term : core) {
			System.out.println(term.toString());
		}
		// Not ready yet, since getUnsatCore returns nonstandard unsat cores.
		// script.getInterpolants(core);
	}

	@Test
	public void testNumberOfDifferentStatements() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnsatSet5(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(10);
		workingSet.flip(0, 10);
		solver.pushRecLevel();
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
		solver.popRecLevel();

		int maxDifference = 0;
		int currentDifference = 0;
		for (final MusContainer container1 : muses) {
			for (final MusContainer container2 : muses) {
				currentDifference = Heuristics.numberOfDifferentStatements(container1, container2);
				if (currentDifference > maxDifference) {
					maxDifference = currentDifference;
				}
			}
		}
		Assert.assertTrue(maxDifference == 8);
	}

	@Test
	public void testHeuristicDifferentMusesWithRespectToStatements01() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnsatSet5(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(10);
		workingSet.flip(0, 10);
		solver.pushRecLevel();
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
		solver.popRecLevel();

		final Random rnd = new Random(1337);
		final ArrayList<MusContainer> differentMuses = Heuristics.chooseDifferentMusesWithRespectToStatements(muses, 13,
				rnd, handler);
		int maxDifference = Integer.MIN_VALUE;
		int minDifference = Integer.MAX_VALUE;
		int currentDifference;
		for (final MusContainer container1 : differentMuses) {
			for (final MusContainer container2 : differentMuses) {
				if (container1.equals(container2)) {
					continue;
				}
				currentDifference = Heuristics.numberOfDifferentStatements(container1, container2);
				if (maxDifference < currentDifference) {
					maxDifference = currentDifference;
				}
				if (minDifference > currentDifference) {
					minDifference = currentDifference;
				}
			}
		}
		Assert.assertTrue(maxDifference == 8);
		Assert.assertTrue(minDifference == 2);
	}

	@Test
	public void testHeuristicDifferentMusesWithRespectToStatements02() {
		final LogProxy logger = new DefaultLogger();
		final TimeoutHandler handler = new TimeoutHandler(null);
		final Script script = setupScript(Logics.AUFLIRA, handler, logger);
		final DPLLEngine engine = new DPLLEngine(logger, handler);
		final Translator translator = new Translator();
		setupUnsatSet5(script, translator, engine);

		final UnexploredMap map = new UnexploredMap(engine, translator);
		final ConstraintAdministrationSolver solver = new ConstraintAdministrationSolver(script, translator);
		final BitSet workingSet = new BitSet(10);
		workingSet.flip(0, 10);
		solver.pushRecLevel();
		final ReMus remus = new ReMus(solver, map, workingSet, handler, 0, new Random(1337), false, logger);
		final ArrayList<MusContainer> muses = remus.enumerate();
		solver.popRecLevel();

		final Random rnd = new Random(1337);
		final ArrayList<MusContainer> differentMuses = Heuristics.chooseDifferentMusesWithRespectToStatements(muses, 3,
				rnd, handler);
		int maxDifference = Integer.MIN_VALUE;
		int minDifference = Integer.MAX_VALUE;
		int currentDifference;
		for (final MusContainer container1 : differentMuses) {
			for (final MusContainer container2 : differentMuses) {
				if (container1.equals(container2)) {
					continue;
				}
				currentDifference = Heuristics.numberOfDifferentStatements(container1, container2);
				if (maxDifference < currentDifference) {
					maxDifference = currentDifference;
				}
				if (minDifference > currentDifference) {
					minDifference = currentDifference;
				}
			}
		}
		Assert.assertTrue(maxDifference == 7);
		Assert.assertTrue(minDifference == 5);
	}

	@Test
	public void testMusEnumerationScriptSet2() {
		final MusEnumerationScript script = setupMusEnumerationScript(Logics.AUFLIRA);
		script.setOption(MusOptions.INTERPOLATION_HEURISTIC, HeuristicsType.SMALLEST);
		script.setOption(SMTLIBConstants.RANDOM_SEED, 1337);
		script.setOption(MusOptions.LOG_ADDITIONAL_INFORMATION, true);

		script.push(1);
		setupUnsatSet2(script);
		Assert.assertTrue(LBool.UNSAT == script.checkSat());
		final Term[] core1 = script.getUnsatCore();
		Assert.assertTrue(core1.length == 2);
		script.pop(1);

		setupUnsatSet2(script);
		// By setting the seed we reset the internal Random instance
		script.setOption(SMTLIBConstants.RANDOM_SEED, 1337);
		Assert.assertTrue(LBool.UNSAT == script.checkSat());
		final Term[] core2 = script.getUnsatCore();
		Assert.assertTrue(core1[0].toString().equals(core2[0].toString()));
		Assert.assertTrue(core1[1].toString().equals(core2[1].toString()));

		script.setOption(MusOptions.INTERPOLATION_HEURISTIC, HeuristicsType.BIGGEST);
		final Term[] core3 = script.getUnsatCore();
		Assert.assertTrue(!core1.equals(core3));
		Assert.assertTrue(core3.length == 3);
	}

	@Test
	public void testMusEnumerationScriptSet2WithUnnamedTerms1() {
		final MusEnumerationScript script = setupMusEnumerationScript(Logics.AUFLIRA);
		script.setOption(MusOptions.INTERPOLATION_HEURISTIC, HeuristicsType.SMALLEST);
		script.setOption(SMTLIBConstants.RANDOM_SEED, 1337);
		script.setOption(MusOptions.LOG_ADDITIONAL_INFORMATION, true);

		script.push(1);
		setupUnsatSet2WithUnnamedTerms1(script);
		Assert.assertTrue(LBool.UNSAT == script.checkSat());
		final Term[] core1 = script.getUnsatCore();
		Assert.assertTrue(core1.length == 1);
		script.pop(1);

		setupUnsatSet2WithUnnamedTerms1(script);
		// By setting the seed we reset the internal Random instance
		script.setOption(SMTLIBConstants.RANDOM_SEED, 1337);
		Assert.assertTrue(LBool.UNSAT == script.checkSat());
		final Term[] core2 = script.getUnsatCore();
		Assert.assertTrue(core2.length == 1);
		Assert.assertTrue(core1[0].toString().equals(core2[0].toString()));

		script.setOption(MusOptions.INTERPOLATION_HEURISTIC, HeuristicsType.BIGGEST);
		final Term[] core3 = script.getUnsatCore();
		Assert.assertTrue(!core1.equals(core3));
		Assert.assertTrue(core3.length == 2);
	}

	@Test
	public void testMusEnumerationScriptSet2WithUnnamedTerms2() {
		final MusEnumerationScript script = setupMusEnumerationScript(Logics.AUFLIRA);
		script.setOption(MusOptions.INTERPOLATION_HEURISTIC, HeuristicsType.SMALLEST);
		script.setOption(SMTLIBConstants.RANDOM_SEED, 1337);
		script.setOption(MusOptions.LOG_ADDITIONAL_INFORMATION, true);

		script.push(1);
		setupUnsatSet2WithUnnamedTerms2(script);
		Assert.assertTrue(LBool.UNSAT == script.checkSat());
		final Term[] core1 = script.getUnsatCore();
		Assert.assertTrue(core1.length == 2);
		script.pop(1);

		setupUnsatSet2WithUnnamedTerms2(script);
		// By setting the seed we reset the internal Random instance
		script.setOption(SMTLIBConstants.RANDOM_SEED, 1337);
		Assert.assertTrue(LBool.UNSAT == script.checkSat());
		final Term[] core2 = script.getUnsatCore();
		Assert.assertTrue(core1[0].toString().equals(core2[0].toString()));
		Assert.assertTrue(core1[1].toString().equals(core2[1].toString()));

		script.setOption(MusOptions.INTERPOLATION_HEURISTIC, HeuristicsType.BIGGEST);
		final Term[] core3 = script.getUnsatCore();
		Assert.assertTrue(!core1.equals(core3));
		Assert.assertTrue(core3.length == 2);
	}

	@Test
	public void testMusEnumerationScriptSet5() {
		final MusEnumerationScript script = setupMusEnumerationScript(Logics.AUFLIRA);
		script.setOption(MusOptions.INTERPOLATION_HEURISTIC, HeuristicsType.SMALLEST);
		script.setOption(SMTLIBConstants.RANDOM_SEED, 1337);
		script.setOption(MusOptions.LOG_ADDITIONAL_INFORMATION, true);

		script.push(1);
		setupUnsatSet5(script);
		Assert.assertTrue(LBool.UNSAT == script.checkSat());
		final Term[] core1 = script.getUnsatCore();
		Assert.assertTrue(core1.length == 2);
		script.pop(1);

		setupUnsatSet5(script);
		// By setting the seed we reset the internal Random instance
		script.setOption(SMTLIBConstants.RANDOM_SEED, 1337);
		Assert.assertTrue(LBool.UNSAT == script.checkSat());
		final Term[] core2 = script.getUnsatCore();
		Assert.assertTrue(core1[0].toString().equals(core2[0].toString()));
		Assert.assertTrue(core1[1].toString().equals(core2[1].toString()));

		script.setOption(MusOptions.INTERPOLATION_HEURISTIC, HeuristicsType.BIGGEST);
		final Term[] core3 = script.getUnsatCore();
		Assert.assertTrue(!core1.equals(core3));
		Assert.assertTrue(core3.length == 6);
	}

	@Test
	public void testMusEnumerationScriptUnknownSet1() {
		final MusEnumerationScript script = setupMusEnumerationScript(Logics.AUFLIRA);
		script.setOption(MusOptions.INTERPOLATION_HEURISTIC, HeuristicsType.BIGGEST);
		script.setOption(SMTLIBConstants.RANDOM_SEED, 1337);
		script.setOption(MusOptions.LOG_ADDITIONAL_INFORMATION, true);
		script.setOption(MusOptions.UNKNOWN_ALLOWED, true);

		script.push(1);
		setupUnknownSet(script);
		Assert.assertTrue(LBool.UNSAT == script.checkSat());

		final Term[] core = script.getUnsatCore();
		// The solver should still be able to find the biggest MUS and
		// determine, that it is unsat even without the
		// UNKNOWN constraint (therefore, it should not be "polluted" with the
		// UNKNOWN constraint), as you should be
		// able to see in testReMusUnknownSet02.
		Assert.assertTrue(core.length == 6);
		for (final Term c : core) {
			Assert.assertFalse(Translator.getName(c).equals("c10"));
		}
		// Enable as soon as unsat core of MUSEnumeration script is according to
		// the standard.
		// script.getInterpolants(core);
	}

	/**
	 * Example for wrong unsat core, if constraint in unsat core is not named.
	 */
	@Test
	public void testMusEnumerationScriptNoMusEnumerated() {
		final MusEnumerationScript script = setupMusEnumerationScript(Logics.AUFLIRA);
		script.setOption(MusOptions.INTERPOLATION_HEURISTIC, HeuristicsType.BIGGEST);
		script.setOption(SMTLIBConstants.RANDOM_SEED, 1337);
		script.setOption(MusOptions.LOG_ADDITIONAL_INFORMATION, true);
		script.setOption(MusOptions.ENUMERATION_TIMEOUT, 1);

		setupUnsatSet2(script);
		Assert.assertTrue(LBool.UNSAT == script.checkSat());
		final Term[] core = script.getUnsatCore();
		for (final Term term : core) {
			System.out.println(term.toString());
		}
		// This interpolant makes no sense and is only for testing.
		script.getInterpolants(core);
	}
}
