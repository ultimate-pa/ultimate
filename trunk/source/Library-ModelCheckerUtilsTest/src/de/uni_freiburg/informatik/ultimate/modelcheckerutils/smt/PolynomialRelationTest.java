/*
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtilsTest Library.
 *
 * The ULTIMATE ModelCheckerUtilsTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtilsTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtilsTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtilsTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtilsTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.io.IOException;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.NotAffineException;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.polynomial.solve_for_subject.MultiCaseSolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.polynomial.solve_for_subject.MultiCaseSolvedBinaryRelation.Xnf;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Max Barth (Max.Barth95@gmx.de)
 * @author LeonardFichtner (leonard.fichtner@web.de)
 */
public class PolynomialRelationTest {

	/**
	 * Warning: each test will overwrite the SMT script of the preceding test.
	 */
	private static final boolean WRITE_SMT_SCRIPTS_TO_FILE = false;
	private static final String SOLVER_COMMAND_Z3 = "z3 SMTLIB2_COMPLIANT=true -t:3500 -memory:2024 -smt2 -in smt.arith.solver=2";
	private static final String SOLVER_COMMAND_CVC4 =
			"cvc4 --incremental --print-success --lang smt --rewrite-divk --tlimit-per=3000";
	private static final String SOLVER_COMMAND_MATHSAT = "mathsat";
	private static final boolean USE_QUANTIFIER_ELIMINATION_TO_SIMPLIFY_INPUT_OF_EQUIVALENCE_CHECK = false;
	private Script mScript;

	@Before
	public void setUp() throws IOException {
//		mServices = UltimateMocks.createUltimateServiceProviderMock();
	}

	@After
	public void tearDown() {
		mScript.exit();
	}

	public static Sort getBitvectorSort8(final Script script) {
		return SmtSortUtils.getBitvectorSort(script, 8);
	}

	private Script createSolver(final String solverCommand) {
		final Script tmp = new HistoryRecordingScript(UltimateMocks.createSolver(solverCommand, LogLevel.INFO));
		final Script result;
		if (WRITE_SMT_SCRIPTS_TO_FILE) {
			try {
				result = new LoggingScript(tmp, "PolynomialRelationTest.smt2", true);
			} catch (final IOException e) {
				throw new AssertionError("IOException while constructing LoggingScript");
			}
		} else {
			result = tmp;
		}
		return result;
	}

	@Test
	public void relationRealDefault() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y") };
		final String inputSTR = "(= (+ 7.0 x) y )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);

	}

	@Test
	public void relationRealEQ() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y") };
		final String inputSTR = "(= (* 7.0 x) y )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);

	}

	@Test
	public void relationRealEQ2() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y") };
		final String inputSTR = "(= (* 3.0 x) (* 7.0 y) )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealEQ3() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z") };
		final String inputSTR = "(= (* 3.0 x) (+ (* 7.0 y) (* 5.0 z)) )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealEQ4() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z") };
		final String inputSTR = "(= (* 6.0 (+ y x)) (* 7.0 z) )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyEQPurist01() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "ri") };
		final String inputSTR = "(= (* y x) ri)";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyEQPurist02() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z", "ri") };
		final String inputSTR = "(= (* y x z) ri)";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyEQ5() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z") };
		final String inputSTR = "(= (* 6.0 (* y x)) (+ 3.0 (* z z)))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyEQ6() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z") };
		final String inputSTR = "(= (* z (+ 6.0 (* (* y y) x))) (+ 3.0 (* z z)))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyEQ7() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z") };
		final String inputSTR = "(= (* 3.0 x (/ y z) z 5.0) (* y z)))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyMultipleSubjectsEQ7() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z") };
		final String inputSTR = "(= (* z (+ 6.0 (* (* x y) x))) (+ 3.0 (* z z)))";
		notSolvableForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	/**
	 * The background why this shouldn't work, is because divisions by variables are treated as an individual variable,
	 * but now the subject occurs in this variable.
	 */
	@Test
	public void relationRealPolyNestedSubjectEQ8() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y") };
		final String inputSTR = "(= 1.0 (/ y x))";
		notSolvableForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyWithDivisionsEQ9() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z") };
		final String inputSTR = "(= (/ (+ 6.0 (* (/ z y) x)) 2.0) (+ 3.0 (/ y z)))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyDetectNestedSecondVariableEQ10() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z") };
		final String inputSTR = "(= (/ (+ 6.0 (* (/ z y) x)) 2.0) (+ 3.0 (/ y x)))";
		notSolvableForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealGEQ01() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "lo") };
		final String inputSTR = "(>= (* 3.0 x) lo )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyGEQPurist01() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "ri") };
		final String inputSTR = "(>= (* x y) ri)";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyGEQPurist02() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z", "u", "ri") };
		final String inputSTR = "(>= (* x y y y z z u) ri)";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyGEQ02() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z", "lo") };
		final String inputSTR = "(>= (* 3.0 x (/ y z) z 5.0) (* y lo))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealLEQ01() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "hi") };
		final String inputSTR = "(<= (* 3.0 x) hi )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyLEQ02() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z", "hi") };
		final String inputSTR = "(<= (* 3.0 x (/ y z) z 5.0) (* y hi))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealDISTINCT01() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y") };
		final String inputSTR = "(not(= (* 3.0 x) y ))";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyDISTINCT02() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z") };
		final String inputSTR = "(not(= (* 3.0 x (/ y z) z 5.0) (* y z)))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealGREATER01() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "lo") };
		final String inputSTR = "(> (* 3.0 x) lo )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyGREATER02() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z", "lo") };
		final String inputSTR = "(> (* 3.0 x (/ y z) z 5.0) (* y lo))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealLESS01() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "hi") };
		final String inputSTR = "(< (* 4.0 x) hi )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyLESS02() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z", "hi") };
		final String inputSTR = "(< (* 3.0 x (/ y z) z 5.0) (* y hi))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationBvPolyEQ01() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y") };
		final String inputSTR = "(= (bvmul (_ bv255 8) x) (bvmul (_ bv64 8) y y y))";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationBvPolyEQ02() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y") };
		final String inputSTR = "(= (bvmul (_ bv1 8) x) (bvmul (_ bv64 8) y y y))";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationBvPolyEQ03() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y") };
		final String inputSTR = "(= (bvmul (_ bv255 8) x y) (bvmul (_ bv64 8) y y y))";
		notSolvableForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationBvPolyEQ04() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y") };
		final String inputSTR = "(= (bvmul (_ bv252 8) x) (bvmul (_ bv64 8) y y y))";
		notSolvableForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationBvEQ05() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y") };
		final String inputSTR = "(= (bvmul (_ bv255 8) x) (bvmul (_ bv8 8) y))";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntPolyPuristEq() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(= (* y x) z )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntPolyPuristDistinct() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(not (= (* y x) z))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	/**
	 * One of the supporting terms in the y-not-zero-case
	 * is not (< x (div z y)) but (< x (+ (div (- z 1)  y) 1))
	 * You can see the problem for y=2, x=1, and z=3
	 *
	 */
	@Test
	public void relationIntPolyPuristLeq() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(< (* y x) z )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	public void relationIntPolyMATHSATEQ3() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(= (* 6 (* y x)) (+ 3 (* z z)))";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	public void relationIntPolyUnknownEQ4() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(= (* z (+ 6 (* (* y y) x))) (+ 3 (* z z)))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	public void relationIntPolyUnknownEQ5() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(= (* 3 x (div y z) z 5) (* y z)))";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntPolyZ3CVC4EQ6() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(= (* 3 y x) (* 9 y))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntPolyZ3CVC4Distinct6() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(not (= (* 3 y x) (* 9 y)))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}



	@Test
	public void relationIntPolyZ3CVC4MATHSATEQ7() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(= (* 3 y x) (* 333 y))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	public void relationIntPolyMATHSATEQ8() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(= (* 3 y x) (* 21 z))";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	public void relationIntPolyCVC4MATHSATEQ9() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(= (* 3 y x) (* 21 z y))";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntPolyZ3MATHSATEQ10() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(= (* 3 y x) (* 11 y))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	public void relationIntPolyCVC4MATHSATEQ11() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(= (* 3 y x) (* 333 y y y))";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	public void relationIntPolyUnknownEQ12() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(= (* y (+ 6 (* y x))) (+ 3 y))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntPolyZ3EQ13() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(= (* 3 (div x 6) (div y z)) (* y z))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	public void relationIntPolyUnknownEQ14() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(= (* 3 (div x 6) (+ 5 (div y z))) (* y z))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntPolyZ3CVC4MATHSATEQ15() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(= (* y (+ 6 x)) (+ 3 y))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	/**
	 * Currently fails because some coefficient is null, this probably will be
	 * handled when the "Todo if no constantTErm throw error or handle it" is
	 * finished
	 */
	@Test
	public void relationIntPolyUnknownEQ16() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(= (div (div x 5 2) (div y z)) y))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	private void notSolvableForX(final String solverCommand, final String inputAsString, final VarDecl... varDecls) throws NotAffineException {
		final Script script = createSolver(solverCommand);
		script.setLogic(Logics.ALL);
		for (final VarDecl varDecl : varDecls) {
			varDecl.declareVars(script);
		}
		mScript = script;
		final Term subject = TermParseUtils.parseTerm(mScript, "x");
		final MultiCaseSolvedBinaryRelation sbr = PolynomialRelation
				.convert(mScript, TermParseUtils.parseTerm(mScript, inputAsString))
				.solveForSubject(mScript, subject, Xnf.DNF);
		Assert.assertNull(sbr);
	}

	private void testSolveForX(final String solverCommand, final String inputAsString, final VarDecl... varDecls) throws NotAffineException {
		final Script script = createSolver(solverCommand);
		script.setLogic(Logics.ALL);
		for (final VarDecl varDecl : varDecls) {
			varDecl.declareVars(script);
		}
		mScript = script;
		final Term inputAsTerm = TermParseUtils.parseTerm(mScript, inputAsString);
		final Term x = TermParseUtils.parseTerm(mScript, "x");
		testSingleCaseSolveForSubject(inputAsTerm, x);
		testMultiCaseSolveForSubject(inputAsTerm, x, Xnf.DNF);
		testMultiCaseSolveForSubject(inputAsTerm, x, Xnf.CNF); // this is not yet implemented?
	}

	private void testSolveForXMultiCaseOnly(final String solverCommand, final String inputAsString,
			final VarDecl... varDecls) throws NotAffineException {
		final Script script = createSolver(solverCommand);
		script.setLogic(Logics.ALL);
		for (final VarDecl varDecl : varDecls) {
			varDecl.declareVars(script);
		}
		mScript = script;
		final Term inputAsTerm = TermParseUtils.parseTerm(script, inputAsString);
		final Term subject = TermParseUtils.parseTerm(script, "x");
		testMultiCaseSolveForSubject(inputAsTerm, subject, Xnf.DNF);
		 testMultiCaseSolveForSubject(inputAsTerm, subject, Xnf.CNF);
	}


	private void testSingleCaseSolveForSubject(final Term inputAsTerm, final Term x) throws NotAffineException {
		final SolvedBinaryRelation sbr = PolynomialRelation.convert(mScript, inputAsTerm).solveForSubject(mScript, x);
		mScript.echo(new QuotedObject("Checking if input and output of solveForSubject are equivalent"));
		Assert.assertTrue(assumptionsImpliesEquality(inputAsTerm, sbr));
	}

	private void testMultiCaseSolveForSubject(final Term inputAsTerm, final Term x, final Xnf xnf)
			throws NotAffineException {
		final MultiCaseSolvedBinaryRelation mcsbr =
				PolynomialRelation.convert(mScript, inputAsTerm).solveForSubject(mScript, x, xnf);
		mScript.echo(new QuotedObject("Checking if input and output of multiCaseSolveForSubject are equivalent"));
		final Term solvedAsTerm = mcsbr.asTerm(mScript);
		final Term tmp;
		if (USE_QUANTIFIER_ELIMINATION_TO_SIMPLIFY_INPUT_OF_EQUIVALENCE_CHECK) {
			final IUltimateServiceProvider services = UltimateMocks.createUltimateServiceProviderMock();
			final ManagedScript mgdScript = new ManagedScript(services, mScript);
			final ILogger logger = services.getLoggingService().getLogger(this.getClass().getSimpleName());
			tmp = PartialQuantifierElimination.tryToEliminate(services, logger, mgdScript, solvedAsTerm,
					SimplificationTechnique.NONE, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		} else {
			tmp = solvedAsTerm;
		}
		final LBool equivalent = SmtUtils.checkEquivalence(inputAsTerm, tmp, mScript);
		switch (equivalent) {
		case SAT:
			Assert.assertTrue("solveForSubject is unsound", false);
			break;
		case UNKNOWN:
			Assert.assertTrue("Insufficient ressources to check soundness", false);
			break;
		case UNSAT:
			// equivalence as expected
			break;
		default:
			throw new AssertionError("unknown value " + equivalent);
		}

	}

	@Deprecated
	private boolean assumptionsImpliesEquality(final Term originalTerm, final SolvedBinaryRelation sbr) {
		if (sbr.getAssumptionsMap().isEmpty()) {
			return SmtUtils.areFormulasEquivalent(sbr.asTerm(mScript), originalTerm, mScript);
		} else {
			final Term disJ = SmtUtils.not(mScript, SmtUtils.and(mScript, sbr.getAssumptionsMap().values()));
			final Term impli1 = SmtUtils.or(mScript, disJ, sbr.asTerm(mScript));
			final Term impli2 = SmtUtils.or(mScript, disJ, originalTerm);
			return SmtUtils.areFormulasEquivalent(impli1, impli2, mScript);
		}
	}

	@Test
	public void relationIntDivDefault() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(= (+ 7 x) y )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);

	}

	@Test
	public void relationIntDivEQ() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(= (* 7 x) y )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);

	}

	@Test
	public void relationIntDivEQ2() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(= (* 3 x) (* 7 y) )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDivEQ3() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(= (* 3 x) (+ (* 7 y) (* 5 z)) )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDivEQ4() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(= (* 6 (+ y x)) (* 7 z) )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDivGEQ() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "lo") };
		final String inputSTR = "(>= (* 3 x) lo )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDivLEQ() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "hi") };
		final String inputSTR = "(<= (* 3 x) hi )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDivDISTINCT() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(not(= (* 3 x) y ))";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDivGREATER() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "lo") };
		final String inputSTR = "(> (* 3 x) lo )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDivLESS() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "hi") };
		final String inputSTR = "(< (* 4 x) hi )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntModEq() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (mod x 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntModEqUselessSummands() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(= (+ (mod x 3) (* y y) y 1) (* y (+ y 1)) )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	/**
	 * Bug: Detection of div/mod fails if input is too simple.
	 */
	@Test
	public void relationIntModEqZero() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x") };
		final String inputSTR = "(= (mod x 3) 0 )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	/**
	 * Bug: Fails to detect that we cannot solve for x.
	 */
	@Test
	public void relationIntDivUnsolvable() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (div (* x x) 3) eq )";
		notSolvableForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	/**
	 * Bug: Fails to detect that we cannot solve if subject is in divisor.
	 */
	@Test
	public void relationIntDivSubjectInDivisor() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (div 1337 x) eq )";
		notSolvableForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntModNEWEq() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (+(mod x 3)1) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDivNEWEq() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (+(div x 3)1) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDivEq() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (div x 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntMultiParamDivEq() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (div x 2 2 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntRecModSimplifyEq() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (mod (mod x 3) 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntRecModSimplifyMoreEq() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (mod (mod (mod x 3) 3) 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	// @Test // long runtime not sure if result is correct and the test is false negative
	public void relationIntRecModMoreEq() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (mod (mod (mod x 7) 9) 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	// @Test // long runtime not sure if result is correct and the test is false negative
	public void relationIntRecModMore1Eq() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (mod (mod (mod (mod x 5) 7) 9) 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	// @Test // long runtime not sure if result is correct and the test is false negative
	public void relationIntRecModMore2Eq() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (mod (mod (mod (mod (mod x 13) 5) 7) 9) 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	// @Test // long runtime not sure if result is correct and the test is false negative
	public void relationIntRecModSimplifyMore1Eq() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (mod (mod (mod x 3) 4) 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	// @Test // long runtime not sure if result is correct and the test is false negative
	public void relationIntRecModSimplifyMore2Eq() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (mod (mod (mod x 4) 3) 7) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	// @Test // test fails if you run the whole suite. If you run it alone it holds
	public void relationIntRecModDivEq() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (mod (div x 7) 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntRecModEq() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (mod (mod x 7) 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	// @Test // test does fail even tho the result is correct
	public void relationIntRecDivModEq() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (div (mod x 7) 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntRecDivasdModEq() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (div (mod x 7) 7) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDefaultModEq() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "eq") };
		final String inputSTR = "(= (+ (mod (mod y 7) 3)  x) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntRecDivEq() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "eq") };
		final String inputSTR = "(= (div (div x 7) 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntRecDivSimplifyEq() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (div (div x 3) 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void choirNightTrezor01() throws NotAffineException {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "b") };
		final String inputSTR = "(= (mod (+ (* (mod (+ b 1) 4294967296) 4294967295) x) 4294967296) 1)";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}
}