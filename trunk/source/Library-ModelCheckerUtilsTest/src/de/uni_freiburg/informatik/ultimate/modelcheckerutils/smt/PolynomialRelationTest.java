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
import java.util.Collections;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.MultiCaseSolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.MultiCaseSolvedBinaryRelation.Xnf;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.LoggingScriptForMainTrackBenchmarks;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Max Barth (Max.Barth95@gmx.de)
 * @author LeonardFichtner (leonard.fichtner@web.de)
 */
public class PolynomialRelationTest {

	private static final boolean WRITE_SMT_SCRIPTS_TO_FILE = false;
	private static final boolean WRITE_MAIN_TRACK_SCRIPT_IF_UNKNOWN_TO_FILE = false;

	private static final String SOLVER_COMMAND_Z3 =
			"z3 SMTLIB2_COMPLIANT=true -t:6000 -memory:2024 -smt2 -in smt.arith.solver=2";
	private static final String SOLVER_COMMAND_CVC4 = "cvc4 --incremental --print-success --lang smt --tlimit-per=6000";
	private static final String SOLVER_COMMAND_MATHSAT = "mathsat";
	/**
	 * If DEFAULT_SOLVER_COMMAND is not null we ignore the solver specified for each test and use only the solver
	 * specified here. This can be useful to check if there is a suitable solver for all tests and this can be useful
	 * for generating difficult SMT-LIB benchmarks.
	 */
	private static final String DEFAULT_SOLVER_COMMAND = null;

	private static final boolean USE_QUANTIFIER_ELIMINATION_TO_SIMPLIFY_INPUT_OF_EQUIVALENCE_CHECK = false;
	private Script mScript;

	@Before
	public void setUp() throws IOException {
		// mServices = UltimateMocks.createUltimateServiceProviderMock();
	}

	@After
	public void tearDown() {
		mScript.exit();
	}

	public static Sort getBitvectorSort8(final Script script) {
		return SmtSortUtils.getBitvectorSort(script, 8);
	}

	private Script createSolver(final String proviededSolverCommand) {
		String effectiveSolveCommand;
		if (DEFAULT_SOLVER_COMMAND != null) {
			effectiveSolveCommand = DEFAULT_SOLVER_COMMAND;
		} else {
			effectiveSolveCommand = proviededSolverCommand;
		}
		Script result = new HistoryRecordingScript(UltimateMocks.createSolver(effectiveSolveCommand, LogLevel.INFO));
		final String testName = ReflectionUtil.getCallerMethodName(4);
		if (WRITE_SMT_SCRIPTS_TO_FILE) {
			try {
				final String filename = testName + ".smt2";
				result = new LoggingScript(result, filename, true);
			} catch (final IOException e) {
				throw new AssertionError("IOException while constructing LoggingScript");
			}
		}
		if (WRITE_MAIN_TRACK_SCRIPT_IF_UNKNOWN_TO_FILE) {
			final String baseFilename = testName;
			result = new LoggingScriptForMainTrackBenchmarks(result, baseFilename, ".");
		}
		return result;
	}

	@Test
	public void relationRealDefault() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y") };
		final String inputSTR = "(= (+ 7.0 x) y )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealEQ() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y") };
		final String inputSTR = "(= (* 7.0 x) y )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealEQ2() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y") };
		final String inputSTR = "(= (* 3.0 x) (* 7.0 y) )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealEQ3() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z") };
		final String inputSTR = "(= (* 3.0 x) (+ (* 7.0 y) (* 5.0 z)) )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealEQ4() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z") };
		final String inputSTR = "(= (* 6.0 (+ y x)) (* 7.0 z) )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyEQPurist01() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "ri") };
		final String inputSTR = "(= (* y x) ri)";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyEQPurist02() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z", "ri") };
		final String inputSTR = "(= (* y x z) ri)";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyEQ5() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z") };
		final String inputSTR = "(= (* 6.0 (* y x)) (+ 3.0 (* z z)))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyEQ6() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z") };
		final String inputSTR = "(= (* z (+ 6.0 (* (* y y) x))) (+ 3.0 (* z z)))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_MATHSAT, inputSTR, vars);
	}

	@Test
	public void relationRealPolyEQ7() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z") };
		final String inputSTR = "(= (* 3.0 x (/ y z) z 5.0) (* y z)))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyMultipleSubjectsEQ7() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z") };
		final String inputSTR = "(= (* z (+ 6.0 (* (* x y) x))) (+ 3.0 (* z z)))";
		notSolvableForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	/**
	 * The background why this shouldn't work, is because divisions by variables are treated as an individual variable,
	 * but now the subject occurs in this variable.
	 */
	@Test
	public void relationRealPolyNestedSubjectEQ8() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y") };
		final String inputSTR = "(= 1.0 (/ y x))";
		notSolvableForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyWithDivisionsEQ9() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z") };
		final String inputSTR = "(= (/ (+ 6.0 (* (/ z y) x)) 2.0) (+ 3.0 (/ y z)))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyDetectNestedSecondVariableEQ10() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z") };
		final String inputSTR = "(= (/ (+ 6.0 (* (/ z y) x)) 2.0) (+ 3.0 (/ y x)))";
		notSolvableForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealGEQ01() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "lo") };
		final String inputSTR = "(>= (* 3.0 x) lo )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyGEQPurist01() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "ri") };
		final String inputSTR = "(>= (* x y) ri)";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyGEQPurist02() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z", "u", "ri") };
		final String inputSTR = "(>= (* x y y y z z u) ri)";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyGEQ02() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z", "lo") };
		final String inputSTR = "(>= (* 3.0 x (/ y z) z 5.0) (* y lo))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealLEQ01() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "hi") };
		final String inputSTR = "(<= (* 3.0 x) hi )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyLEQ02() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z", "hi") };
		final String inputSTR = "(<= (* 3.0 x (/ y z) z 5.0) (* y hi))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealDISTINCT01() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y") };
		final String inputSTR = "(not(= (* 3.0 x) y ))";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyDISTINCT02() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z") };
		final String inputSTR = "(not(= (* 3.0 x (/ y z) z 5.0) (* y z)))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealGREATER01() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "lo") };
		final String inputSTR = "(> (* 3.0 x) lo )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyGREATER02() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z", "lo") };
		final String inputSTR = "(> (* 3.0 x (/ y z) z 5.0) (* y lo))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealLESS01() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "hi") };
		final String inputSTR = "(< (* 4.0 x) hi )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationRealPolyLESS02() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getRealSort, "x", "y", "z", "hi") };
		final String inputSTR = "(< (* 3.0 x (/ y z) z 5.0) (* y hi))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationBvPolyEQ01() {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y") };
		final String inputSTR = "(= (bvmul (_ bv255 8) x) (bvmul (_ bv64 8) y y y))";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationBvPolyEQ02() {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y") };
		final String inputSTR = "(= (bvmul (_ bv1 8) x) (bvmul (_ bv64 8) y y y))";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationBvPolyEQ03() {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y") };
		final String inputSTR = "(= (bvmul (_ bv255 8) x y) (bvmul (_ bv64 8) y y y))";
		notSolvableForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationBvPolyEQ04() {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y") };
		final String inputSTR = "(= (bvmul (_ bv252 8) x) (bvmul (_ bv64 8) y y y))";
		notSolvableForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationBvEQ05() {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y") };
		final String inputSTR = "(= (bvmul (_ bv255 8) x) (bvmul (_ bv8 8) y))";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	/**
	 * The mapping {x->2, y->6} is a satisfying assignment because 2*2=4 and 2*6=4 because we have to take everything
	 * modulo 8. If we would divide both sides by 2 this mapping is not a satisfying assignment any more.
	 */
	@Test
	public void relationBvEQ06NoDiv() {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y") };
		final String inputSTR = "(= (bvmul (_ bv2 8) x) (bvmul (_ bv2 8) y ))";
		notSolvableForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	// Result in DNF: (or (and (= y 0) (= z 0)) (and (= (mod z y) 0) (not (= y 0)) (= x (div z y))))
	// @Test Insufficient resources to check soundness
	public void relationIntPolyPuristEq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(= (* y x) z )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_MATHSAT, inputSTR, vars);
	}

	// Result in DNF: (or (and (distinct x (div z y)) (not (= y 0))) (and (not (= y 0)) (not (= (mod z y) 0))) (and (not
	// (= z 0)) (= y 0)))
	// Result in CNF: (and (or (not (= z 0)) (not (= y 0))) (or (= y 0) (distinct x (div z y)) (not (= (mod z y) 0))))
	// @Test Commented because mathsat does not terminate
	public void relationIntPolyPuristDistinct() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(not (= (* y x) z))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_MATHSAT, inputSTR, vars);
	}

	/**
	 * One of the supporting terms in the y-not-zero-case is not (< x (div z y)) but (< x (+ (div (- z 1) y) 1)) You can
	 * see the problem for y=2, x=1, and z=3
	 *
	 */
	// @Test Insufficient resources to check soundness
	public void relationIntPolyPuristLeq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(< (* y x) z )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	/**
	 * Disjuncts of the DNF result: (and (= x (div (div t 2) a)) (not (= a 0)) (= (mod t 2) 0) (= (mod (div t 2) a) 0))
	 * (and (= (mod t 2) 0) (= a 0) (= (div t 2) 0))
	 *
	 * You get the CNF result if you swap the and/or and negate all atoms of
	 * {@link PolynomialRelationTest#relationIntPolyDistinct}
	 */
	@Test
	public void relationIntPolyEq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "a", "t") };
		final String inputSTR = "(= (* 2 a x) t )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_MATHSAT, inputSTR, vars);
	}

	/**
	 * Disjuncts of the DNF result: (and (= x (distinct (div (div t 2) a))) (not (= a 0))) (and (= a 0) (not (= (div t
	 * 2) 0))) (and (not (= (mod (div t 2) a) 0)) (not (= a 0))) (and (not (= (mod t 2) 0)))
	 *
	 * You get the CNF result if you swap the and/or and negate all atoms of
	 * {@link PolynomialRelationTest#relationIntPolyEq}
	 */
	// @Test Insufficient resources to check soundness
	public void relationIntPolyDistinct() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "a", "t") };
		final String inputSTR = "(not (= (* 2 a x) t ))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	/**
	 * Delete after {@link PolynomialRelationTest#relationIntPolyDistinct} can be solved.
	 */
	@Test
	public void relationIntPolyDistinctSimplified() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "a", "t") };
		final String inputSTR = "(not (= (* 2 a x) 1337 ))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	// @Test Insufficient resources to check soundness
	public void relationIntPolyLess() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "a", "t") };
		final String inputSTR = "(< (* 2 a x) t )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	/**
	 * Delete after {@link PolynomialRelationTest#relationIntPolyDistinct} can be solved.
	 */
	@Test
	public void relationIntPolyLessSimplified() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "a", "t") };
		final String inputSTR = "(< (* 2 a x) 1337 )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_MATHSAT, inputSTR, vars);
	}

	// @Test Insufficient resources to check soundness
	public void relationIntPolyLeq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "a", "t") };
		final String inputSTR = "(<= (* 2 a x) t )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	/**
	 * Delete after {@link PolynomialRelationTest#relationIntPolyLeq} can be solved.
	 */
	@Test
	public void relationIntPolyLeqSimplified() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "a", "t") };
		final String inputSTR = "(<= (* 2 a x) 1337 )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_MATHSAT, inputSTR, vars);
	}

	@Test
	public void relationIntPolyGeq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "a", "t") };
		final String inputSTR = "(>= (* 2 a x) t )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_CVC4, inputSTR, vars);
	}

	@Test
	public void relationIntPolyGq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "a", "t") };
		final String inputSTR = "(> (* 2 a x) t )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_CVC4, inputSTR, vars);
	}

	@Test
	public void relationIntPolyEqRhsLiteral() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(= (* 17 y z x) 42 )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	// @Test Insufficient resources to check soundness
	public void relationIntPolyMATHSATEQ3() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(= (* 6 (* y x)) (+ 3 (* z z)))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	// @Test Insufficient resources to check soundness
	public void relationIntPolyUnknownEQ4() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(= (* z (+ 6 (* (* y y) x))) (+ 3 (* z z)))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	// @Test Insufficient resources to check soundness
	public void relationIntPolyUnknownEQ5() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(= (* 3 x (div y z) z 5) (* y z)))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntPolyZ3CVC4EQ6() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(= (* 3 y x) (* 9 y))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntPolyZ3CVC4Distinct6() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(not (= (* 3 y x) (* 9 y)))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntPolyZ3CVC4MATHSATEQ7() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(= (* 3 y x) (* 333 y))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntPolyMATHSATEQ8() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(= (* 3 y x) (* 21 z))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_MATHSAT, inputSTR, vars);
	}

	// @Test > 170h on Jenkins
	public void relationIntPolyCVC4MATHSATEQ9() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(= (* 3 y x) (* 21 z y))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_MATHSAT, inputSTR, vars);
	}

	@Test
	public void relationIntPolyZ3MATHSATEQ10() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(= (* 3 y x) (* 11 y))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	// @Test >8h on Jenkins although it runs fine on Matthias' maschine with the same mathsat
	public void relationIntPolyCVC4MATHSATEQ11() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(= (* 3 y x) (* 333 y y y))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_MATHSAT, inputSTR, vars);
	}

	// @Test Insufficient resources to check soundness
	public void relationIntPolyUnknownEQ12() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(= (* y (+ 6 (* y x))) (+ 3 y))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	// @Test Insufficient resources to check soundness
	public void relationIntPolyZ3EQ13() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(= (* 3 (div x 6) (div y z)) (* y z))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	// @Test Insufficient resources to check soundness
	public void relationIntPolyUnknownEQ14() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(= (* 3 (div x 6) (+ 5 (div y z))) (* y z))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntPolyZ3CVC4MATHSATEQ15() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(= (* y (+ 6 x)) (+ 3 y))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	/**
	 * Currently fails because some coefficient is null, this probably will be handled when the "Todo if no constantTErm
	 * throw error or handle it" is finished
	 */
	@Test
	public void relationIntPolyUnknownEQ16() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(= (div (div x 5 2) (div y z)) y))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	private void notSolvableForX(final String solverCommand, final String inputAsString, final VarDecl... varDecls) {
		final Script script = createSolver(solverCommand);
		script.setLogic(Logics.ALL);
		for (final VarDecl varDecl : varDecls) {
			varDecl.declareVars(script);
		}
		mScript = script;
		final Term subject = TermParseUtils.parseTerm(mScript, "x");
		final MultiCaseSolvedBinaryRelation sbr =
				PolynomialRelation.convert(mScript, TermParseUtils.parseTerm(mScript, inputAsString))
						.solveForSubject(mScript, subject, Xnf.DNF, Collections.emptySet());
		Assert.assertNull(sbr);
	}

	private void testSolveForX(final String solverCommand, final String inputAsString, final VarDecl... varDecls) {
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
			final VarDecl... varDecls) {
		final Script script = createSolver(solverCommand);
		script.setLogic(Logics.ALL);
		for (final VarDecl varDecl : varDecls) {
			varDecl.declareVars(script);
		}
		mScript = script;
		final Term inputAsTerm = TermParseUtils.parseTerm(script, inputAsString);
		final Term subject = TermParseUtils.parseTerm(script, "x");
		final SolvedBinaryRelation sbr =
				PolynomialRelation.convert(mScript, inputAsTerm).solveForSubject(mScript, subject);
		Assert.assertNull("Solvable, but unsolvable expected", sbr);
		testMultiCaseSolveForSubject(inputAsTerm, subject, Xnf.DNF);
		testMultiCaseSolveForSubject(inputAsTerm, subject, Xnf.CNF);
	}

	private void testSingleCaseSolveForSubject(final Term inputAsTerm, final Term x) {
		final SolvedBinaryRelation sbr = PolynomialRelation.convert(mScript, inputAsTerm).solveForSubject(mScript, x);
		mScript.echo(new QuotedObject("Checking if input and output of solveForSubject are equivalent"));
		Assert.assertTrue(SmtUtils.areFormulasEquivalent(sbr.asTerm(mScript), inputAsTerm, mScript));
	}

	private void testMultiCaseSolveForSubject(final Term inputAsTerm, final Term x, final Xnf xnf) {
		final MultiCaseSolvedBinaryRelation mcsbr = PolynomialRelation.convert(mScript, inputAsTerm)
				.solveForSubject(mScript, x, xnf, Collections.emptySet());
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
			Assert.assertTrue("Insufficient resources to check soundness", false);
			break;
		case UNSAT:
			// equivalence as expected
			break;
		default:
			throw new AssertionError("unknown value " + equivalent);
		}

	}

	@Test
	public void relationIntDivDefault() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(= (+ 7 x) y )";
		testSolveForX(SOLVER_COMMAND_Z3, inputSTR, vars);

	}

	@Test
	public void relationIntDivEQ() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(= (* 7 x) y )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);

	}

	@Test
	public void relationIntDivEQ2() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(= (* 3 x) (* 7 y) )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDivEQ3() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(= (* 3 x) (+ (* 7 y) (* 5 z)) )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDivEQ4() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(= (* 6 (+ y x)) (* 7 z) )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDivGEQ() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "lo") };
		final String inputSTR = "(>= (* 3 x) lo )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDivLEQ() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "hi") };
		final String inputSTR = "(<= (* 3 x) hi )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDivDISTINCT() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(not (= (* 3 x) y ))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDivGREATER() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "lo") };
		final String inputSTR = "(> (* 3 x) lo )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDivLESS() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "hi") };
		final String inputSTR = "(< (* 4 x) hi )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntModEq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (mod x 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntModEqUselessSummands() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(= (+ (mod x 3) (* y y) y 1) (* y (+ y 1)) )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_CVC4, inputSTR, vars);
	}

	/**
	 * Bug: Detection of div/mod fails if input is too simple.
	 */
	@Test
	public void relationIntModEqZero() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x") };
		final String inputSTR = "(= (mod x 3) 0 )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	/**
	 * Bug: Fails to detect that we cannot solve for x.
	 */
	@Test
	public void relationIntDivUnsolvable() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (div (* x x) 3) eq )";
		notSolvableForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	/**
	 * Bug: Fails to detect that we cannot solve if subject is in divisor.
	 */
	@Test
	public void relationIntDivSubjectInDivisor() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (div 1337 x) eq )";
		notSolvableForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntModNEWEq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (+(mod x 3)1) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDivNEWEq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (+(div x 3)1) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDivEq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (div x 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntMultiParamDivEq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (div x 2 2 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_CVC4, inputSTR, vars);
	}

	@Test
	public void relationIntRecModSimplifyEq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (mod (mod x 3) 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntRecModSimplifyMoreEq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (mod (mod (mod x 3) 3) 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntRecModMoreEq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (mod (mod (mod x 7) 9) 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntRecModMore1Eq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (mod (mod (mod (mod x 5) 7) 9) 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntRecModMore2Eq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (mod (mod (mod (mod (mod x 13) 5) 7) 9) 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntRecModSimplifyMore1Eq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (mod (mod (mod x 3) 4) 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntRecModSimplifyMore2Eq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (mod (mod (mod x 4) 3) 7) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntRecModDivEq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (mod (div x 7) 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntRecModEq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (mod (mod x 7) 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntRecDivModEq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (div (mod x 7) 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntRecDivasdModEq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (div (mod x 7) 7) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDefaultModEq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "eq") };
		final String inputSTR = "(= (+ (mod (mod x 7) 3) y) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntRecDivEq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "eq") };
		final String inputSTR = "(= (div (div x 7) 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntRecDivSimplifyEq() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (div (div x 3) 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	// @Test Insufficient resources to check soundness
	public void choirNightTrezor01() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "b") };
		final String inputSTR = "(= (mod (+ (* (mod (+ b 1) 4294967296) 4294967295) x) 4294967296) 1)";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDivModMultiOccurrence01() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (+ (div x 3) x) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDivModMultiOccurrence02() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "eq") };
		final String inputSTR = "(= (+ (div x 3) (mod (+ x 1) 5)) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	// @Test Insufficient resources to check soundness
	public void relationIntDivModMultiOccurrence03() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "eq") };
		final String inputSTR = "(= (div (* x y) 3) eq )";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDivModMultiOccurrence04() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "eq") };
		final String inputSTR = "(= (+ (div (* x y) 3) x) eq )";
		notSolvableForX(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDivModStickyPaint() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(<= (div (+ z (* y (- 1)) x) (- 8)) 9)";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntDivModStickyPaintSimplified() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y", "z") };
		final String inputSTR = "(= (div x (- 8)) y)";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	/**
	 * Example that is motivated by the problem that the terms of the following two lines do not evaluate to the same
	 * value for Euclidean division of integers.
	 *
	 * <pre>
	 * 20 / (-2 * 7)  =  20 / -14  =  -1    (the remainder is 6)
	 * 20 / -2 / 7  =  -10 / 7  =   -2    (the remainder is 4)
	 * </pre>
	 *
	 * So if we have -2 * y * x = 20 * t the intermediate transformation to y * x = -10 * t is unsound.
	 */
	@Test
	public void relationIntNonlin01MilkFactoryOutlet() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(<= 20 (* 2 x y))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntNonlin02Buttermilk() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(= (* (- 2) x y) 20)";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

	@Test
	public void relationIntNonlin01FactoryOutletLinear() {
		final VarDecl[] vars = { new VarDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String inputSTR = "(<= 20 (* 2 x 6))";
		testSolveForXMultiCaseOnly(SOLVER_COMMAND_Z3, inputSTR, vars);
	}

}