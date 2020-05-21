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

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.NotAffineException;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.polynomial.solve_for_subject.MultiCaseSolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.polynomial.solve_for_subject.MultiCaseSolvedBinaryRelation.Xnf;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * @author Max Barth (Max.Barth95@gmx.de)
 * @author LeonardFichtner (leonard.fichtner@web.de)
 */
public class PolynomialRelationTest {

	/**
	 * Warning: each test will overwrite the SMT script of the preceding test.
	 */
	private static final boolean WRITE_SMT_SCRIPTS_TO_FILE = false;
	private static final String SOLVER_COMMAND_Z3 = "z3 SMTLIB2_COMPLIANT=true -t:3500 -memory:2024 -smt2 -in";
	private static final String SOLVER_COMMAND_CVC4 =
			"cvc4 --incremental --print-success --lang smt --rewrite-divk --tlimit-per=3000";
	private static final String SOLVER_COMMAND_MATHSAT = "mathsat";
	private IUltimateServiceProvider mServices;
	private Script mScript;

	@Before
	public void setUp() throws IOException {
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		final Script tmp = new HistoryRecordingScript(UltimateMocks.createSolver(SOLVER_COMMAND_Z3, LogLevel.INFO));
		if (WRITE_SMT_SCRIPTS_TO_FILE) {
			mScript = new LoggingScript(tmp, "PolynomialRelationTest.smt2", true);
		} else {
			mScript = tmp;
		}
		mScript.setLogic(Logics.ALL);

		new VarDecl(SmtSortUtils::getRealSort, "hi", "lo", "x", "y", "z", "u", "ri").declareVars(mScript);
		new VarDecl(SmtSortUtils::getIntSort, "xi", "yi", "zi").declareVars(mScript);
	}

	@After
	public void tearDown() {
		mScript.exit();
	}

	@Test
	public void relationRealDefault() throws NotAffineException {
		final String inputSTR = "(= (+ 7.0 x) y )";
		testSolveForSubject(inputSTR, "x");

	}

	@Test
	public void relationRealEQ() throws NotAffineException {
		final String inputSTR = "(= (* 7.0 x) y )";
		testSolveForSubject(inputSTR, "x");

	}

	@Test
	public void relationRealEQ2() throws NotAffineException {
		final String inputSTR = "(= (* 3.0 x) (* 7.0 y) )";
		testSolveForSubject(inputSTR, "x");
	}

	@Test
	public void relationRealEQ3() throws NotAffineException {
		final String inputSTR = "(= (* 3.0 x) (+ (* 7.0 y) (* 5.0 z)) )";
		testSolveForSubject(inputSTR, "x");
	}

	@Test
	public void relationRealEQ4() throws NotAffineException {
		final String inputSTR = "(= (* 6.0 (+ y x)) (* 7.0 z) )";
		testSolveForSubject(inputSTR, "x");
	}

	@Test
	public void relationRealPolyEQPurist01() throws NotAffineException {
		final String inputSTR = "(= (* y x) ri)";
		testSolveForSubjectMultiCaseOnly(inputSTR, "x");
	}

	@Test
	public void relationRealPolyEQPurist02() throws NotAffineException {
		final String inputSTR = "(= (* y x z) ri)";
		testSolveForSubjectMultiCaseOnly(inputSTR, "x");
	}

	@Test
	public void relationRealPolyEQ5() throws NotAffineException {
		final String inputSTR = "(= (* 6.0 (* y x)) (+ 3.0 (* z z)))";
		testSolveForSubjectMultiCaseOnly(inputSTR, "x");
	}

	@Test
	public void relationRealPolyEQ6() throws NotAffineException {
		final String inputSTR = "(= (* z (+ 6.0 (* (* y y) x))) (+ 3.0 (* z z)))";
		testSolveForSubjectMultiCaseOnly(inputSTR, "x");
	}

	@Test
	public void relationRealPolyEQ7() throws NotAffineException {
		final String inputSTR = "(= (* 3.0 x (/ y z) z 5.0) (* y z)))";
		testSolveForSubjectMultiCaseOnly(inputSTR, "x");
	}

	@Test
	public void relationRealPolyMultipleSubjectsEQ7() throws NotAffineException {
		final String inputSTR = "(= (* z (+ 6.0 (* (* x y) x))) (+ 3.0 (* z z)))";
		Assert.assertNull(polyRelOnLeftHandSide(inputSTR, "x"));
	}

	/**
	 * The background why this shouldn't work, is because divisions by variables are treated as an individual variable,
	 * but now the subject occurs in this variable.
	 */
	@Test
	public void relationRealPolyNestedSubjectEQ8() throws NotAffineException {
		final String inputSTR = "(= 1.0 (/ y x))";
		Assert.assertNull(polyRelOnLeftHandSide(inputSTR, "x"));
	}

	@Test
	public void relationRealPolyWithDivisionsEQ9() throws NotAffineException {
		final String inputSTR = "(= (/ (+ 6.0 (* (/ z y) x)) 2.0) (+ 3.0 (/ y z)))";
		testSolveForSubjectMultiCaseOnly(inputSTR, "x");
	}

	@Test
	public void relationRealPolyDetectNestedSecondVariableEQ10() throws NotAffineException {
		final String inputSTR = "(= (/ (+ 6.0 (* (/ z y) x)) 2.0) (+ 3.0 (/ y x)))";
		Assert.assertNull(polyRelOnLeftHandSide(inputSTR, "x"));
	}

	@Test
	public void relationRealGEQ01() throws NotAffineException {
		final String inputSTR = "(>= (* 3.0 x) lo )";
		testSolveForSubject(inputSTR, "x");
	}

	@Test
	public void relationRealPolyGEQPurist01() throws NotAffineException {
		final String inputSTR = "(>= (* x y) ri)";
		testSolveForSubjectMultiCaseOnly(inputSTR, "x");
	}

	@Test
	public void relationRealPolyGEQPurist02() throws NotAffineException {
		final String inputSTR = "(>= (* x y y y z z u) ri)";
		testSolveForSubjectMultiCaseOnly(inputSTR, "x");
	}

	@Test
	public void relationRealPolyGEQ02() throws NotAffineException {
		final String inputSTR = "(>= (* 3.0 x (/ y z) z 5.0) (* y lo))";
		testSolveForSubjectMultiCaseOnly(inputSTR, "x");
	}

	@Test
	public void relationRealLEQ01() throws NotAffineException {
		final String inputSTR = "(<= (* 3.0 x) hi )";
		testSolveForSubject(inputSTR, "x");
	}

	@Test
	public void relationRealPolyLEQ02() throws NotAffineException {
		final String inputSTR = "(<= (* 3.0 x (/ y z) z 5.0) (* y hi))";
		testSolveForSubjectMultiCaseOnly(inputSTR, "x");
	}

	@Test
	public void relationRealDISTINCT01() throws NotAffineException {
		final String inputSTR = "(not(= (* 3.0 x) y ))";
		testSolveForSubject(inputSTR, "x");
	}

	@Test
	public void relationRealPolyDISTINCT02() throws NotAffineException {
		final String inputSTR = "(not(= (* 3.0 x (/ y z) z 5.0) (* y z)))";
		testSolveForSubjectMultiCaseOnly(inputSTR, "x");
	}

	@Test
	public void relationRealGREATER01() throws NotAffineException {
		final String inputSTR = "(> (* 3.0 x) lo )";
		testSolveForSubject(inputSTR, "x");
	}

	@Test
	public void relationRealPolyGREATER02() throws NotAffineException {
		final String inputSTR = "(> (* 3.0 x (/ y z) z 5.0) (* y lo))";
		testSolveForSubjectMultiCaseOnly(inputSTR, "x");
	}

	@Test
	public void relationRealLESS01() throws NotAffineException {
		final String inputSTR = "(< (* 4.0 x) hi )";
		testSolveForSubject(inputSTR, "x");
	}

	@Test
	public void relationRealPolyLESS02() throws NotAffineException {
		final String inputSTR = "(< (* 3.0 x (/ y z) z 5.0) (* y hi))";
		testSolveForSubjectMultiCaseOnly(inputSTR, "x");
	}

	@Test
	public void relationBvPolyEQ01() throws NotAffineException {
		final String inputSTR = "(= (bvmul (_ bv255 8) xb) (bvmul (_ bv64 8) yb yb yb))";
		final Sort bv8 = SmtSortUtils.getBitvectorSort(mScript, 8);
		mScript.declareFun("xb", new Sort[0], bv8);
		mScript.declareFun("yb", new Sort[0], bv8);
		testSolveForSubject(inputSTR, "xb");
	}

	@Test
	public void relationBvPolyEQ02() throws NotAffineException {
		final String inputSTR = "(= (bvmul (_ bv1 8) xb) (bvmul (_ bv64 8) yb yb yb))";
		final Sort bv8 = SmtSortUtils.getBitvectorSort(mScript, 8);
		mScript.declareFun("xb", new Sort[0], bv8);
		mScript.declareFun("yb", new Sort[0], bv8);
		testSolveForSubject(inputSTR, "xb");
	}

	@Test
	public void relationBvPolyEQ03() throws NotAffineException {
		final String inputSTR = "(= (bvmul (_ bv255 8) xb yb) (bvmul (_ bv64 8) yb yb yb))";
		final Sort bv8 = SmtSortUtils.getBitvectorSort(mScript, 8);
		mScript.declareFun("xb", new Sort[0], bv8);
		mScript.declareFun("yb", new Sort[0], bv8);
		Assert.assertNull(polyRelOnLeftHandSide(inputSTR, "xb"));
	}

	@Test
	public void relationBvPolyEQ04() throws NotAffineException {
		final String inputSTR = "(= (bvmul (_ bv252 8) xb) (bvmul (_ bv64 8) yb yb yb))";
		final Sort bv8 = SmtSortUtils.getBitvectorSort(mScript, 8);
		mScript.declareFun("xb", new Sort[0], bv8);
		mScript.declareFun("yb", new Sort[0], bv8);
		Assert.assertNull(polyRelOnLeftHandSide(inputSTR, "xb"));
	}

	@Test
	public void relationBvEQ05() throws NotAffineException {
		final String inputSTR = "(= (bvmul (_ bv255 8) xb) (bvmul (_ bv8 8) yb))";
		final Sort bv8 = SmtSortUtils.getBitvectorSort(mScript, 8);
		mScript.declareFun("xb", new Sort[0], bv8);
		mScript.declareFun("yb", new Sort[0], bv8);
		testSolveForSubject(inputSTR, "xb");
	}

	@Test
	public void relationIntEQ1() throws NotAffineException {
		final String inputSTR = "(= (* 3 xi) (+ (* 7 yi) (* 5 zi)) )";
		testSolveForSubject(inputSTR, "xi");
	}

	@Test
	public void relationIntEQ2() throws NotAffineException {
		final String inputSTR = "(= (* 6 (+ yi xi)) (* 7 zi) )";
		testSolveForSubject(inputSTR, "xi");
	}

	@Test
	public void relationIntPolyPuristEq() throws NotAffineException {
		final String inputSTR = "(= (* yi xi) zi )";
		testSolveForSubjectMultiCaseOnly(inputSTR, "xi");
	}

	/**
	 * One of the supporting terms in the y-not-zero-case
	 * is not (< xi (div zi yi)) but (< xi (+ (div (- zi 1)  yi) 1))
	 * You can see the problem for yi=2, xi=1, and zi=3
	 *
	 */
	@Test
	public void relationIntPolyPuristLeq() throws NotAffineException {
		final String inputSTR = "(< (* yi xi) zi )";
		testSolveForSubjectMultiCaseOnly(inputSTR, "xi");
	}

	public void relationIntPolyMATHSATEQ3() throws NotAffineException {
		final String inputSTR = "(= (* 6 (* yi xi)) (+ 3 (* zi zi)))";
		testSolveForSubject(inputSTR, "xi");
	}

	public void relationIntPolyUnknownEQ4() throws NotAffineException {
		final String inputSTR = "(= (* zi (+ 6 (* (* yi yi) xi))) (+ 3 (* zi zi)))";
		testSolveForSubjectMultiCaseOnly(inputSTR, "xi");
	}

	public void relationIntPolyUnknownEQ5() throws NotAffineException {
		final String inputSTR = "(= (* 3 xi (div yi zi) zi 5) (* yi zi)))";
		testSolveForSubject(inputSTR, "xi");
	}

	@Test
	public void relationIntPolyZ3CVC4EQ6() throws NotAffineException {
		final String inputSTR = "(= (* 3 yi xi) (* 9 yi))";
		testSolveForSubjectMultiCaseOnly(inputSTR, "xi");
	}

	@Test
	public void relationIntPolyZ3CVC4MATHSATEQ7() throws NotAffineException {
		final String inputSTR = "(= (* 3 yi xi) (* 333 yi))";
		testSolveForSubjectMultiCaseOnly(inputSTR, "xi");
	}

	public void relationIntPolyMATHSATEQ8() throws NotAffineException {
		final String inputSTR = "(= (* 3 yi xi) (* 21 zi))";
		testSolveForSubject(inputSTR, "xi");
	}

	public void relationIntPolyCVC4MATHSATEQ9() throws NotAffineException {
		final String inputSTR = "(= (* 3 yi xi) (* 21 zi yi))";
		testSolveForSubject(inputSTR, "xi");
	}

	@Test
	public void relationIntPolyZ3MATHSATEQ10() throws NotAffineException {
		final String inputSTR = "(= (* 3 yi xi) (* 11 yi))";
		testSolveForSubjectMultiCaseOnly(inputSTR, "xi");
	}

	public void relationIntPolyCVC4MATHSATEQ11() throws NotAffineException {
		final String inputSTR = "(= (* 3 yi xi) (* 333 yi yi yi))";
		testSolveForSubject(inputSTR, "xi");
	}

	public void relationIntPolyUnknownEQ12() throws NotAffineException {
		final String inputSTR = "(= (* yi (+ 6 (* yi xi))) (+ 3 yi))";
		testSolveForSubjectMultiCaseOnly(inputSTR, "xi");
	}

	@Test
	public void relationIntPolyZ3EQ13() throws NotAffineException {
		final String inputSTR = "(= (* 3 (div xi 6) (div yi zi)) (* yi zi))";
		testSolveForSubjectMultiCaseOnly(inputSTR, "xi");
	}

	public void relationIntPolyUnknownEQ14() throws NotAffineException {
		final String inputSTR = "(= (* 3 (div xi 6) (+ 5 (div yi zi))) (* yi zi))";
		testSolveForSubjectMultiCaseOnly(inputSTR, "xi");
	}

	@Test
	public void relationIntPolyZ3CVC4MATHSATEQ15() throws NotAffineException {
		final String inputSTR = "(= (* yi (+ 6 xi)) (+ 3 yi))";
		testSolveForSubjectMultiCaseOnly(inputSTR, "xi");
	}

	// /**
	// * Currently fails because some coefficient is null, this probably will be handled when the
	// * "Todo if no constantTErm throw error or handle it" is finished
	// */
	// @Test
	// public void relationIntPolyUnknownEQ16() throws NotAffineException {
	// final String inputSTR = "(= (div (div xi 5 2) (div yi zi)) yi))";
	// testSolveForSubjectMultiCaseOnly(inputSTR, "xi");
	// }

	private MultiCaseSolvedBinaryRelation polyRelOnLeftHandSide(final String termAsString, final String varString)
			throws NotAffineException {
		final Term var = TermParseUtils.parseTerm(mScript, varString);
		final MultiCaseSolvedBinaryRelation sbr =
				PolynomialRelation.convert(mScript, TermParseUtils.parseTerm(mScript, termAsString))
						.solveForSubject(mScript, var, Xnf.DNF);
		return sbr;
	}

	private void testSolveForSubject(final String inputAsString, final String subject) throws NotAffineException {
		final Term inputAsTerm = TermParseUtils.parseTerm(mScript, inputAsString);
		final Term x = TermParseUtils.parseTerm(mScript, subject);
		testSingleCaseSolveForSubject(inputAsTerm, x);
		testMultiCaseSolveForSubject(inputAsTerm, x, Xnf.DNF);
		// testMultiCaseSolveForSubject(inputAsTerm, x, Xnf.CNF); this is not yet implemented?
	}

	private void testSolveForSubjectMultiCaseOnly(final String inputAsString, final String subject)
			throws NotAffineException {
		final Term inputAsTerm = TermParseUtils.parseTerm(mScript, inputAsString);
		final Term x = TermParseUtils.parseTerm(mScript, subject);
		testMultiCaseSolveForSubject(inputAsTerm, x, Xnf.DNF);
		// testMultiCaseSolveForSubject(inputAsTerm, x, Xnf.CNF);
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
		final Term solvedAsTerm = mcsbr.asTerm(mScript);
		mScript.echo(new QuotedObject("Checking if input and output of multiCaseSolveForSubject are equivalent"));
		Assert.assertTrue(SmtUtils.areFormulasEquivalent(inputAsTerm, solvedAsTerm, mScript));
	}

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
}