/*
 * Copyright (C) 2020 University of Freiburg
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.UnfTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class PolynomialRelationTestModBasedSimplification {

	private static final String SOLVER_COMMAND_Z3 = "z3 SMTLIB2_COMPLIANT=true -t:6000 -memory:2024 -smt2 -in";
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
		final Script result =
				new HistoryRecordingScript(UltimateMocks.createSolver(proviededSolverCommand, LogLevel.INFO));
		return result;
	}

	@Test
	public void bvsmodConstantSimplification01() {
		final FunDecl[] funDecls = { new FunDecl(PolynomialRelationTest::getBitvectorSort8, "x") };
		final String input = "(= (_ bv3 8) (bvsmod	(bvneg(_ bv9 8))(_ bv4 8)))";
		final String expected = "true";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void bvsmodConstantSimplificationDivZero() {
		final FunDecl[] funDecls = { new FunDecl(PolynomialRelationTest::getBitvectorSort8, "x") };
		final String input = "(= (_ bv9 8) (bvsmod	(_ bv9 8)(_ bv0 8)))";
		final String expected = "true";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void bvsmodConstantSimplification03() {
		final FunDecl[] funDecls = { new FunDecl(PolynomialRelationTest::getBitvectorSort8, "x") };
		final String input = "(= (bvneg(_ bv3 8)) (bvsmod	(_ bv9 8)(bvneg(_ bv4 8))))";
		final String expected = "true";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void bvsmodConstantSimplification04() {
		final FunDecl[] funDecls = { new FunDecl(PolynomialRelationTest::getBitvectorSort8, "x") };
		final String input = "(= (bvneg (_ bv1 8)) (bvsmod	(bvneg(_ bv9 8)) (bvneg(_ bv4 8))))";
		final String expected = "true";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void bvuremConstantSimplificationDivZero() {
		final FunDecl[] funDecls = { new FunDecl(PolynomialRelationTest::getBitvectorSort8, "x") };
		final String input = "(= (_ bv9 8) (bvurem	(_ bv9 8) (_ bv0 8)))";
		final String expected = "true";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void bvudivConstantSimplificationDivZero() {
		final FunDecl[] funDecls = { new FunDecl(PolynomialRelationTest::getBitvectorSort8, "x") };
		final String input = "(=  (_ bv255 8) (bvudiv	(_ bv9 8) (_ bv0 8)))";
		final String expected = "true";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationEq01() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		final String input = "(= (mod x 256) 256)";
		final String expected = "false";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationEq02() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		final String input = "(= (mod x 256) 255)";
		final String expected = input;
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationEq03() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		final String input = "(= (mod x 256) 0)";
		final String expected = input;
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationEq04() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		final String input = "(= (mod x 256) (- 1))";
		final String expected = "false";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationDistinct01() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		final String input = "(distinct (mod x 256) 256)";
		final String expected = "true";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationDistinct02() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		final String input = "(distinct (mod x 256) 255)";
		final String expected = input;
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationDistinct03() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		final String input = "(distinct (mod x 256) 0)";
		final String expected = input;
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationDistinct04() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		final String input = "(distinct (mod x 256) (- 1))";
		final String expected = "true";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationLess01() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		final String input = "(< (mod x 256) 256)";
		final String expected = "true";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationLess02() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		final String input = "(< (mod x 256) 255)";
		final String expected = input;
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationLess03() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		final String input = "(< (mod x 256) 0)";
		final String expected = "false";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationLess04() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		final String input = "(< (mod x 256) (- 1))";
		final String expected = "false";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationGreater01() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		final String input = "(> (mod x 256) 256)";
		final String expected = "false";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationGreater02() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		final String input = "(> (mod x 256) 255)";
		final String expected = "false";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationGreater03() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		final String input = "(> (mod x 256) 0)";
		final String expected = input;
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationGreater04() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		final String input = "(> (mod x 256) (- 1))";
		final String expected = "true";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationLeq01() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		final String input = "(<= (mod x 256) 256)";
		final String expected = "true";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationLeq02() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		final String input = "(<= (mod x 256) 255)";
		final String expected = "true";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationLeq03() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		final String input = "(<= (mod x 256) 0)";
		final String expected = input;
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationLeq04() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		final String input = "(<= (mod x 256) (- 1))";
		final String expected = "false";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationGeq01() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		final String input = "(>= (mod x 256) 256)";
		final String expected = "false";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationGeq02() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		final String input = "(>= (mod x 256) 255)";
		final String expected = input;
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationGeq03() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		final String input = "(>= (mod x 256) 0)";
		final String expected = "true";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationGeq04() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		final String input = "(>= (mod x 256) (- 1))";
		final String expected = "true";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationWithNegativeCoefficients01() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String input = "(>= (+ (* (- 2) (mod x 256)) (* 2 (mod y 256))) (- 510))";
		final String expected = "true";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationWithNegativeCoefficients02() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String input = "(>= (+ (* (- 2) (mod x 256)) (* 2 (mod y 256))) (- 509))";
		final String expected = input;
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationWithNegativeCoefficients03() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String input = "(>= (+ (* (- 2) (mod x 256)) (* 2 (mod y 256))) 510)";
		final String expected = input;
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void modBasedSimplificationWithNegativeCoefficients04() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String input = "(>= (+ (* (- 2) (mod x 256)) (* 2 (mod y 256))) 511)";
		final String expected = "false";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	@Test
	public void divisorAlwaysPositive() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x", "y") };
		final String input = "(= y (mod x (- 7)))";
		final String expected = "(= (mod x 7) y)";
		testSimplification(SOLVER_COMMAND_Z3, input, expected, funDecls);
	}

	private void testSimplification(final String solverCommand, final String inputAsString,
			final String expectedResultAsString, final FunDecl... funDecls) {
		final Script script = createSolver(solverCommand);
		script.setLogic(Logics.ALL);
		for (final FunDecl funDecl : funDecls) {
			funDecl.declareFuns(script);
		}
		mScript = script;
		final Term inputAsTerm = TermParseUtils.parseTerm(script, inputAsString);
		final Term expectedResultAsTerm = TermParseUtils.parseTerm(script, expectedResultAsString);
		// final PolynomialRelation polyRel = PolynomialRelation.convert(script, inputAsTerm);
		// final Term pnf = polyRel.positiveNormalForm(script);

		final UnfTransformer unfT = new UnfTransformer(mScript);
		final Term pnf = unfT.transform(inputAsTerm);

		System.out.println(pnf);
		Assert.assertTrue("Input and expected result are not logically equivalent",
				SmtUtils.areFormulasEquivalent(pnf, expectedResultAsTerm, script));
		if (SmtUtils.isTrueLiteral(expectedResultAsTerm) || SmtUtils.isFalseLiteral(expectedResultAsTerm)) {
			// for NOOPs the input is always logically equivalent, if true/false expected we
			// check this syntactically
			Assert.assertTrue("Simplification failed", pnf.equals(expectedResultAsTerm));
		}
		if (SmtUtils.isTrueLiteral(pnf) || SmtUtils.isFalseLiteral(pnf)) {
			// check that expected result in the test suite did not miss an simplification
			// that is performed by the implementation
			Assert.assertTrue("Expected result missed simplification", pnf.equals(expectedResultAsTerm));
		}
	}

}