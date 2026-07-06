/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

import org.hamcrest.MatcherAssert;
import org.hamcrest.core.IsEqual;
import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.StatisticsScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.UnfTransformer;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * Tests for the n-ary (variadic) bvand/bvor/bvxor simplification added to
 * {@link de.uni_freiburg.informatik.ultimate.lib.smtlibutils.BitvectorUtils}: flattening of nested applications,
 * literal folding, duplicate elimination (idempotence for bvand/bvor, nilpotence for bvxor), and
 * absorption/annihilation with the neutral (0) and absorbing (all-ones) bitvector constants.
 *
 * Extracted from {@link SimplificationTest} into its own file; reuses {@link SimplificationTest#runSimplificationTest}
 * so the test-running/-checking logic is not duplicated.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class BitvectorUtilsTest {

	/**
	 * Warning: each test will overwrite the SMT script of the preceding test.
	 */
	private static final boolean WRITE_SMT_SCRIPTS_TO_FILE = false;
	private static final boolean WRITE_BENCHMARK_RESULTS_TO_WORKING_DIRECTORY = false;
	private static final long TEST_TIMEOUT_MILLISECONDS = 20_000;
	private static final LogLevel LOG_LEVEL = LogLevel.INFO;
	private static final String SOLVER_COMMAND = "cvc4 --incremental --lang smt";

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;
	private static QuantifierEliminationTestCsvWriter mCsvWriter;

	@BeforeClass
	public static void beforeAllTests() {
		mCsvWriter = new QuantifierEliminationTestCsvWriter(BitvectorUtilsTest.class.getSimpleName());
	}

	@AfterClass
	public static void afterAllTests() {
		if (WRITE_BENCHMARK_RESULTS_TO_WORKING_DIRECTORY) {
			try {
				mCsvWriter.writeCsv();
			} catch (final IOException e) {
				throw new AssertionError(e);
			}
		}
	}

	@Before
	public void setUp() throws IOException {
		mServices = UltimateMocks.createUltimateServiceProviderMock(LOG_LEVEL);
		mServices.getProgressMonitorService().setDeadline(System.currentTimeMillis() + TEST_TIMEOUT_MILLISECONDS);
		mLogger = mServices.getLoggingService().getLogger("lol");

		final Script solverInstance = new HistoryRecordingScript(UltimateMocks.createSolver(SOLVER_COMMAND, LOG_LEVEL));
		if (WRITE_SMT_SCRIPTS_TO_FILE) {
			mScript = new LoggingScript(solverInstance, "BitvectorUtilsTest.smt2", true);
		} else {
			mScript = solverInstance;
		}
		mScript = new StatisticsScript(mScript);

		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);
	}

	@After
	public void tearDown() {
		mScript.exit();
		mCsvWriter.reportTestFinished();
	}

	@Test
	public void bvaddAbsorption() { // Testing new class allowing multiple elements
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvand (_ bv2 8) x (_ bv1 8))";
		final String simplified = "(_ bv0 8)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, simplified,
				SimplificationTechnique.POLY_PAC, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvandFlatteningOnlyVariables() {
		// x, y, z are declared as free (unconstrained) variables so that FormulaUnLet cannot substitute them away
		// before simplification runs. This actually exercises simplify_NonConstantCase.
		// Also tests duplicate elimination (idempotence): y occurs twice and must collapse to a single occurrence.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y", "z") };
		final String formulaAsString = "(bvand x (bvand y (bvand y z)))";
		final String expected = "(bvand x y z)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvandIdentityElimination() {
		// x is a free variable, so (x AND 255) must simplify to x via absorption (255 is the all-ones element).
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvand x (_ bv255 8))";
		final String expected = "x";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvorAbsorptionMax() {
		// Tests absorption for OR: (x OR 255) -> 255
		// For an 8-bit vector, 255 (0xFF, i.e. all ones) is the absorbing element.
		// x is a free variable so this actually exercises the annihilation branch in simplify_NonConstantCase.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvor x (_ bv255 8))";
		final String expected = "(_ bv255 8)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvxorFlattening() {
		// Tests whether nested XOR operations are flattened: (x XOR (y XOR z)) -> x XOR y XOR z
		// x, y, z are free variables so FormulaUnLet cannot collapse them and flattening is actually exercised.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y", "z") };
		final String formulaAsString = "(bvxor x (bvxor y z))";
		final String expected = "(bvxor x y z)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvorIdentityZero() {
		// Tests the neutral element for OR: (x OR 0) -> x
		// The zero must vanish from the operation completely.
		// x is a free variable, so the expected result is unambiguously x (not a constant).
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvor x (_ bv0 8))";
		final String expected = "x";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvxorLiteralEvaluation() {
		// Tests pre-evaluation of literals for XOR: (12 XOR x XOR 3) -> (15 XOR x)
		// Since 12 (1100) XOR 3 (0011) = 15 (1111)
		// x is a free variable so the two literals must actually be folded together by simplify_NonConstantCase.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvxor (_ bv12 8) x (_ bv3 8))";
		final String expected = "(bvxor (_ bv15 8) x)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvxorIdentityZero() {
		// Tests that 0 vanishes for XOR: (x XOR 0) -> x
		// x is a free variable, so the expected result is unambiguously x (not a constant).
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvxor x (_ bv0 8))";
		final String expected = "x";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvxorLiteralEvaluationWithVariable() {
		// 1. Get the underlying script
		final Script script = mMgdScript.getScript();

		// 2. Declare x as a global 8-bit bitvector directly in the SMT context
		final de.uni_freiburg.informatik.ultimate.logic.Sort bvSort = script.sort("BitVec", new String[] { "8" });
		script.declareFun("x", new de.uni_freiburg.informatik.ultimate.logic.Sort[0], bvSort);

		// 3. The nested test formula: (12 XOR (x XOR 3))
		final String formulaAsString = "(bvxor (_ bv12 8) (bvxor x (_ bv3 8)))";
		final String expected = "(bvxor (_ bv15 8) x)";

		// 4. Pass an empty array for FunDecl, since x is already declared!
		SimplificationTest.runSimplificationTest(new FunDecl[0], formulaAsString, expected,
				SimplificationTechnique.POLY_PAC, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvandDuplicateElimination() {
		// Idempotence for AND: (x AND x) -> x. The duplicate must be removed, not merged into an operator.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvand x x)";
		final String expected = "x";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvorDuplicateElimination() {
		// Idempotence for OR: (x OR x OR y) -> (x OR y). One occurrence of x must be dropped, y stays untouched.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y") };
		final String formulaAsString = "(bvor x x y)";
		final String expected = "(bvor x y)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvxorNilpotencePairCancelsDuringUnfTransformer() {
		// This test isolates the exact call that hits the finalArgs.isEmpty() branch in
		// NaryBitvectorOperation_BitvectorResult.simplify_NonConstantCase, in case a breakpoint placed later
		// (e.g. inside SmtUtils.simplifyWithStatistics, which runs AFTER UnfTransformer in runSimplificationTest)
		// never triggers: for a plain "(bvxor x x)" formula the whole term is already fully resolved to the
		// zero-constant during the UnfTransformer pass, before simplifyWithStatistics even gets to see it. There
		// is nothing left for the later simplification technique to do, so a breakpoint placed there will never
		// fire for this input - the branch was already executed earlier, right here.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final Script script = mMgdScript.getScript();
		for (final FunDecl funDecl : funDecls) {
			funDecl.declareFuns(script);
		}

		final Term formulaAsTerm = TermParseUtils.parseTerm(script, "(bvxor x x)");
		final Term letFree = new FormulaUnLet().transform(formulaAsTerm);

		final Term unf = new UnfTransformer(script).transform(letFree);

		final Term expected = TermParseUtils.parseTerm(script, "(_ bv0 8)");
		MatcherAssert.assertThat(unf, IsEqual.equalTo(expected));
	}

	@Test
	public void bvxorNilpotencePairCancels() {
		// Nilpotence for XOR: (x XOR x) -> 0. Both occurrences cancel out completely, so finalArgs is empty and the
		// zero-constant edge case (BitvectorUtils.constructTerm with BigInteger.ZERO) must kick in.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvxor x x)";
		final String expected = "(_ bv0 8)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvxorNilpotenceWithRemainder() {
		// Nilpotence for XOR with a surviving variable: (x XOR x XOR y) -> y. The x-pair cancels (even count), y is
		// unpaired (odd count) and must remain; since only one term is left, no operator node is needed at all.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y") };
		final String formulaAsString = "(bvxor x x y)";
		final String expected = "y";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvandLiteralEvaluation() {
		// Tests pre-evaluation of literals for AND: (12 AND x AND 14) -> (12 AND x)
		// Since 12 (00001100) AND 14 (00001110) = 12 (00001100), which is neither 0 nor 255, the operator stays.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvand (_ bv12 8) x (_ bv14 8))";
		final String expected = "(bvand (_ bv12 8) x)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvandLiteralEvaluationTriggersAnnihilation() {
		// Tests the interplay of literal folding and annihilation for AND: (12 AND x AND 3) -> 0
		// Since 12 (00001100) AND 3 (00000011) = 0, annihilation (X AND 0 = 0) kicks in and x is dropped
		// entirely, even though x itself is unknown. Important: literal folding must run BEFORE the annihilation
		// check, otherwise this case would not be detected.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvand (_ bv12 8) x (_ bv3 8))";
		final String expected = "(_ bv0 8)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvorLiteralEvaluation() {
		// Tests pre-evaluation of literals for OR: (12 OR x OR 3) -> (15 OR x)
		// Since 12 (00001100) OR 3 (00000011) = 15 (00001111), which is neither 0 nor 255, the operator stays.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvor (_ bv12 8) x (_ bv3 8))";
		final String expected = "(bvor (_ bv15 8) x)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvorIdentityZeroWithMultipleVariables() {
		// Tests that 0 also vanishes for OR when several variables remain:
		// (x OR 0 OR y) -> (x OR y). Unlike bvorIdentityZero, the operator is kept here, since after the 0 drops
		// out there are still two terms left (no finalArgs.size() == 1 special case).
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y") };
		final String formulaAsString = "(bvor x (_ bv0 8) y)";
		final String expected = "(bvor x y)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

}