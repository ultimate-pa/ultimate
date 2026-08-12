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
 * @author Roman Vintonyak
 * @author David Enoghama
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
		// before simplification runs. This actually exercises BitvectorUtils.simplifyBvand.
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
		// x is a free variable so this actually exercises the annihilation branch in BitvectorUtils.simplifyBvor.
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
		// x is a free variable so the two literals must actually be folded together by BitvectorUtils.simplifyBvxor.
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
		// BitvectorUtils.simplifyBvxor, in case a breakpoint placed later
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

	// --- Step 1 (flatten): additional edge cases ---

	@Test
	public void bvandDifferentOperatorsNotFlattened() {
		// Flattening must only unwrap applications of the SAME operator. (bvor y z) is a different operator than
		// the outer bvand, so it must stay intact as one non-literal argument instead of being exploded into y, z.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y", "z") };
		final String formulaAsString = "(bvand x (bvor y z))";
		final String expected = "(bvand x (bvor y z))";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvorNestedApplicationResolvesBottomUp() {
		// A literal nested inside a sub-application never reaches the outer flatten() unresolved: since terms are
		// built bottom-up, the inner (bvor (_ bv0 8) y) is fully simplified to "y" (absorption of 0) before the
		// outer bvor ever sees it. This is exactly why flatten() does not need to recurse (see its comment).
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y") };
		final String formulaAsString = "(bvor x (bvor (_ bv0 8) y))";
		final String expected = "(bvor x y)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	// --- Step 2 (split, sort): additional edge cases ---

	@Test
	public void bvorNonAdjacentDuplicateElimination() {
		// Unlike the other duplicate-elimination tests, the two occurrences of y are NOT adjacent in the raw
		// input. This only collapses correctly if sortByHashCode actually brings them together before the
		// duplicate-collecting step counts runs.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y") };
		final String formulaAsString = "(bvor y x y)";
		final String expected = "(bvor x y)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvandOrderIndependence() {
		// The expected-result comparison in runSimplificationTest normalizes both sides via CommuhashNormalForm
		// before comparing, which would mask a broken sort. This test instead compares two raw post-UnfTransformer
		// results directly against each other: (bvand y x) and (bvand x y) must produce the identical term.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y") };
		final Script script = mMgdScript.getScript();
		for (final FunDecl funDecl : funDecls) {
			funDecl.declareFuns(script);
		}

		final Term firstOrder = new UnfTransformer(script)
				.transform(new FormulaUnLet().transform(TermParseUtils.parseTerm(script, "(bvand y x)")));
		final Term secondOrder = new UnfTransformer(script)
				.transform(new FormulaUnLet().transform(TermParseUtils.parseTerm(script, "(bvand x y)")));

		MatcherAssert.assertThat(firstOrder, IsEqual.equalTo(secondOrder));
	}

	// --- Step 3 (constant folding): additional edge cases ---

	@Test
	public void bvandLiteralEvaluationThreeLiterals() {
		// Tests that folding generalizes past the first pair of literals: (1 AND x AND 3 AND 5) -> (1 AND x).
		// 1 (00000001) AND 3 (00000011) = 1, then 1 AND 5 (00000101) = 1, which is neither 0 nor 255.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvand (_ bv1 8) x (_ bv3 8) (_ bv5 8))";
		final String expected = "(bvand (_ bv1 8) x)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	// --- Step 4 (duplicate collectors): additional edge cases ---

	@Test
	public void bvandIdempotenceThreeCopies() {
		// Idempotence collapses ANY number of copies (not just pairs) to one: (x AND x AND x) -> x. Contrasts with
		// bvxorNilpotenceThreeCopies below, where an odd count also survives but for a different reason (parity).
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvand x x x)";
		final String expected = "x";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvxorNilpotenceThreeCopies() {
		// Nilpotence is a parity check, not a presence check: an odd run length (here 3) leaves exactly one copy,
		// not zero and not three: (x XOR x XOR x) -> x.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvxor x x x)";
		final String expected = "x";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvxorTwoSeparateDuplicatePairs() {
		// Two independent duplicate pairs must each cancel on their own run, without interfering with each other:
		// (x XOR x XOR y XOR y XOR z) -> z.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y", "z") };
		final String formulaAsString = "(bvxor x x y y z)";
		final String expected = "z";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	// --- Step 5 (absorption, annihilation): additional edge cases ---

	@Test
	public void bvorAnnihilationViaFoldedAllOnes() {
		// The all-ones value does not need to be written directly: it can also emerge from folding several
		// literals. 200 (11001000) OR 55 (00110111) = 255, which then annihilates the whole bvor, dropping x.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvor (_ bv200 8) x (_ bv55 8))";
		final String expected = "(_ bv255 8)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvxorAbsorptionViaFoldedZero() {
		// Same idea for bvxor's neutral element: 12 XOR 12 folds to 0, which is then absorbed (dropped), leaving
		// only x: (12 XOR 12 XOR x) -> x.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvxor (_ bv12 8) (_ bv12 8) x)";
		final String expected = "x";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvxorAllOnesPreserved() {
		// Negative-space guard: unlike bvand/bvor, bvxor has no special rule for the all-ones constant, so it must
		// be kept as-is rather than accidentally dropped or annihilated: (x XOR 255) stays (x XOR 255).
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvxor x (_ bv255 8))";
		final String expected = "(bvxor x (_ bv255 8))";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvandWidth1AllOnesAbsorption() {
		// isAllOnes depends on the bit width (2^width - 1), so it needs coverage away from the usual 8-bit sort.
		// At width 1 the all-ones value is 1 itself: (x AND 1) -> x.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort1, "x") };
		final String formulaAsString = "(bvand x (_ bv1 1))";
		final String expected = "x";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvorWidth1IdentityZero() {
		// Companion to bvandWidth1AllOnesAbsorption: confirms the zero-check itself (width-independent) still
		// works correctly at the same tiny width, right next to the all-ones boundary: (x OR 0) -> x.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort1, "x") };
		final String formulaAsString = "(bvor x (_ bv0 1))";
		final String expected = "x";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvorWidth32AnnihilationMax() {
		// isAllOnes must also generalize to wider bit widths: at width 32 the all-ones value is 2^32 - 1, which
		// annihilates bvor just like 255 does at width 8.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "x") };
		final String formulaAsString = "(bvor x (_ bv4294967295 32))";
		final String expected = "(_ bv4294967295 32)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	// --- Step 6 (assembly): additional edge cases ---

	@Test
	public void bvxorNilpotenceWithNonzeroLiteralSurvivor() {
		// The single surviving finalArgs entry can also be the literal, not just a variable: both x's cancel via
		// nilpotence, leaving only the constant 5 to be unwrapped: (5 XOR x XOR x) -> 5.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvxor (_ bv5 8) x x)";
		final String expected = "(_ bv5 8)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvandNoSimplificationPassThrough() {
		// Minimal regression guard: two distinct free variables and no literals means there is nothing to fold,
		// absorb, or deduplicate. The pipeline must leave this case intact instead of mis-simplifying it.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y") };
		final String formulaAsString = "(bvand x y)";
		final String expected = "(bvand x y)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvConstantsCase() {
		final String formulaAsString = "(bvand (_ bv1 8) (_ bv3 8) (_ bv7 8))";
		final String expected = "(_ bv1 8)";

		SimplificationTest.runSimplificationTest(new FunDecl[0], formulaAsString, expected,
				SimplificationTechnique.POLY_PAC, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	// --- Operator mirroring (bvugt/bvuge/bvsgt/bvsge -> bvult/bvule/bvslt/bvsle) ---

	@Test
	public void bvugtMirroredToBvult() {
		// Unsigned "greater than" is eliminated by swapping operands into "less than": (x bvugt 1) -> (1 bvult x).
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvugt x (_ bv1 8))";
		final String expected = "(bvult (_ bv1 8) x)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvugeMirroredToBvule() {
		// Same mirroring for the non-strict unsigned variant: (x bvuge 1) -> (1 bvule x).
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvuge x (_ bv1 8))";
		final String expected = "(bvule (_ bv1 8) x)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvsgtMirroredToBvslt() {
		// Signed "greater than" is mirrored the same way as the unsigned case: (x bvsgt 1) -> (1 bvslt x).
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvsgt x (_ bv1 8))";
		final String expected = "(bvslt (_ bv1 8) x)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvsgeMirroredToBvsle() {
		// Same mirroring for the non-strict signed variant: (x bvsge 1) -> (1 bvsle x).
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvsge x (_ bv1 8))";
		final String expected = "(bvsle (_ bv1 8) x)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvugtConstantFoldingAfterMirroring() {
		// Guards against a purely syntactic swap: mirroring to bvult must still trigger the existing constant
		// folding, not just rewrite the operator. Both operands are literals here, so the result must be "true",
		// not an unevaluated (bvult (_ bv3 8) (_ bv5 8)) term.
		final String formulaAsString = "(bvugt (_ bv5 8) (_ bv3 8))";
		final String expected = "true";

		SimplificationTest.runSimplificationTest(new FunDecl[0], formulaAsString, expected,
				SimplificationTechnique.POLY_PAC, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvsgtConstantFoldingAfterMirroring() {
		// Same guard for the signed variant, to confirm signed constant folding also still works after mirroring.
		final String formulaAsString = "(bvsgt (_ bv5 8) (_ bv3 8))";
		final String expected = "true";

		SimplificationTest.runSimplificationTest(new FunDecl[0], formulaAsString, expected,
				SimplificationTechnique.POLY_PAC, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	// --- Extract-over-extend no-op ---

	@Test
	public void bvExtractOverSignExtend() {
		// extract exactly undoes sign_extend when the width matches: ((_ extract 7 0) ((_ sign_extend 24) x)) -> x.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "((_ extract 7 0) ((_ sign_extend 24) x))";
		final String expected = "x";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvExtractOverZeroExtend() {
		// Same no-op for zero_extend: ((_ extract 7 0) ((_ zero_extend 24) x)) -> x.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "((_ extract 7 0) ((_ zero_extend 24) x))";
		final String expected = "x";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvExtractOverSignExtendWrongWidthNotSimplified() {
		// Guard: extracting MORE than the original width reaches into the padding bits (unknown for symbolic x), so
		// the rule must not fire: ((_ extract 15 0) ((_ sign_extend 24) x)) must stay unsimplified.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "((_ extract 15 0) ((_ sign_extend 24) x))";
		final String expected = "((_ extract 15 0) ((_ sign_extend 24) x))";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvExtractOfPlainVariableNotSimplified() {
		// Guard: no sign_extend/zero_extend underneath at all, so the rule must not touch it.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "y") };
		final String formulaAsString = "((_ extract 7 0) y)";
		final String expected = "((_ extract 7 0) y)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

}