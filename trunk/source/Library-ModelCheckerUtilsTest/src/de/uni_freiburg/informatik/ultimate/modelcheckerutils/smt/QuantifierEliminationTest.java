/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
import java.math.BigInteger;
import java.util.Arrays;

import org.junit.After;
import org.junit.AfterClass;
import org.junit.Assert;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.SmtFunctionsAndAxioms;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.DeclarableFunctionSymbol;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.CommuhashNormalForm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.ExtendedSimplificationResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.StatisticsScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalNestedStore;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PrenexNormalForm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class QuantifierEliminationTest {

	/**
	 * Warning: each test will overwrite the SMT script of the preceding test.
	 */
	private static final boolean WRITE_SMT_SCRIPTS_TO_FILE = false;
	private static final boolean WRITE_BENCHMARK_RESULTS_TO_WORKING_DIRECTORY = false;
	private static final boolean CHECK_SIMPLIFICATION_POSSIBILITY = false;
	private static final long TEST_TIMEOUT_MILLISECONDS = 1_000;
	private static final LogLevel LOG_LEVEL = LogLevel.INFO;
	private static final LogLevel LOG_LEVEL_SOLVER = LogLevel.INFO;
	private static final String SOLVER_COMMAND =
			String.format("z3 SMTLIB2_COMPLIANT=true -t:%s -memory:2024 -smt2 -in", TEST_TIMEOUT_MILLISECONDS);

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;
	private static QuantifierEliminationTestCsvWriter mCsvWriter;

	public static Sort getBitvectorSort1(final Script script) {
		return SmtSortUtils.getBitvectorSort(script, 1);
	}

	public static Sort getBitvectorSort8(final Script script) {
		return SmtSortUtils.getBitvectorSort(script, 8);
	}

	public static Sort getBitvectorSort32(final Script script) {
		return SmtSortUtils.getBitvectorSort(script, 32);
	}

	public static Sort getArrayBv32Bv1Sort(final Script script) {
		return SmtSortUtils.getArraySort(script, getBitvectorSort32(script), getBitvectorSort1(script));
	}

	public static Sort getArrayBv32Bv8Sort(final Script script) {
		return SmtSortUtils.getArraySort(script, getBitvectorSort32(script), getBitvectorSort8(script));
	}

	public static Sort getArrayBv32Bv32Sort(final Script script) {
		return SmtSortUtils.getArraySort(script, getBitvectorSort32(script), getBitvectorSort32(script));
	}

	public static Sort getArrayBv32Bv32Bv32Sort(final Script script) {
		return SmtSortUtils.getArraySort(script, getBitvectorSort32(script), getArrayBv32Bv32Sort(script));
	}

	public static Sort getArrayIntBoolSort(final Script script) {
		return SmtSortUtils.getArraySort(script, SmtSortUtils.getIntSort(script), SmtSortUtils.getBoolSort(script));
	}

	public static Sort getArrayIntIntSort(final Script script) {
		return SmtSortUtils.getArraySort(script, SmtSortUtils.getIntSort(script), SmtSortUtils.getIntSort(script));
	}

	public static Sort getArrayIntIntIntSort(final Script script) {
		return SmtSortUtils.getArraySort(script, SmtSortUtils.getIntSort(script),
				SmtSortUtils.getArraySort(script, SmtSortUtils.getIntSort(script), SmtSortUtils.getIntSort(script)));
	}

	@BeforeClass
	public static void beforeAllTests() {
		mCsvWriter = new QuantifierEliminationTestCsvWriter(QuantifierEliminationTest.class.getSimpleName());
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

		final Script solverInstance =
				new HistoryRecordingScript(UltimateMocks.createSolver(SOLVER_COMMAND, LOG_LEVEL_SOLVER));
		if (WRITE_SMT_SCRIPTS_TO_FILE) {
			mScript = new LoggingScript(solverInstance, "QuantifierEliminationTest.smt2", true);
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
	public void prenexQuantifiedCapture() {
		final Term seventeen = mScript.numeral(BigInteger.valueOf(17));
		final Term fourtytwo = mScript.numeral(BigInteger.valueOf(42));
		final TermVariable x = mScript.variable("x", SmtSortUtils.getIntSort(mMgdScript));
		final Term eq1 = mScript.term("=", x, seventeen);
		final Term eq2 = mScript.term("=", x, fourtytwo);
		final Term qeq1 = mScript.quantifier(0, new TermVariable[] { x }, eq1);
		final Term qeq2 = mScript.quantifier(0, new TermVariable[] { x }, eq2);
		final Term term = mScript.term("and", qeq1, qeq2);
		final Term result = new PrenexNormalForm(mMgdScript).transform(term);
		mScript.assertTerm(result);
		final LBool checkSatRes = mScript.checkSat();
		Assert.assertTrue(checkSatRes == LBool.SAT);
	}

	/**
	 * Quantifier elimination use case that comes from using constant arrays to initialize array variables in the C to
	 * Boogie translation. Variant where the helper function is inlined.
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 */
	@Test
	public void constantArrayTest01() {
		mScript.declareFun("a", new Sort[0],
				SmtSortUtils.getArraySort(mScript, SmtSortUtils.getIntSort(mMgdScript), SmtSortUtils.getArraySort(
						mScript, SmtSortUtils.getIntSort(mMgdScript), SmtSortUtils.getIntSort(mMgdScript))));
		mScript.declareFun("i", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));

		final String formulaAsString =
				"(exists ((v_a (Array Int (Array Int Int)))) " + "(= a (store v_a i ((as const (Array Int Int)) 0))))";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		// mLogger.info("Input: " + formulaAsTerm.toStringDirect());
		final Term result = PartialQuantifierElimination.eliminate(mServices, mMgdScript, formulaAsTerm,
				SimplificationTechnique.SIMPLIFY_DDA);
		mLogger.info("Result: " + result.toStringDirect());
		Assert.assertTrue(!(result instanceof QuantifiedFormula));
	}

	/**
	 * Quantifier elimination use case that comes from using constant arrays to initialize array variables in the C to
	 * Boogie translation. Variant where a helper function is used that is defined via define-function. (Perhaps this
	 * makes no difference.)
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 */
	@Test
	public void constantArrayTest02() {
		final Sort arrayFromIntToIntToInt =
				SmtSortUtils.getArraySort(mScript, SmtSortUtils.getIntSort(mMgdScript), SmtSortUtils.getArraySort(
						mScript, SmtSortUtils.getIntSort(mMgdScript), SmtSortUtils.getIntSort(mMgdScript)));

		final String[] paramIds = { "a", "i" };
		final Sort[] paramSorts = new Sort[] { arrayFromIntToIntToInt, SmtSortUtils.getIntSort(mMgdScript) };
		final Sort resultSort = arrayFromIntToIntToInt;
		final String functionDefinitionAsString = "(store a i ((as const (Array Int Int)) 0))";
		final DeclarableFunctionSymbol additionalFunction = DeclarableFunctionSymbol.createFromString(mScript,
				"~initToZeroAtPointerBaseAddress~int", functionDefinitionAsString, paramIds, paramSorts, resultSort);
		additionalFunction.defineOrDeclare(mScript);
		final SmtFunctionsAndAxioms smtSymbols = new SmtFunctionsAndAxioms(mMgdScript);

		mScript.declareFun("b", new Sort[0], arrayFromIntToIntToInt);
		mScript.declareFun("j", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		final String formulaAsString =
				"(exists ((v_a (Array Int (Array Int Int)))) " + "(= b (~initToZeroAtPointerBaseAddress~int v_a j)))";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		mLogger.info("Before inlining: " + formulaAsTerm.toStringDirect());
		final Term inlined = smtSymbols.inline(formulaAsTerm);
		mLogger.info("After inlining : " + inlined.toStringDirect());
		final LBool isDistinct = SmtUtils.checkSatTerm(mScript, mScript.term("distinct", formulaAsTerm, inlined));
		mLogger.info("isDistinct     : " + isDistinct);
		Assert.assertTrue(isDistinct == LBool.UNSAT);
		final Term result = PartialQuantifierElimination.eliminate(mServices, mMgdScript, inlined,
				SimplificationTechnique.SIMPLIFY_DDA);
		mLogger.info("Result         : " + result.toStringDirect());
		Assert.assertTrue(!(result instanceof QuantifiedFormula));
	}

	static void runQuantifierEliminationTest(final FunDecl[] funDecls, final String eliminationInputAsString,
			final String expectedResultAsString, final boolean expectQuantifierFreeResult,
			final IUltimateServiceProvider services, final ILogger logger, final ManagedScript mgdScript,
			final QuantifierEliminationTestCsvWriter csvWriter) {
		for (final FunDecl funDecl : funDecls) {
			funDecl.declareFuns(mgdScript.getScript());
		}
		runQuantifierEliminationTest(eliminationInputAsString, expectedResultAsString, expectQuantifierFreeResult,
				services, logger, mgdScript, csvWriter);
	}

	/**
	 * @deprecated use instead method with argument "FunDecl[] funDecls"
	 */
	@Deprecated
	private static void runQuantifierEliminationTest(final String eliminationInputAsString,
			final String expectedResultAsString, final boolean expectQuantifierFreeResult,
			final IUltimateServiceProvider services, final ILogger logger, final ManagedScript mgdScript,
			final QuantifierEliminationTestCsvWriter csvWriter) {
		final Term formulaAsTerm = TermParseUtils.parseTerm(mgdScript.getScript(), eliminationInputAsString);
		Term letFree = new FormulaUnLet().transform(formulaAsTerm);
		letFree = new CommuhashNormalForm(services, mgdScript.getScript()).transform(letFree);
		letFree = new NnfTransformer(mgdScript, services, QuantifierHandling.KEEP).transform(letFree);
		final String testId = ReflectionUtil.getCallerMethodName(4);
		csvWriter.reportEliminationBegin(letFree, testId);
		final Term result = PartialQuantifierElimination.eliminate(services, mgdScript, letFree,
				SimplificationTechnique.SIMPLIFY_DDA);
		logger.info("Result: " + result);
		if (!Arrays.asList(result.getFreeVars()).isEmpty()) {
			throw new AssertionError("Result contains free vars: " + Arrays.toString(result.getFreeVars()));
		}
		if (CHECK_SIMPLIFICATION_POSSIBILITY) {
			final ExtendedSimplificationResult esr =
					SmtUtils.simplifyWithStatistics(mgdScript, result, services, SimplificationTechnique.SIMPLIFY_DDA);
			logger.info("Simplified result: " + esr.getSimplifiedTerm());
			logger.info(esr.buildSizeReductionMessage());
			if (esr.getReductionOfTreeSize() > 0) {
				throw new AssertionError("Reduction " + esr.getReductionOfTreeSize());
			}
		}
		final boolean resultIsQuantifierFree = QuantifierUtils.isQuantifierFree(result);
		if (expectQuantifierFreeResult) {
			Assert.assertTrue("Result is not quantifier-free ", resultIsQuantifierFree);
		} else {
			Assert.assertTrue("Result is quantifier-free ", !resultIsQuantifierFree);
		}
		if (expectedResultAsString != null) {
			checkLogicalEquivalence(mgdScript.getScript(), result, expectedResultAsString);
		}
		csvWriter.reportEliminationSuccess(result, testId, (StatisticsScript) mgdScript.getScript());
	}

	private static void checkLogicalEquivalence(final Script script, final Term result,
			final String expectedResultAsString) {
		final Term expectedResultAsTerm = TermParseUtils.parseTerm(script, expectedResultAsString);
		script.echo(new QuotedObject("Start correctness check for quantifier elimination."));
		final LBool lbool = SmtUtils.checkEquivalence(result, expectedResultAsTerm, script);
		script.echo(new QuotedObject("Finished correctness check for quantifier elimination. Result: " + lbool));
		final String errorMessage;
		switch (lbool) {
		case SAT:
			errorMessage = "Not equivalent to expected result: " + result;
			break;
		case UNKNOWN:
			errorMessage = "Insufficient ressources for checking equivalence to expected result: " + result;
			break;
		case UNSAT:
			errorMessage = null;
			break;
		default:
			throw new AssertionError("unknown value " + lbool);
		}
		Assert.assertTrue(errorMessage, lbool == LBool.UNSAT);
	}

	@Test
	public void multidimensionalNestedStore() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		final Sort intintintArraySort =
				SmtSortUtils.getArraySort(mScript, intSort, SmtSortUtils.getArraySort(mScript, intSort, intSort));
		mScript.declareFun("v_#memory_int_BEFORE_CALL_2", new Sort[0], intintintArraySort);
		mScript.declareFun("nonMain_~dst~0.base", new Sort[0], intSort);
		mScript.declareFun("v_#Ultimate.C_memcpy_#t~loopctr6_8", new Sort[0], intSort);
		mScript.declareFun("#Ultimate.C_memcpy_dest.offset", new Sort[0], intSort);
		mScript.declareFun("v_prenex_1", new Sort[0], intSort);
		mScript.declareFun("v_#Ultimate.C_memcpy_#t~loopctr6_9", new Sort[0], intSort);
		mScript.declareFun("#Ultimate.C_memcpy_#t~mem7", new Sort[0], intSort);
		mScript.declareFun("#memory_int", new Sort[0], intintintArraySort);
		mScript.declareFun("nonMain_~src~0.base", new Sort[0], intSort);
		mScript.declareFun("nonMain_~src~0.offset", new Sort[0], intSort);
		final String formulaAsString =
				"(store |v_#memory_int_BEFORE_CALL_2| nonMain_~dst~0.base (store (store (select |v_#memory_int_BEFORE_CALL_2| nonMain_~dst~0.base) (+ |v_#Ultimate.C_memcpy_#t~loopctr6_8| |#Ultimate.C_memcpy_dest.offset|) v_prenex_1) (+ |v_#Ultimate.C_memcpy_#t~loopctr6_9| |#Ultimate.C_memcpy_dest.offset|) |#Ultimate.C_memcpy_#t~mem7|))";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		final MultiDimensionalNestedStore mdns = MultiDimensionalNestedStore.of(formulaAsTerm);
		Assert.assertTrue(mdns.getDimension() == 2);
	}

}
