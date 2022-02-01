/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.UnfTransformer;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class SmtUtilsTest {

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;
	private Term mTrue;
	private Term mFalse;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock(LogLevel.DEBUG);
		mScript = UltimateMocks.createZ3Script(LogLevel.INFO);
		mLogger = mServices.getLoggingService().getLogger("lol");
		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);
		mTrue = mScript.term("true");
		mFalse = mScript.term("false");
	}

	@Test
	public void testSubstitutionWithLocalSimplification1() {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);

		final String names = "ABCDE";
		final Term[] values = new Term[] { mScript.term("-", mScript.numeral("1")), mScript.numeral("0"),
				mScript.numeral("2"), mScript.numeral("0"), mScript.numeral("0"), };
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (int i = 0; i < names.length(); ++i) {
			final Term term = declareVar(String.valueOf(names.charAt(i)), intSort);
			if (i < values.length) {
				final Term value = values[i];
				final Term newValue = new UnfTransformer(mScript).transform(value);
				substitutionMapping.put(term, newValue);
			}
		}

		final Term input = TermParseUtils.parseTerm(mScript,
				"(and (<= A E) (or (and (= C 2) (<= D E) (<= B D) (not (= A D))) (= C 1) (and (<= C 1) (not (= C 2)) (not (= C 1)) (= C 3))))");

		final SubstitutionWithLocalSimplification swls =
				new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping);
		final Term result = swls.transform(input);
		final LBool isDistinct = SmtUtils.checkSatTerm(mScript, mScript.term("distinct", mTrue, result));
		final boolean isEqualToTrue = result.equals(mTrue);

		mLogger.info("Original:               " + input.toStringDirect());
		mLogger.info("Witness:                " + substitutionMapping.toString());
		mLogger.info("After Substitution:     " + result.toStringDirect());
		mLogger.info("(distinct true result): " + isDistinct);
		mLogger.info("isEqualToTrue:          " + isEqualToTrue);
		Assert.assertTrue(isDistinct == LBool.UNSAT && isEqualToTrue);
	}

	@Test
	public void testSubstitutionWithLocalSimplification2() {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);

		final String names = "AB";
		final Term[] values = new Term[] { mScript.term("-", mScript.numeral("1")), mScript.numeral("0") };
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (int i = 0; i < names.length(); ++i) {
			final Term term = declareVar(String.valueOf(names.charAt(i)), intSort);
			if (i < values.length) {
				final Term value = values[i];
				final Term newValue = new UnfTransformer(mScript).transform(value);
				substitutionMapping.put(term, newValue);
			}
		}

		final Term input = TermParseUtils.parseTerm(mScript, "(= A B)");

		final SubstitutionWithLocalSimplification swls =
				new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping);
		final Term result = swls.transform(input);
		final LBool isDistinct = SmtUtils.checkSatTerm(mScript, mScript.term("distinct", mFalse, result));
		final boolean isEqualToFalse = result.equals(mFalse);

		mLogger.info("Original:                " + input.toStringDirect());
		mLogger.info("Witness:                 " + substitutionMapping.toString());
		mLogger.info("After Substitution:      " + result.toStringDirect());
		mLogger.info("(distinct false result): " + isDistinct);
		mLogger.info("isEqualToFalse:          " + isEqualToFalse);
		Assert.assertTrue(isDistinct == LBool.UNSAT && isEqualToFalse);
	}

	private Term declareVar(final String name, final Sort sort) {
		mScript.declareFun(name, new Sort[0], sort);
		return mScript.term(name);
	}

	@Test
	public void divRealTest01() {
		final Sort realSort = SmtSortUtils.getRealSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], realSort);
		mScript.declareFun("y", new Sort[0], realSort);
		// check that initial literals are simplified by division
		// check that commutativity is not applied
		// check that intermediate literals are simplified by multiplication
		// check that a non-initial zero cannot be simplified
		final String inputAsString01 = "(/ 10.0 2.0 x 0.0 3.0 5.0 y)";
		final String expectedOutputAsString01 = "(/ 5.0 x 0.0 15.0 y)";
		divRealTest(inputAsString01, expectedOutputAsString01);
		// check that initial zero can be simplified
		// check that intermediate one is dropped
		final String inputAsString02 = "(/ 0.0 2.0 x 1.0 y)";
		final String expectedOutputAsString02 = "(/ 0.0 x y)";
		divRealTest(inputAsString02, expectedOutputAsString02);
		// check that non-integer rationals are represented as binary real
		// divison terms (This is the default representation of SMTInterpol's
		// libraries, we do not want to change that add allow nested
		// division terms for these cases
		final String inputAsString03 = "(/ 7.0 0.5 4.0 x 11.5)";
		final String expectedOutputAsString03 = "(/ (/ 7.0 2.0) x (/ 23.0 2.0))";
		divRealTest(inputAsString03, expectedOutputAsString03);
	}

	@Test
	public void divIntTest01() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], intSort);
		mScript.declareFun("y", new Sort[0], intSort);
		// check that initial literals are simplified by division
		// check that commutativity is not applied
		// check that integrality of literals is kept
		// check that intermediate literals are not simplified by multiplication
		// check that a non-initial zero cannot be simplified
		final String inputAsString01 = "(div 10 2 3 x 0 3 5 y)";
		final String expectedOutputAsString01 = "(div 1 x 0 3 5 y)";
		divIntTest(inputAsString01, expectedOutputAsString01);
		// check that initial zero can be simplified
		// check that intermediate one is dropped
		final String inputAsString02 = "(div 0 2 x 1 y)";
		final String expectedOutputAsString02 = "(div 0 x y)";
		divIntTest(inputAsString02, expectedOutputAsString02);
	}

	private void divRealTest(final String inputAsString, final String expectedOutputAsString) {
		final Term inputAsTerm = TermParseUtils.parseTerm(mScript, inputAsString);
		final Term expectedOutputAsTerm = TermParseUtils.parseTerm(mScript, expectedOutputAsString);
		mLogger.info("Input: " + inputAsTerm);
		final Term outputAsTerm = SmtUtils.divReal(mScript, ((ApplicationTerm) inputAsTerm).getParameters());
		mLogger.info("Output: " + outputAsTerm);
		mLogger.info("Expected output: " + expectedOutputAsTerm);
		final boolean outputIsCorrect = expectedOutputAsTerm.equals(outputAsTerm);
		Assert.assertTrue(outputIsCorrect);
	}

	private void divIntTest(final String inputAsString, final String expectedOutputAsString) {
		final Term inputAsTerm = TermParseUtils.parseTerm(mScript, inputAsString);
		final Term expectedOutputAsTerm = TermParseUtils.parseTerm(mScript, expectedOutputAsString);
		mLogger.info("Input: " + inputAsTerm);
		final Term outputAsTerm = SmtUtils.divInt(mScript, ((ApplicationTerm) inputAsTerm).getParameters());
		mLogger.info("Output: " + outputAsTerm);
		mLogger.info("Expected output: " + expectedOutputAsTerm);
		final boolean outputIsCorrect = expectedOutputAsTerm.equals(outputAsTerm);
		Assert.assertTrue(outputIsCorrect);
	}

	/**
	 * 2019-11-24 Matthias: Small test that triggers the following Exception.
	 *
	 * <pre>
	 * SMTLIBException: Undeclared function symbol (const Int): de.uni_freiburg.informatik.ultimate.logic.NoopScript.term(NoopScript.java:478)]
	 * </pre>
	 */
	@Test
	public void constIntBug() {
		final HistoryRecordingScript hrs = new HistoryRecordingScript(mScript);
		final String inputAsString = "((as const (Array Int Int)) 0)";
		final Term inputAsTerm = TermParseUtils.parseTerm(mScript, inputAsString);
		new TermTransferrer(hrs, hrs, Collections.emptyMap(), true).transform(inputAsTerm);
	}
}
