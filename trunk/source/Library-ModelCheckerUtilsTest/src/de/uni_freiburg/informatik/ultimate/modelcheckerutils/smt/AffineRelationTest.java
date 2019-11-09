/*
 * Copyright (C) 2019 Max Barth (Max.Barth95@gmx.de)
 * Copyright (C) 2019 University of Freiburg
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

import java.io.FileNotFoundException;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.NotAffineException;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.polynomial.solve_for_subject.MultiCaseSolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.polynomial.solve_for_subject.MultiCaseSolvedBinaryRelation.Xnf;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * @author Max Barth (Max.Barth95@gmx.de)
 */
public class AffineRelationTest {

	private static final boolean WRITE_SCRIPT_TO_FILE = false;
	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private Sort mRealSort;
	private Sort mIntSort;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mScript = UltimateMocks.createZ3Script(LogLevel.INFO);
		if (WRITE_SCRIPT_TO_FILE) {
			final String file = "AffineRelationTestScript.smt2";
			try {
				mScript = new LoggingScript(mScript, file, true);
			} catch (final FileNotFoundException e) {
				throw new AssertionError("Cannot write script to " + file);
			}
		}
		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);
		mRealSort = SmtSortUtils.getRealSort(mMgdScript);
		mIntSort = SmtSortUtils.getIntSort(mMgdScript);

		declareVar("hi", mIntSort); // lower bound
		declareVar("lo", mIntSort); // upper bound
		declareVar("x", mIntSort); // Subject
		declareVar("y", mIntSort);
		declareVar("z", mIntSort);
		declareVar("b", mIntSort);

	}

	private Term declareVar(final String name, final Sort sort) {
		mScript.declareFun(name, new Sort[0], sort);
		return mScript.term(name);
	}

	@After
	public void tearDown() {
		mScript.exit();
	}

	@Test
	public void relationIntDivDefault() throws NotAffineException {
		final String inputSTR = "(= (+ 7 x) y )";
		testSolveForX(inputSTR);

	}

	@Test
	public void relationIntDivEQ() throws NotAffineException {
		final String inputSTR = "(= (* 7 x) y )";
		testSolveForX(inputSTR);

	}

	@Test
	public void relationIntDivEQ2() throws NotAffineException {
		final String inputSTR = "(= (* 3 x) (* 7 y) )";
		testSolveForX(inputSTR);
	}

	@Test
	public void relationIntDivEQ3() throws NotAffineException {
		final String inputSTR = "(= (* 3 x) (+ (* 7 y) (* 5 z)) )";
		testSolveForX(inputSTR);
	}

	@Test
	public void relationIntDivEQ4() throws NotAffineException {
		final String inputSTR = "(= (* 6 (+ y x)) (* 7 z) )";
		testSolveForX(inputSTR);
	}

	@Test
	public void relationIntDivGEQ() throws NotAffineException {
		final String inputSTR = "(>= (* 3 x) lo )";
		testSolveForX(inputSTR);
	}

	@Test
	public void relationIntDivLEQ() throws NotAffineException {
		final String inputSTR = "(<= (* 3 x) hi )";
		testSolveForX(inputSTR);
	}

	@Test
	public void relationIntDivDISTINCT() throws NotAffineException {
		final String inputSTR = "(not(= (* 3 x) y ))";
		testSolveForX(inputSTR);
	}

	@Test
	public void relationIntDivGREATER() throws NotAffineException {
		final String inputSTR = "(> (* 3 x) lo )";
		testSolveForX(inputSTR);
	}

	@Test
	public void relationIntDivLESS() throws NotAffineException {
		final String inputSTR = "(< (* 4 x) hi )";
		testSolveForX(inputSTR);
	}

	// @Test
	public void relationIntModEq() throws NotAffineException {
		final String inputSTR = "(= (mod x 3) hi )";
		testSolveForXMultiCaseOnly(inputSTR);
	}

	// @Test
	public void relationIntDivEq() throws NotAffineException {
		final String inputSTR = "(= (div x 3) hi )";
		testSolveForXMultiCaseOnly(inputSTR);
	}

	// @Test
	public void relationIntRecModEq() throws NotAffineException {
		final String inputSTR = "(= (mod (mod x 7) 3) hi )";
		testSolveForXMultiCaseOnly(inputSTR);
	}

	// @Test
	public void relationIntDefaultModEq() throws NotAffineException {
		final String inputSTR = "(= (+ (mod (mod y 7) 3)  x) hi )";
		testSolveForXMultiCaseOnly(inputSTR);
	}

	// @Test
	public void relationIntRecDivEq() throws NotAffineException {
		final String inputSTR = "(= (div (div x 7) 3) hi )";
		testSolveForXMultiCaseOnly(inputSTR);
	}

	// @Test
	public void choirNightTrezor01() throws NotAffineException {
		final String inputSTR = "(= (mod (+ (* (mod (+ b 1) 4294967296) 4294967295) x) 4294967296) 1)";
		testSolveForXMultiCaseOnly(inputSTR);
	}


	private void testSolveForX(final String inputAsString) throws NotAffineException {
		final Term inputAsTerm = TermParseUtils.parseTerm(mScript, inputAsString);
		final Term x = TermParseUtils.parseTerm(mScript, "x");
		testSingleCaseSolveForSubject(inputAsTerm, x);
		testMultiCaseSolveForSubject(inputAsTerm, x, Xnf.DNF);
		testMultiCaseSolveForSubject(inputAsTerm, x, Xnf.CNF);
	}

	private void testSolveForXMultiCaseOnly(final String inputAsString) throws NotAffineException {
		final Term inputAsTerm = TermParseUtils.parseTerm(mScript, inputAsString);
		final Term x = TermParseUtils.parseTerm(mScript, "x");
		testMultiCaseSolveForSubject(inputAsTerm, x, Xnf.DNF);
		testMultiCaseSolveForSubject(inputAsTerm, x, Xnf.CNF);
	}

	private void testSingleCaseSolveForSubject(final Term inputAsTerm, final Term x) throws NotAffineException {
		final SolvedBinaryRelation sbr = AffineRelation.convert(mScript, inputAsTerm).solveForSubject(mScript, x);
		Assert.assertTrue(assumptionsImpliesEquality(inputAsTerm, sbr));
	}

	private void testMultiCaseSolveForSubject(final Term inputAsTerm, final Term x, final Xnf xnf)
			throws NotAffineException {
		final MultiCaseSolvedBinaryRelation mcsbr = AffineRelation.convert(mScript, inputAsTerm)
				.solveForSubject(mScript, x, xnf);
		final Term solvedAsTerm = mcsbr.asTerm(mScript);
		Assert.assertTrue(SmtUtils.areFormulasEquivalent(inputAsTerm, solvedAsTerm, mScript));
	}

	private boolean assumptionsImpliesEquality(final Term originalTerm, final SolvedBinaryRelation sbr) {
		if (sbr.getAssumptionsMap().isEmpty()) {
			return SmtUtils.areFormulasEquivalent(sbr.relationToTerm(mScript), originalTerm, mScript);
		} else {
			final Term disJ = SmtUtils.not(mScript, SmtUtils.and(mScript, sbr.getAssumptionsMap().values()));
			final Term impli1 = SmtUtils.or(mScript, disJ, sbr.relationToTerm(mScript));
			final Term impli2 = SmtUtils.or(mScript, disJ, originalTerm);
			return SmtUtils.areFormulasEquivalent(impli1, impli2, mScript);
		}
	}
}