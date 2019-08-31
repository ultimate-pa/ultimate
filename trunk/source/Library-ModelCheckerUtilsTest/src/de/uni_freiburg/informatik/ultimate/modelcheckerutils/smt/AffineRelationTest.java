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

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.NotAffineException;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * @author schaetzc@tf.uni-freiburg.de
 */
public class AffineRelationTest {

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private Sort mRealSort;
	private Sort mIntSort;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mScript = UltimateMocks.createZ3Script(LogLevel.INFO);
		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);
		mRealSort = SmtSortUtils.getRealSort(mMgdScript);
		mIntSort = SmtSortUtils.getIntSort(mMgdScript);

		declareVar("hi", mIntSort); // lower bound
		declareVar("lo", mIntSort); // upper bound
		declareVar("x", mIntSort); // Subject
		declareVar("y", mIntSort);
		declareVar("z", mIntSort);

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
		Assert.assertTrue(assumptionsImplyEquality(TermParseUtils.parseTerm(mScript, inputSTR),
				affRelOnLeftHandSide(inputSTR, "x")));

	}

	@Test
	public void relationIntDiv() throws NotAffineException {
		final String inputSTR = "(= (* 7 x) y )";
		Assert.assertTrue(assumptionsImplyEquality(TermParseUtils.parseTerm(mScript, inputSTR),
				affRelOnLeftHandSide(inputSTR, "x")));

	}

	@Test
	public void relationIntDiv2() throws NotAffineException {
		final String inputSTR = "(= (* 3 x) (* 7 y) )";
		Assert.assertTrue(assumptionsImplyEquality(TermParseUtils.parseTerm(mScript, inputSTR),
				affRelOnLeftHandSide(inputSTR, "x")));
	}

	@Test
	public void relationIntDiv3() throws NotAffineException {
		final String inputSTR = "(= (* 3 x) (+ (* 7 y) (* 5 z)) )";
		Assert.assertTrue(assumptionsImplyEquality(TermParseUtils.parseTerm(mScript, inputSTR),
				affRelOnLeftHandSide(inputSTR, "x")));
	}

	@Test
	public void relationIntDiv4() throws NotAffineException {
		// testen 33 für a terminiert nicht
		final String inputSTR = "(= (* 6 (+ y x)) (* 7 z) )";
		Assert.assertTrue(assumptionsImplyEquality(TermParseUtils.parseTerm(mScript, inputSTR),
				affRelOnLeftHandSide(inputSTR, "x")));
	}

	@Test
	public void relationIntDiv51() throws NotAffineException {
		final String inputSTR = "(>= (* 3 x) lo )";
		Assert.assertTrue(assumptionsImplyEquality(TermParseUtils.parseTerm(mScript, inputSTR),
				affRelOnLeftHandSide(inputSTR, "x")));

	}

	@Test
	public void relationIntDiv52() throws NotAffineException {
		final String inputSTR = "(<= (* 3 x) hi )";
		Assert.assertTrue(assumptionsImplyEquality(TermParseUtils.parseTerm(mScript, inputSTR),
				affRelOnLeftHandSide(inputSTR, "x")));

	}

	@Test
	public void relationIntDiv6() throws NotAffineException {
		final String inputSTR = "(not(= (* 3 x) y ))";
		Assert.assertTrue(assumptionsImplyEquality(TermParseUtils.parseTerm(mScript, inputSTR),
				affRelOnLeftHandSide(inputSTR, "x")));

	}

	@Test
	public void relationIntDiv71() throws NotAffineException {
		final String inputSTR = "(> (* 3 x) lo )";
		Assert.assertTrue(assumptionsImplyEquality(TermParseUtils.parseTerm(mScript, inputSTR),
				affRelOnLeftHandSide(inputSTR, "x")));

	}

	@Test
	public void relationIntDiv72() throws NotAffineException {
		final String inputSTR = "(< (* 4 x) hi )";
		Assert.assertTrue(assumptionsImplyEquality(TermParseUtils.parseTerm(mScript, inputSTR),
				affRelOnLeftHandSide(inputSTR, "x")));

	}

	@Test
	public void greaterTIR() throws NotAffineException {
		final String inputSTR = "(exists ((x Int)) 	(and (> (* 7 x) lo ) (> hi x)))";
		final Term outputTERM = parseAndElim(inputSTR);
		Assert.assertTrue(SmtTestUtils.areLogicallyEquivalent(mScript, outputTERM, inputSTR));
		Assert.assertTrue(QuantifierUtils.isQuantifierFree(outputTERM));
	}

	@Test
	public void lessTIR() throws NotAffineException {
		final String inputSTR = "(exists ((x Int)) 	(and (< (* 7 x) hi ) (< lo x)))";
		final Term outputTERM = parseAndElim(inputSTR);
		Assert.assertTrue(
				SmtUtils.areFormulasEquivalent(TermParseUtils.parseTerm(mScript, inputSTR), outputTERM, mScript));
		Assert.assertTrue(QuantifierUtils.isQuantifierFree(outputTERM));

	}

	@Test
	public void greaterEqTIR() throws NotAffineException {
		final String inputSTR = "(forall ((x Int)) 	(or (>= (* 7 x) lo ) (> hi x)))";
		final Term outputTERM = parseAndElim(inputSTR);
		Assert.assertTrue(
				SmtUtils.areFormulasEquivalent(TermParseUtils.parseTerm(mScript, inputSTR), outputTERM, mScript));
		Assert.assertTrue(QuantifierUtils.isQuantifierFree(outputTERM));

	}

	@Test
	public void lessEqTIR() throws NotAffineException {
		final String inputSTR = "(forall ((x Int)) 	(or (<= (* 7 x) hi ) (< lo x)))";
		final Term outputTERM = parseAndElim(inputSTR);
		Assert.assertTrue(
				SmtUtils.areFormulasEquivalent(TermParseUtils.parseTerm(mScript, inputSTR), outputTERM, mScript));
		Assert.assertTrue(QuantifierUtils.isQuantifierFree(outputTERM));

	}

	@Test
	public void greaterTIRNegativeCoef() throws NotAffineException {
		final String inputSTR = "(exists ((x Int)) 	(and (> (* (- 7) x) lo ) (< lo x)))";
		final Term outputTERM = parseAndElim(inputSTR);
		Assert.assertTrue(SmtTestUtils.areLogicallyEquivalent(mScript, outputTERM, inputSTR));
		Assert.assertTrue(QuantifierUtils.isQuantifierFree(outputTERM));

	}

	@Test
	public void lessTIRNegativeCoef() throws NotAffineException {
		final String inputSTR = "(exists ((x Int)) 	(and (< (* (- 7) x) lo ) (> hi x)))";
		final Term outputTERM = parseAndElim(inputSTR);
		Assert.assertTrue(
				SmtUtils.areFormulasEquivalent(TermParseUtils.parseTerm(mScript, inputSTR), outputTERM, mScript));
		Assert.assertTrue(QuantifierUtils.isQuantifierFree(outputTERM));

	}

	@Test
	public void greaterEqTIRNegativeCoef() throws NotAffineException {
		final String inputSTR = "(forall ((x Int)) 	(or (>= (* (- 7) x) lo ) (> x lo)))";
		final Term outputTERM = parseAndElim(inputSTR);
		Assert.assertTrue(
				SmtUtils.areFormulasEquivalent(TermParseUtils.parseTerm(mScript, inputSTR), outputTERM, mScript));
		Assert.assertTrue(QuantifierUtils.isQuantifierFree(outputTERM));

	}

	@Test
	public void lessEqTIRNegativeCoef() throws NotAffineException {
		final String inputSTR = "(forall ((x Int)) 	(or (<= (* (- 7) x) hi ) (> hi x)))";
		final Term outputTERM = parseAndElim(inputSTR);
		Assert.assertTrue(
				SmtUtils.areFormulasEquivalent(TermParseUtils.parseTerm(mScript, inputSTR), outputTERM, mScript));
		Assert.assertTrue(QuantifierUtils.isQuantifierFree(outputTERM));

	}

	public Term parseAndElim(final String formulaAsString) {
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		final Term result = PartialQuantifierElimination.tryToEliminate(mServices, null, mMgdScript, formulaAsTerm,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		return result;
	}

	private SolvedBinaryRelation affRelOnLeftHandSide(final String termAsString, final String varString)
			throws NotAffineException {
		final Term var = TermParseUtils.parseTerm(mScript, varString);
		final SolvedBinaryRelation sbr = AffineRelation
				.convert(mScript, TermParseUtils.parseTerm(mScript, termAsString)).solveForSubject(mScript, var);
		return sbr;
	}

	private boolean assumptionsImplyEquality(final Term originalTerm, final SolvedBinaryRelation sbr) {
		return SmtUtils.areFormulasEquivalent(sbr.relationToTerm(mScript), originalTerm,
				SmtUtils.and(mScript, sbr.getAssumptionsMap().values()), mScript);
	}
}