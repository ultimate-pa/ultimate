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
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.NotAffineException;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
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

		declareVar("a", mIntSort);
		declareVar("b", mIntSort);
		declareVar("c", mIntSort);
		declareVar("x", mRealSort);
		declareVar("y", mRealSort);
		declareVar("z", mRealSort);

	}

	private Term declareVar(final String name, final Sort sort) {
		mScript.declareFun(name, new Sort[0], sort);
		return mScript.term(name);
	}

	@After
	public void tearDown() {
		mScript.exit();
	}
	// TODO write tests for quantifier elimination

	@Test
	public void relationIntDivDefault() throws NotAffineException {
		final String inputSTR = "(= (+ 3 a) b )";
		Assert.assertTrue(assumptionImpliesEquality(TermParseUtils.parseTerm(mScript, inputSTR),
				affRelOnLeftHandSide(inputSTR, "a")));

	}

	@Test
	public void relationIntDiv() throws NotAffineException {
		final String inputSTR = "(= (* 3 a) b )";
		Assert.assertTrue(assumptionImpliesEquality(TermParseUtils.parseTerm(mScript, inputSTR),
				affRelOnLeftHandSide(inputSTR, "a")));

	}

	@Test
	public void relationIntDiv2() throws NotAffineException {
		final String inputSTR = "(= (* 3 a) (* 7 b) )";
		Assert.assertTrue(assumptionImpliesEquality(TermParseUtils.parseTerm(mScript, inputSTR),
				affRelOnLeftHandSide(inputSTR, "a")));
	}

	@Test
	public void relationIntDiv3() throws NotAffineException {
		final String inputSTR = "(= (* 3 a) (+ (* 7 b) (* 5 c)) )";
		Assert.assertTrue(assumptionImpliesEquality(TermParseUtils.parseTerm(mScript, inputSTR),
				affRelOnLeftHandSide(inputSTR, "a")));
	}

	@Test
	public void relationIntDiv4() throws NotAffineException {
		final String inputSTR = "(= (* 6 (+ 33 a)) (* 7 b) )";
		Assert.assertTrue(assumptionImpliesEquality(TermParseUtils.parseTerm(mScript, inputSTR),
				affRelOnLeftHandSide(inputSTR, "a")));
	}

	@Test
	public void relationIntDiv51() throws NotAffineException {
		final String inputSTR = "(>= (* 3 a) b )";
		Assert.assertTrue(assumptionImpliesEquality(TermParseUtils.parseTerm(mScript, inputSTR),
				affRelOnLeftHandSide(inputSTR, "a")));

	}

	@Test
	public void relationIntDiv52() throws NotAffineException {
		final String inputSTR = "(<= (* 3 a) b )";
		Assert.assertTrue(assumptionImpliesEquality(TermParseUtils.parseTerm(mScript, inputSTR),
				affRelOnLeftHandSide(inputSTR, "a")));

	}

	@Test
	public void relationIntDiv6() throws NotAffineException {
		final String inputSTR = "(not(= (* 3 a) b ))";
		Assert.assertTrue(assumptionImpliesEquality(TermParseUtils.parseTerm(mScript, inputSTR),
				affRelOnLeftHandSide(inputSTR, "a")));

	}

	@Test
	public void relationIntDiv71() throws NotAffineException {
		final String inputSTR = "(> (* 3 a) b )";
		Assert.assertTrue(assumptionImpliesEquality(TermParseUtils.parseTerm(mScript, inputSTR),
				affRelOnLeftHandSide(inputSTR, "a")));

	}

	@Test
	public void relationIntDiv72() throws NotAffineException {
		final String inputSTR = "(< (* 4 a) b )";
		Assert.assertTrue(assumptionImpliesEquality(TermParseUtils.parseTerm(mScript, inputSTR),
				affRelOnLeftHandSide(inputSTR, "a")));

	}

	private SolvedBinaryRelation affRelOnLeftHandSide(final String termAsString, final String varString)
			throws NotAffineException {
		final Term var = TermParseUtils.parseTerm(mScript, varString);
		final SolvedBinaryRelation sbr = AffineRelation
				.convert(mScript, TermParseUtils.parseTerm(mScript, termAsString)).nEWonLeftHandSideOnly(mScript, var);
		return sbr;
	}

	private boolean assumptionImpliesEquality(final Term originalTerm, final SolvedBinaryRelation sbr) {
		Term impli1 = sbr.relationToTerm(mScript);
		Term impli2 = originalTerm;
		if (sbr.getAdditionalAssumption() != null) {
			impli1 = SmtUtils.implies(mScript, sbr.getAdditionalAssumption(), sbr.relationToTerm(mScript));
			impli2 = SmtUtils.implies(mScript, sbr.getAdditionalAssumption(), originalTerm);
		}
		Term comp = mScript.term("=", impli1, impli2);
		comp = mScript.term("not", comp);
		final LBool sat = Util.checkSat(mScript, comp);
		if (sat == LBool.UNSAT) {
			return true;
		} else {
			return false;
		}

	}

}