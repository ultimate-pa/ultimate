/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
import java.math.BigInteger;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.services.ToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Scriptor;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * Test for reproducing a bug in the partial quantifier elimination for arrays.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class NestedStoreSequenceTest {

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock(LogLevel.DEBUG);
		mLogger = mServices.getLoggingService().getLogger("lol");
		try {
			mScript = new Scriptor("z3 SMTLIB2_COMPLIANT=true -t:5000 -memory:2024 -smt2 -in", mLogger, mServices,
					new ToolchainStorage(), "z3");
		} catch (final IOException e) {
			throw new AssertionError(e);
		}
		// script = new SMTInterpol();
		mMgdScript = new ManagedScript(mServices, mScript);

		mScript.setLogic(Logics.ALL);
	}

	@Test
	public void test0() {

		final Sort bv8 = SmtSortUtils.getBitvectorSort(mScript, new BigInteger[] { BigInteger.valueOf(8) });
		final Sort bv32 = SmtSortUtils.getBitvectorSort(mScript, new BigInteger[] { BigInteger.valueOf(32) });

		mScript.declareFun("idx1", new Sort[0], bv32);
		mScript.declareFun("val", new Sort[0], bv8);

		final String formulaAsString = "(exists ((a (Array (_ BitVec 32) (_ BitVec 8)))) (and (= (store a idx1 (_ bv5 8)) a) (= (select a idx1) val)))";

		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		mLogger.info(formulaAsTerm);
		final Term result = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMgdScript, formulaAsTerm,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		mLogger.info(result);

		final String expectedResultAsString = "(= (_ bv5 8) val)";
		final Term expectedResult = TermParseUtils.parseTerm(mScript, expectedResultAsString);
		Assert.assertTrue(expectedResult.equals(result));

	}

	@Test
	public void test1() {

		final Sort bv8 = SmtSortUtils.getBitvectorSort(mScript, new BigInteger[] { BigInteger.valueOf(8) });
		final Sort bv32 = SmtSortUtils.getBitvectorSort(mScript, new BigInteger[] { BigInteger.valueOf(32) });

		mScript.declareFun("idx1", new Sort[0], bv32);
		mScript.declareFun("idx2", new Sort[0], bv32);
		mScript.declareFun("val", new Sort[0], bv8);

		final String formulaAsString = "(exists ((a (Array (_ BitVec 32) (_ BitVec 8)))) (and (= (store (store a idx1 (_ bv5 8)) idx2 (_ bv0 8)) a) (= (select a idx1) val)))";

		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		mLogger.info(formulaAsTerm);
		final Term result = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMgdScript, formulaAsTerm,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		final String expectedResultAsString = "(and (=> (= idx1 idx2) (= (_ bv0 8) val)) (=> (distinct idx1 idx2) (= (_ bv5 8) val)))";
		final Term expectedResult = TermParseUtils.parseTerm(mScript, expectedResultAsString);

		final boolean resultIsQuantifierFree = QuantifierUtils.isQuantifierFree(result);
		final boolean resultIsEquivalentToExpectedResult = SmtTestUtils.areEquivalent(mScript, result, expectedResult);
		Assert.assertTrue(resultIsQuantifierFree && resultIsEquivalentToExpectedResult);

		mLogger.info(result);
	}

	@Test
	public void test2() {

		final Sort bv8 = SmtSortUtils.getBitvectorSort(mScript, new BigInteger[] { BigInteger.valueOf(8) });
		final Sort bv32 = SmtSortUtils.getBitvectorSort(mScript, new BigInteger[] { BigInteger.valueOf(32) });

		mScript.declareFun("idx1", new Sort[0], bv32);
		mScript.declareFun("idx2", new Sort[0], bv32);
		mScript.declareFun("idx3", new Sort[0], bv32);
		mScript.declareFun("val", new Sort[0], bv8);

		final String formulaAsString = "(exists ((a (Array (_ BitVec 32) (_ BitVec 8)))) (and (= (store (store (store a idx1 (_ bv5 8)) idx2 (_ bv0 8)) idx3 (_ bv23 8)) a) (= (select a idx1) val)))";

		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		mLogger.info(formulaAsTerm);
		final Term result = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMgdScript, formulaAsTerm,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		final String expectedResultAsString = "(and (=> (and (= idx1 idx2) (distinct idx1 idx3)) (= (_ bv0 8) val)) (=> (and (distinct idx1 idx2) (distinct idx1 idx3)) (= (_ bv5 8) val)) (=> (= idx1 idx3) (= (_ bv23 8) val)))";
		final Term expectedResult = TermParseUtils.parseTerm(mScript, expectedResultAsString);

		final boolean resultIsQuantifierFree = QuantifierUtils.isQuantifierFree(result);
		final boolean resultIsEquivalentToExpectedResult = SmtTestUtils.areEquivalent(mScript, result, expectedResult);
		Assert.assertTrue(resultIsQuantifierFree && resultIsEquivalentToExpectedResult);

		mLogger.info(result);
	}

	@Test
	public void test3() {

		final Sort bv8 = SmtSortUtils.getBitvectorSort(mScript, new BigInteger[] { BigInteger.valueOf(8) });
		final Sort bv32 = SmtSortUtils.getBitvectorSort(mScript, new BigInteger[] { BigInteger.valueOf(32) });

		mScript.declareFun("idx1", new Sort[0], bv32);
		mScript.declareFun("idx2", new Sort[0], bv32);
		mScript.declareFun("idx3", new Sort[0], bv32);
		mScript.declareFun("val", new Sort[0], bv8);

		final String formulaAsString = "(not (exists ((a (Array (_ BitVec 32) (_ BitVec 8)))) (and (= (store (store (store a idx1 (_ bv5 8)) idx2 (_ bv0 8)) idx3 (_ bv23 8)) a) (= (select a idx1) val))))";

		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		mLogger.info(formulaAsTerm);
		final Term result = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMgdScript, formulaAsTerm,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		final String expectedResultAsString = "(not (and (=> (and (= idx1 idx2) (distinct idx1 idx3)) (= (_ bv0 8) val)) (=> (and (distinct idx1 idx2) (distinct idx1 idx3)) (= (_ bv5 8) val)) (=> (= idx1 idx3) (= (_ bv23 8) val))))";
		final Term expectedResult = TermParseUtils.parseTerm(mScript, expectedResultAsString);

		final boolean resultIsQuantifierFree = QuantifierUtils.isQuantifierFree(result);
		final boolean resultIsEquivalentToExpectedResult = SmtTestUtils.areEquivalent(mScript, result, expectedResult);
		Assert.assertTrue(resultIsQuantifierFree && resultIsEquivalentToExpectedResult);

		mLogger.info(result);
	}

}
