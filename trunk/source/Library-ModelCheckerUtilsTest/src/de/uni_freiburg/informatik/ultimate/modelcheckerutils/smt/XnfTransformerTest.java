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

import org.eclipse.core.runtime.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PrenexNormalForm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class XnfTransformerTest {

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock(LogLevel.DEBUG);
		mLogger = mServices.getLoggingService().getLogger("lol");
		mScript =
				UltimateMocks.createSolver("z3 SMTLIB2_COMPLIANT=true -t:5000 -memory:2024 -smt2 -in", LogLevel.DEBUG);
		mMgdScript = new ManagedScript(mServices, mScript);

		mScript.setLogic(Logics.ALL);
	}

	@Test
	public void testNnf() {

		final Sort boolSort = SmtSortUtils.getBoolSort(mScript);
		final Sort intSort = SmtSortUtils.getIntSort(mScript);

		mScript.declareFun("myfun", new Sort[] { intSort, intSort }, boolSort);
		final String formula = "(exists ((k Int)) (= (not (= 0 k)) (= 1 k)))";

		final Term input = TermParseUtils.parseTerm(mScript, formula);
		final Term negInput = SmtUtils.not(mScript, input);

		toPnf(input);
		toPnf(negInput);
		Assert.isTrue(true);
	}

	private Term toPnf(final Term t) {
		mLogger.info("ORG: " + t);
		final Term nnf = new NnfTransformer(mMgdScript, mServices, QuantifierHandling.KEEP, true).transform(t);
		mLogger.info("NNF:" + nnf);
		final Term pnf = new PrenexNormalForm(mMgdScript).transform(nnf);
		mLogger.info("PNF:" + pnf);
		return pnf;

	}

}
