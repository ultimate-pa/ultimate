/*
 * Copyright (C) 2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.mapelim.monniaux;

import org.hamcrest.core.Is;
import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 *
 * This is a basic example for a unit test.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class MonniauxMapEliminatorTest {

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;
	private Sort mRealSort;
	private Sort mBoolSort;
	private Sort mIntSort;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mLogger = mServices.getLoggingService().getLogger("lol");
		mScript = UltimateMocks.createZ3Script();
		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);

		mRealSort = SmtSortUtils.getRealSort(mMgdScript);
		mBoolSort = SmtSortUtils.getBoolSort(mMgdScript);
		mIntSort = SmtSortUtils.getIntSort(mMgdScript);

		mLogger.info("Before");
	}

	@Test
	public void testStoreSelectEqualityCollector() {
		mLogger.info("testStoreSelectEqualityCollector");
		mScript.declareFun("a", new Sort[0], SmtSortUtils.getArraySort(mScript, mIntSort, mIntSort));
		mScript.declareFun("i", new Sort[0], mIntSort);

		final String formulaAsString = "(= i (select (store a i i) i))";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		final StoreSelectEqualityCollector sseCollector = new StoreSelectEqualityCollector();
		sseCollector.transform(formulaAsTerm);
		Assert.assertThat(sseCollector.mSelectTerms.size(), Is.is(1));
		Assert.assertThat(sseCollector.mStoreTerms.size(), Is.is(1));
		
		// TBD: Tests for the sets idxD and valD
		
		// TBD: Tests for the sets lowD and highD
	}

	@After
	public void executeAfterEachTest() {
		mScript.exit();
		mLogger.info("After");
	}

}
