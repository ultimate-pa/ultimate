/*
 * Copyright (C) 2021 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple;

import java.util.Collections;

import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ConcurrencyInformation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.SmtFunctionsAndAxioms;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.SerialProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class HoareTripleCheckerTest {

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;
	private Term mTrue;
	private Term mFalse;
	private PredicateUnifier mPredicateUnifier;
	private CfgSmtToolkit mCsToolkit;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock(LogLevel.DEBUG);
		mScript = new HistoryRecordingScript(UltimateMocks.createZ3Script(LogLevel.INFO));
		mLogger = mServices.getLoggingService().getLogger("lol");
		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);
		mTrue = mScript.term("true");
		mFalse = mScript.term("false");

		final DefaultIcfgSymbolTable symbolTable = new DefaultIcfgSymbolTable();
		final BasicPredicateFactory predicateFactory = new BasicPredicateFactory(mServices, mMgdScript, symbolTable);
		mPredicateUnifier = new PredicateUnifier(mLogger, mServices, mMgdScript, predicateFactory, symbolTable,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		final ModifiableGlobalsTable modGlobTab = new ModifiableGlobalsTable(new HashRelation<>());
		final IcfgEdgeFactory icfgEdgeFactory = new IcfgEdgeFactory(new SerialProvider());
		final ConcurrencyInformation ci =
				new ConcurrencyInformation(Collections.emptyMap(), Collections.emptyMap(), Collections.emptySet());
		final SmtFunctionsAndAxioms smtFunctionsAndAxioms = new SmtFunctionsAndAxioms(mMgdScript);
		mCsToolkit = new CfgSmtToolkit(modGlobTab, mMgdScript, symbolTable, Collections.emptySet(),
				Collections.emptyMap(), Collections.emptyMap(), icfgEdgeFactory, ci, smtFunctionsAndAxioms);
	}

	@Test
	public void sdHtcTest01() {
		// From
		// Rerun
		// de.uni_freiburg.informatik.ultimate.regressiontest.generic.TerminationRegressionTestSuite.I_lassos_regression_SyntaxSupportConst02.bpl
		// S_lassos_regression_BuchiAutomizerBpl-nonlinear.epf T_lassos_regression_BuchiAutomizerBpl.xml
		// I_lassos_regression_SyntaxSupportConst02.bpl S_lassos_regression_BuchiAutomizerBpl-nonlinear.epf
		// T_lassos_regression_BuchiAutomizerBpl.xml(de.uni_freiburg.informatik.ultimate.regressiontest.generic.TerminationRegressionTestSuite)
		// de.uni_freiburg.informatik.ultimate.test.UltimateTestFailureException: ExpectedResult: TERMINATING
		// UltimateResult: EXCEPTION_OR_ERROR [de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer:
		// AssertionError: HoareTripleChecker results differ between SdHoareTripleChecker (result: INVALID) and
		// MonolithicHoareTripleChecker (result: VALID):
		// de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.ChainingHoareTripleChecker$ReviewedProtectedHtc.createAssertionError(ChainingHoareTripleChecker.java:367)]
		//
		// at de.uni_freiburg.informatik.ultimate.test.test(UltimateTestCase.java)
		//
		//
		//

		// {34#(and (>= oldRank0 (+ (* 2 x) 1)) (>= (+ (- 1) c) 0))}
		// assume x >= 0;x := x - c;
		// {36#(and (or unseeded (and (>= oldRank0 0) (> oldRank0 (+ (* 2 x) 1)))) (>= (+ (- 1) c) 0))}

		new SdHoareTripleChecker(mCsToolkit, mPredicateUnifier);
	}

}
