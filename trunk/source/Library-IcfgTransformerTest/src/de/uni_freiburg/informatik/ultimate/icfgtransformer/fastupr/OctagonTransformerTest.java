/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.icfgtransformer.fastupr;

import java.math.BigDecimal;
import java.util.Set;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.FastUPRUtils;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctConjunction;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctagonDetector;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctagonTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 *
 * This is a basic example for a unit test.
 *
 * You may need some mock classes. Have a look at QuantifiierEliminiationTest in Library-ModelCheckerUtilsTest to see
 * examples for creating {@link IUltimateServiceProvider}, {@link ILogger} and {@link Script} mocks.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class OctagonTransformerTest {

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;
	private FastUPRUtils mUtils;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mLogger = mServices.getLoggingService().getLogger("lol");
		mScript = UltimateMocks.createZ3Script();
		// script = new SMTInterpol();
		mMgdScript = new ManagedScript(mServices, mScript);

		mScript.setLogic(Logics.ALL);
		mUtils = new FastUPRUtils(mLogger, false);
		mLogger.info("Before finished");
	}

	@Test
	public void testDetector() {

		System.out.println("DetectorTest:");
		final OctagonDetector detector = new OctagonDetector(mLogger, mMgdScript, mServices);
		final TermVariable inVarX = mMgdScript.constructFreshTermVariable("xin", mScript.sort("Int"));
		final TermVariable outVarX = mMgdScript.constructFreshTermVariable("yout", mScript.sort("Int"));
		final Term exampleTerm = mScript.term("=", mScript.term("+", inVarX, mScript.decimal(BigDecimal.ONE)), outVarX);
		mUtils.setDetailed(true);
		final Set<Term> octTerms = detector.getConjunctSubTerms(exampleTerm);
		mUtils.setDetailed(false);
		Assert.assertEquals("", octTerms.toString());
	}

	@Test
	public void testTermTransformation() {
		System.out.println("TermTransformationTest:");
		final OctagonDetector detector = new OctagonDetector(mLogger, mMgdScript, mServices);
		final OctagonTransformer transformer =
				new OctagonTransformer(new FastUPRUtils(mLogger, false), mScript, detector);
		final TermVariable inVarX = mMgdScript.constructFreshTermVariable("xin", mScript.sort("Int"));
		final TermVariable outVarX = mMgdScript.constructFreshTermVariable("yout", mScript.sort("Int"));
		final Term exampleTerm = mScript.term("=", mScript.term("+", inVarX, mScript.decimal(BigDecimal.ONE)), outVarX);
		System.out.println("Transform:");
		final OctConjunction example = transformer.transform(exampleTerm);
		System.out.println("Assert:");
		Assert.assertEquals("", example.toString());
	}

	@After
	public void executeAfterEachTest() {
		System.out.println("After");
	}

}
