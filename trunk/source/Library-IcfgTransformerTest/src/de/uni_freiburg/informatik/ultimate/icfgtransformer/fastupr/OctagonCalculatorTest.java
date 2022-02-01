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
import java.util.HashMap;
import java.util.Map;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.FastUPRUtils;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctConjunction;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctagonCalculator;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctagonFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.LocalBoogieVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
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
public class OctagonCalculatorTest {

	private IUltimateServiceProvider mServices;
	private Script mZ3;
	private ManagedScript mMgdZ3;
	private ILogger mLogger;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mLogger = mServices.getLoggingService().getLogger("lol");
		mZ3 = UltimateMocks.createZ3Script(LogLevel.INFO);
		mZ3.setLogic(Logics.ALL);
		mMgdZ3 = new ManagedScript(mServices, mZ3);
		mLogger.info("setUp() finished");
	}

	@Test
	public void sequentializeTest() {
		mLogger.debug("SequentializeTest:");
		final OctagonCalculator calc = new OctagonCalculator(new FastUPRUtils(mLogger, false), mMgdZ3);
		final OctConjunction example = new OctConjunction();
		final BoogieVar x = new LocalBoogieVar("x", "x", BoogieType.createPlaceholderType(0),
				mMgdZ3.constructFreshTermVariable("c", mZ3.sort("Int")), (ApplicationTerm) mZ3.term("false"),
				(ApplicationTerm) mZ3.term("false"));
		final BoogieVar y = new LocalBoogieVar("y", "y", BoogieType.createPlaceholderType(0),
				mMgdZ3.constructFreshTermVariable("d", mZ3.sort("Int")), (ApplicationTerm) mZ3.term("false"),
				(ApplicationTerm) mZ3.term("false"));
		final Map<IProgramVar, TermVariable> inVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> outVars = new HashMap<>();
		final TermVariable inVarX = mMgdZ3.constructFreshTermVariable("xin", mZ3.sort("Int"));
		final TermVariable inVarY = mMgdZ3.constructFreshTermVariable("yin", mZ3.sort("Int"));
		final TermVariable outVarX = mMgdZ3.constructFreshTermVariable("xout", mZ3.sort("Int"));
		final TermVariable outVarY = mMgdZ3.constructFreshTermVariable("yout", mZ3.sort("Int"));
		inVars.put(x, inVarX);
		inVars.put(y, inVarY);
		outVars.put(x, outVarX);
		outVars.put(y, outVarY);

		example.addTerm(OctagonFactory.createTwoVarOctTerm(BigDecimal.ONE, inVarX, true, outVarX, false));
		example.addTerm(OctagonFactory.createTwoVarOctTerm(BigDecimal.ONE.negate(), inVarX, false, outVarX, true));
		example.addTerm(OctagonFactory.createOneVarOctTerm(BigDecimal.TEN, inVarY, false));

		final OctConjunction result = calc.sequentialize(example, inVars, outVars, 2);
		System.out.println(result.toString());
		Assert.assertEquals("(-v_xin_1 +v_xout_1 <= 1) and (v_xin_1 -v_xout_1 <= -1) and (2*v_yin_1 <= 10)",
				example.toString());
		Assert.assertEquals("(v_xout_1 -v_xin_1 <= 2) and (-v_xout_1 +v_xin_1 <= -2) and (2*v_yin_1 <= 10)",
				result.toString());
	}

	@Test
	public void binarySequentializeTest() {
		mLogger.debug("BinarySequentializeTest:");
		final OctagonCalculator calc = new OctagonCalculator(new FastUPRUtils(mLogger, false), mMgdZ3);
		final OctConjunction example = new OctConjunction();
		final BoogieVar x = new LocalBoogieVar("x", "x", BoogieType.createPlaceholderType(0),
				mMgdZ3.constructFreshTermVariable("c", mZ3.sort("Int")), (ApplicationTerm) mZ3.term("false"),
				(ApplicationTerm) mZ3.term("false"));
		final BoogieVar y = new LocalBoogieVar("y", "y", BoogieType.createPlaceholderType(0),
				mMgdZ3.constructFreshTermVariable("d", mZ3.sort("Int")), (ApplicationTerm) mZ3.term("false"),
				(ApplicationTerm) mZ3.term("false"));
		final Map<IProgramVar, TermVariable> inVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> outVars = new HashMap<>();
		final TermVariable inVarX = mMgdZ3.constructFreshTermVariable("xin", mZ3.sort("Int"));
		final TermVariable inVarY = mMgdZ3.constructFreshTermVariable("yin", mZ3.sort("Int"));
		final TermVariable outVarX = mMgdZ3.constructFreshTermVariable("xout", mZ3.sort("Int"));
		final TermVariable outVarY = mMgdZ3.constructFreshTermVariable("yout", mZ3.sort("Int"));
		inVars.put(x, inVarX);
		inVars.put(y, inVarY);
		outVars.put(x, outVarX);
		outVars.put(y, outVarY);

		example.addTerm(OctagonFactory.createTwoVarOctTerm(BigDecimal.ONE, inVarX, true, outVarX, false));
		example.addTerm(OctagonFactory.createTwoVarOctTerm(BigDecimal.ONE.negate(), inVarX, false, outVarX, true));
		example.addTerm(OctagonFactory.createOneVarOctTerm(BigDecimal.TEN, inVarY, false));

		calc.getUtils().setDetailed(true);
		calc.getUtils().debug(example.toString());
		final OctConjunction result = calc.binarySequentialize(example, example, inVars, outVars);
		System.out.println(result.toString());
		Assert.assertEquals("(-v_xin_1 +v_xout_1 <= 1) and (v_xin_1 -v_xout_1 <= -1) and (2*v_yin_1 <= 10)",
				example.toString());
		Assert.assertEquals("(v_xout_1 -v_xin_1 <= 2) and (-v_xout_1 +v_xin_1 <= -2) and (2*v_yin_1 <= 10)",
				result.toString());

	}

	@After
	public void executeAfterEachTest() {
		mZ3.exit();
		mLogger.info("--");
	}
}
