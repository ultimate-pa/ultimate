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

import java.math.BigInteger;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
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
public class SmtExample {

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mLogger = mServices.getLoggingService().getLogger("lol");
		mScript = UltimateMocks.createZ3Script();
		mScript.setLogic(Logics.ALL);
		mMgdScript = new ManagedScript(mServices, mScript);
		mLogger.info("setUp() complete");
	}

	@Test
	public void runSmtTest() {
		mLogger.info("runSmtTest()");
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		final TermVariable x = mScript.variable("x", intSort);
		final TermVariable y = mScript.variable("y", intSort);
		final TermVariable k = mScript.variable("k", intSort);
		final Term two = mScript.numeral("2");
		final Term zero = mScript.numeral(BigInteger.ZERO);
		final Term hundrednintysix = mScript.numeral("196");

		final Term first = mScript.term("<=", mScript.term("-", y, x), mScript.term("+", k, two));
		final Term second = mScript.term("<=", mScript.term("-", x, y), mScript.term("-", mScript.term("-", k), two));
		final Term third = mScript.term("<=", mScript.term("*", two, x),
				mScript.term("+", mScript.term("*", mScript.term("-", two), k), hundrednintysix));
		final Term conj = mScript.term("and", first, second, third);

		final Term quantified = mScript.quantifier(QuantifiedFormula.EXISTS, new TermVariable[] { k }, conj);
		final Term isFalseOuter = mScript.term("=", quantified, mScript.term("false"));
		final Term isFalseInner = mScript.quantifier(QuantifiedFormula.EXISTS, new TermVariable[] { k },
				mScript.term("=", conj, mScript.term("false")));
		final Term simplfOuter = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMgdScript,
				isFalseOuter, SimplificationTechnique.SIMPLIFY_DDA,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		final Term simplfInner = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMgdScript,
				isFalseInner, SimplificationTechnique.SIMPLIFY_DDA,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		mLogger.info("Original (in):");
		mLogger.info(isFalseInner.toStringDirect());
		mLogger.info("Simplified (in):");
		mLogger.info(simplfInner.toStringDirect());

		mLogger.info("Original (out):");
		mLogger.info(isFalseOuter.toStringDirect());
		mLogger.info("Simplified (out):");
		mLogger.info(simplfOuter.toStringDirect());
	}

	@After
	public void tearDown() {
		mScript.exit();
		mLogger.info("tearDown() complete");
	}
}
