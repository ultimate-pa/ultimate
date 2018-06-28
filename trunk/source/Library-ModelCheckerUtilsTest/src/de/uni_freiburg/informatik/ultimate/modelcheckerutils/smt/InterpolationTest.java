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

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtInterpolLogProxyWrapper;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class InterpolationTest {

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mLogger = mServices.getLoggingService().getLogger("lol");
		mScript = new SMTInterpol(new SmtInterpolLogProxyWrapper(mLogger));
		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setOption(":produce-models", true);
		mScript.setOption(":produce-unsat-cores", true);
		mScript.setOption(":produce-interpolants", true);
		mScript.setOption(":interpolant-check-mode", true);
		mScript.setOption(":proof-transformation", "LU");
		mScript.setOption(":array-interpolation", true);
		mScript.setLogic("QF_AUFLIRA");
	}

	@Test
	public void interpolate() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("a", new Sort[0], intSort);
		final String aPartStr = "(= a 1)";

		final String bPartStr = "(= a 2)";

		final Term aPart = TermParseUtils.parseTerm(mScript, aPartStr);
		final Term bPart = TermParseUtils.parseTerm(mScript, bPartStr);

		final Pair<LBool, Term> result = SmtUtils.interpolateBinary(mScript, aPart, bPart);
		mLogger.info(result);
		Assert.assertEquals(LBool.UNSAT, result.getFirst());
	}

}
