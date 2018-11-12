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

import java.math.BigInteger;
import java.util.Collections;
import java.util.Map;

import org.eclipse.core.runtime.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class UltimateNormalFormTest {

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;
	private Term mTrue;
	private Term mFalse;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock(LogLevel.DEBUG);
		mScript = UltimateMocks.createZ3Script(LogLevel.INFO);
		mLogger = mServices.getLoggingService().getLogger("lol");
		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);
		mTrue = mScript.term("true");
		mFalse = mScript.term("false");
	}

	@Test
	public void unf01() {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);

		mScript.declareFun("X", new Sort[0], intSort);
		final Term var = mScript.term("X");
		final Term value = mScript.numeral("23");
		final Map<Term, Term> substitutionMapping = Collections.singletonMap(var, value);
		final Term input = TermParseUtils.parseTerm(mScript, "(- X)");

		final Term result = new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping).transform(input);

		final Term expectedResult = Rational.valueOf(-23, 1).toTerm(intSort);
		Assert.isTrue(result.equals(expectedResult));
	}

	@Test
	public void unf02() {
		final Sort realSort = SmtSortUtils.getRealSort(mScript);

		mScript.declareFun("X", new Sort[0], realSort);
		final Term var = mScript.term("X");
		final Term value = mScript.decimal("23.0");
		final Map<Term, Term> substitutionMapping = Collections.singletonMap(var, value);
		final Term input = TermParseUtils.parseTerm(mScript, "(- X)");

		final Term result = new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping).transform(input);

		final Term expectedResult = Rational.valueOf(-23, 1).toTerm(realSort);
		Assert.isTrue(result.equals(expectedResult));
	}

	@Test
	public void unf03() {
		final Sort realSort = SmtSortUtils.getRealSort(mScript);

		mScript.declareFun("a", new Sort[0], realSort);
		mScript.declareFun("X", new Sort[0], realSort);
		final Term var = mScript.term("X");
		final Term value = TermParseUtils.parseTerm(mScript, "(+ a (- 3.0))");
		final Map<Term, Term> substitutionMapping = Collections.singletonMap(var, value);
		final Term input = TermParseUtils.parseTerm(mScript, "(- X)");

		final Term result = new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping).transform(input);

		final Term expectedResult = TermParseUtils.parseTerm(mScript, "(+ (- a) 3.0)");
		mLogger.info("expected result: " + expectedResult);
		mLogger.info("actual   result: " + result);
		Assert.isTrue(result.equals(expectedResult));
	}

	@Test
	public void unf04() {
		mScript.reset();
		mScript.setLogic(Logics.ALL);

		final Sort bv32Sort = SmtSortUtils.getBitvectorSort(mScript, new BigInteger[]{ BigInteger.valueOf(32) });

		mScript.declareFun("X", new Sort[0], bv32Sort);
		final Term var = mScript.term("X");
		final Term value = TermParseUtils.parseTerm(mScript, "(_ bv4294967295 32)");
		final Map<Term, Term> substitutionMapping = Collections.singletonMap(var, value);
		final Term input = TermParseUtils.parseTerm(mScript, "(bvneg X)");

		final Term result = new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping).transform(input);

		final Term expectedResult = TermParseUtils.parseTerm(mScript, "(_ bv1 32)");
		Assert.isTrue(result.equals(expectedResult));
	}

}
