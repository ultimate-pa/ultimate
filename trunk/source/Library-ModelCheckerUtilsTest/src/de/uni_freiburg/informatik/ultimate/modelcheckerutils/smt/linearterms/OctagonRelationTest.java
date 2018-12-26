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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
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
 * @author schaetzc@tf.uni-freiburg.de
 */
public class OctagonRelationTest {

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

	@Test
	public void testOneVar() {
		Assert.assertEquals("(+x) - (-x) <= 14", octRelAsString("(<= x 7)"));
		Assert.assertEquals("(-x) - (+x) < 14", octRelAsString("(< (- x) 7)"));
		Assert.assertEquals("(+x) - (-x) >= -14", octRelAsString("(>= x (- 7))"));
		Assert.assertEquals("(+x) - (-x) > 14", octRelAsString("(> x 7)"));
		Assert.assertEquals("(+x) - (-x) <= 14/3", octRelAsString("(<= (* 3 x) 7)"));

		Assert.assertEquals("(-a) - (+a) = 5", octRelAsString("(= (- 5) (* a 2))"));
	}

	@Test
	public void testTwoVar() {
		Assert.assertEquals("(+x) - (+y) <= 2", octRelAsString("(<= (- x y) 2)"));
		Assert.assertEquals("(-x) - (+y) < -3", octRelAsString("(< 3.0 (+ x y))"));
		Assert.assertEquals("(+x) - (-y) = 4", octRelAsString("(= (+ (* 3 x) (* 3 y)) 12)"));
		Assert.assertEquals("(-x) - (-y) distinct 4", octRelAsString("(distinct (+ (* x (- 3)) (* 3 y)) 12)"));

		Assert.assertEquals("(+x) - (+y) > 4", octRelAsString("(> (+ x (* (- 3.0) y)) (- 12.0 (* x 2.0)))"));
	}

	@Test
	public void testNoCommonCoefficient() {
		Assert.assertNull(octRelAsString("(<= (+ (* 3 x) (* 4 y)) 5)"));
	}

	@Test
	public void testWrongNumberOfVariables() {
		Assert.assertNull(octRelAsString("(= 1 1)"));
		Assert.assertNull(octRelAsString("(= 0 1)"));
		Assert.assertNull(octRelAsString("(= x x)"));
		Assert.assertNull(octRelAsString("(<= (- x y) z)"));
	}


	/**
	 * 2018-12-25 Matthias: Shows that {@link AffineRelation} does not support
	 * comparison of Int and Real. Support for such comparisons is required by
	 * SMT-LIB but some solvers will not support it and it might get removed form
	 * the standard.
	 */
	public void bugsInAffineRelation() {
		// TODO fix? Z3 allows comparison "Int = Real"
		Assert.assertEquals("(+x) - (+a) = 0", octRelAsString("(= x a)"));
	}

	private String octRelAsString(final String termAsString) {
		try {
			final OctagonRelation octRel = OctagonRelation.from(
					new AffineRelation(mScript, TermParseUtils.parseTerm(mScript, termAsString)));
			return octRel == null ? null : octRel.toString();
		} catch (final NotAffineException nae) {
			throw new IllegalArgumentException("Invalid test case. Term was not affine.", nae);
		}
	}

}
