/*
 * Copyright (C) 2018 Ben Biesenbach (ben.biesenbach@neptun.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.biesenb;

import java.io.IOException;
import java.util.HashSet;
import java.util.Set;

import org.hamcrest.core.Is;
import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.services.ToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Scriptor;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * @author Ben Biesenbach (ben.biesenbach@neptun.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class PredicateTrieTest {

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;
	private TestPredicateFactory mFactory;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock(LogLevel.INFO);
		mLogger = mServices.getLoggingService().getLogger(getClass());
		try {
			mScript = new Scriptor("z3 SMTLIB2_COMPLIANT=true -memory:2024 -smt2 -in", mLogger, mServices,
					new ToolchainStorage(), "z3");
		} catch (final IOException e) {
			throw new AssertionError(e);
		}
		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);
		mFactory = new TestPredicateFactory(mMgdScript);
	}

	@Test
	public void test() {

//		final PredicateTrie<TestPredicate> ptrie = new PredicateTrie<>(mMgdScript);
//		final Set<IProgramVar> vars = new HashSet<>();
//		final IProgramNonOldVar a = mFactory.constructProgramVar("a");
//		final IProgramNonOldVar b = mFactory.constructProgramVar("b");
//		vars.add(a);
//		vars.add(b);
//		final TestPredicate pred1 = pred("=", a, 1);
//		final TestPredicate pred2 = pred("=", a, 1);
//		final TestPredicate pred3 = pred("=", a, 2);
//		final TestPredicate pred4 = pred(">", a, 0);
//		final TestPredicate pred5 = pred(">", a, 1);
//		final TestPredicate pred6 = pred("=", b, 0);
//		final TestPredicate pred7 = and(pred1, pred6);
//
//		final TestPredicate pred8 = and(neg(pred(">", a, 2)), neg(pred("<", a, 2)));
//
//		Assert.assertThat("1", ptrie.unifyPredicate(pred1), Is.is(pred1));
//		Assert.assertThat("2", ptrie.unifyPredicate(pred2), Is.is(pred1));
//		Assert.assertThat("3", ptrie.unifyPredicate(pred3), Is.is(pred3));
//		Assert.assertThat("4", ptrie.unifyPredicate(pred4), Is.is(pred4));
//		Assert.assertThat("5", ptrie.unifyPredicate(pred5), Is.is(pred5));
//		Assert.assertThat("6", ptrie.unifyPredicate(pred6), Is.is(pred6));
//		Assert.assertThat("7", ptrie.unifyPredicate(pred7), Is.is(pred7));
//		Assert.assertThat("8", ptrie.unifyPredicate(pred8), Is.is(pred3));
//
//		mLogger.info("\n" + ptrie.toString());
	}

	private TestPredicate neg(final TestPredicate pred) {
		return mFactory.neg(pred);
	}

	private TestPredicate and(final TestPredicate... preds) {
		return mFactory.and(preds);
	}

	private TestPredicate pred(final String op, final IProgramNonOldVar var, final int value) {
		return mFactory.pred(op, var, value);
	}

	@After
	public void tearDown() {
		mScript.exit();
	}

}
