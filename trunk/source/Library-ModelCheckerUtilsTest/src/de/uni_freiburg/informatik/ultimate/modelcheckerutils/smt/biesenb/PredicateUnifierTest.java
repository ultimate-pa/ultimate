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
import java.util.Collection;
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
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Scriptor;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * @author Ben Biesenbach (ben.biesenbach@neptun.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class PredicateUnifierTest {

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;
	private TestPredicateFactory mFactory;
	private DefaultIcfgSymbolTable mTable;
	private IProgramNonOldVar mA, mB;
	private BasicPredicateFactory mBasicFactory;
	private Term mZero, mOne, mTwo;

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

		mTable = new DefaultIcfgSymbolTable();
		mA = mFactory.constructProgramVar("a");
		mB = mFactory.constructProgramVar("b");
		mTable.add(mA);
		mTable.add(mB);

		mZero = mScript.numeral(String.valueOf(0));
		mOne = mScript.numeral(String.valueOf(1));
		mTwo = mScript.numeral(String.valueOf(2));

		mBasicFactory = new BasicPredicateFactory(mServices, mMgdScript, mTable, SimplificationTechnique.NONE,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
	}

	@Test
	public void testGetOrConstructPredicateForConjunction() {
		final PredicateUnifier oUnifier = new PredicateUnifier(mServices, mMgdScript, mBasicFactory, mTable,
				SimplificationTechnique.NONE, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		final BPredicateUnifier unifier = new BPredicateUnifier(mServices, mMgdScript, mBasicFactory);

		final Term singleTerm1 = mScript.term("=", mA.getTermVariable(), mOne);
		final Term singleTerm2 = mScript.term(">", mA.getTermVariable(), mZero);
		final Term singleTerm3 = mScript.term("<", mA.getTermVariable(), mTwo);
		final Term singleTerm4 = mScript.term("<", mB.getTermVariable(), mOne);

		final IPredicate pred1 = unifier.getOrConstructPredicate(singleTerm1);
		final IPredicate pred2 = unifier.getOrConstructPredicate(singleTerm2);
		final IPredicate pred3 = unifier.getOrConstructPredicate(singleTerm3);
		final IPredicate pred4 = unifier.getOrConstructPredicate(mScript.term("and", singleTerm1, singleTerm4));

		final IPredicate oPred1 = oUnifier.getOrConstructPredicate(singleTerm1);
		final IPredicate oPred2 = oUnifier.getOrConstructPredicate(singleTerm2);
		final IPredicate oPred3 = oUnifier.getOrConstructPredicate(singleTerm3);
		final IPredicate oPred4 = oUnifier.getOrConstructPredicate(mScript.term("and", singleTerm1, singleTerm4));

		final Collection<IPredicate> collection1 = new HashSet<>();
		collection1.add(pred4);
		collection1.add(pred2);
		collection1.add(pred3);

		final Collection<IPredicate> oCollection1 = new HashSet<>();
		oCollection1.add(oPred4);
		oCollection1.add(oPred2);
		oCollection1.add(oPred3);

		// TODO used following to check for myself - how do I test it right?
		mLogger.info("c: " + unifier.getOrConstructPredicateForConjunction(collection1));
		mLogger.info("c: " + oUnifier.getOrConstructPredicateForConjunction(oCollection1));
	}

	@Test
	public void testGetOrConstructPredicateForDisjunction() {
		final PredicateUnifier oUnifier = new PredicateUnifier(mServices, mMgdScript, mBasicFactory, mTable,
				SimplificationTechnique.NONE, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		final BPredicateUnifier unifier = new BPredicateUnifier(mServices, mMgdScript, mBasicFactory);

		final Term singleTerm1 = mScript.term("=", mA.getTermVariable(), mOne);
		final Term singleTerm2 = mScript.term(">", mA.getTermVariable(), mZero);
		final Term singleTerm3 = mScript.term("=", mA.getTermVariable(), mZero);

		final IPredicate pred1 = unifier.getOrConstructPredicate(singleTerm1);
		final IPredicate pred2 = unifier.getOrConstructPredicate(singleTerm2);
		final IPredicate pred3 = unifier.getOrConstructPredicate(singleTerm3);

		final Collection<IPredicate> collection1 = new HashSet<>();
		collection1.add(pred1);
		collection1.add(pred2);
		collection1.add(pred3);

		// TODO used following to check for myself - how do I test it right?
		mLogger.info(unifier.getOrConstructPredicateForDisjunction(collection1));
	}

	@Test
	public void testCannibalize() {
		final BPredicateUnifier unifier = new BPredicateUnifier(mServices, mMgdScript, mBasicFactory);

		final Term singleTerm1 = mScript.term("=", mA.getTermVariable(), mOne);
		final Term singleTerm2 = mScript.term(">", mA.getTermVariable(), mZero);
		final Term singleTerm3 = mScript.term("<", mA.getTermVariable(), mTwo);
		final Term term1 = mScript.term("and", singleTerm2, singleTerm3);
		final Term term2 = mScript.term("and", singleTerm1, term1, term1);
		final Term term3 = mScript.term("or", singleTerm2, singleTerm3);

		unifier.getOrConstructPredicate(term1);

		final Set<IPredicate> collection1 = unifier.cannibalize(false, term2);

		final Set<IPredicate> collection2 = unifier.cannibalize(false, term3);

		// TODO used following to check for myself - how do I test it right?
		// Assert.assertThat("1", collection1, Is.is(oCollection1));
		// Assert.assertThat("2", collection2, Is.is(oCollection2));
	}

	@Test
	public void testGetOrConstructPredicate() {
		final BPredicateUnifier unifier = new BPredicateUnifier(mServices, mMgdScript, mBasicFactory);
		final BPredicateUnifier unifier2 = new BPredicateUnifier(mServices, mMgdScript, mBasicFactory);

		final Term term1 = mScript.term("=", mA.getTermVariable(), mOne);
		final Term term2 = mScript.term(">", mA.getTermVariable(), mZero);
		final Term term3 = mScript.term("<", mA.getTermVariable(), mTwo);
		final Term term4 = mScript.term("=", mA.getTermVariable(), mTwo);

		final IPredicate pred1 = unifier.getOrConstructPredicate(term1);
		final IPredicate pred2 = unifier.getOrConstructPredicate(term2);
		final IPredicate pred3 = unifier.getOrConstructPredicate(mScript.term("and", term2, term3));
		final IPredicate truePred = unifier.getOrConstructPredicate(mScript.term("or", term2, term3));
		final IPredicate falsePred = unifier.getOrConstructPredicate(mScript.term("and", term1, term4));

		final IPredicate pred4 = unifier2.getOrConstructPredicate(pred1);
		final IPredicate pred5 = unifier2.getOrConstructPredicate(pred3);

		Assert.assertThat("1", pred1.getFormula(), Is.is(term1));
		Assert.assertThat("2", pred2.getFormula(), Is.is(term2));
		Assert.assertThat("3", pred3.getFormula(), Is.is(term1));
		Assert.assertThat("4", truePred, Is.is(unifier.getTruePredicate()));
		Assert.assertThat("5", falsePred, Is.is(unifier.getFalsePredicate()));
		Assert.assertThat("6", pred4.getFormula(), Is.is(term1));
		Assert.assertThat("7", pred5, Is.is(pred4));
	}

	@Test
	public void testIsRepresentative() {

		final PredicateUnifier oUnifier = new PredicateUnifier(mServices, mMgdScript, mBasicFactory, mTable,
				SimplificationTechnique.NONE, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		final BPredicateUnifier unifier = new BPredicateUnifier(mServices, mMgdScript, mBasicFactory);

		final TestPredicate pred1 = pred("=", mA, 1);
		final IPredicate pred2 = unifier.getOrConstructPredicate(pred1);
		final IPredicate oPred2 = oUnifier.getOrConstructPredicate(pred1);
		final TestPredicate pred3 = pred("=", mA, 1);
		final IPredicate pred4 = unifier.getOrConstructPredicate(and(neg(pred(">", mA, 2)), neg(pred("<", mA, 2))));
		final IPredicate oPred4 = oUnifier.getOrConstructPredicate(and(neg(pred(">", mA, 2)), neg(pred("<", mA, 2))));
		final TestPredicate pred5 = and(neg(pred(">", mA, 2)), neg(pred("<", mA, 2)));

		Assert.assertFalse("1", unifier.isRepresentative(pred1));
		Assert.assertThat("2", unifier.isRepresentative(pred1), Is.is(oUnifier.isRepresentative(pred1)));
		Assert.assertTrue("3", unifier.isRepresentative(pred2));
		Assert.assertThat("4", unifier.isRepresentative(pred2), Is.is(oUnifier.isRepresentative(oPred2)));
		Assert.assertFalse("5", unifier.isRepresentative(pred3));
		Assert.assertThat("6", unifier.isRepresentative(pred3), Is.is(oUnifier.isRepresentative(pred3)));
		Assert.assertTrue("7", unifier.isRepresentative(pred4));
		Assert.assertThat("8", unifier.isRepresentative(pred4), Is.is(oUnifier.isRepresentative(oPred4)));
		Assert.assertFalse("9", unifier.isRepresentative(pred5));
		Assert.assertThat("10", unifier.isRepresentative(pred5), Is.is(oUnifier.isRepresentative(pred5)));
	}

	@Test
	public void testSipleGetFunctions() {
		final PredicateUnifier oUnifier = new PredicateUnifier(mServices, mMgdScript, mBasicFactory, mTable,
				SimplificationTechnique.NONE, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		final BPredicateUnifier unifier = new BPredicateUnifier(mServices, mMgdScript, mBasicFactory);

		Assert.assertThat("1", unifier.getTruePredicate().getFormula(), Is.is(mScript.term("true")));
		Assert.assertThat("2", unifier.getTruePredicate().getFormula(),
				Is.is(oUnifier.getTruePredicate().getFormula()));
		Assert.assertThat("3", unifier.getFalsePredicate().getFormula(), Is.is(mScript.term("false")));
		Assert.assertThat("4", unifier.getFalsePredicate().getFormula(),
				Is.is(oUnifier.getFalsePredicate().getFormula()));
		Assert.assertThat("5", unifier.getPredicateFactory(), Is.is(mBasicFactory));
		Assert.assertThat("6", unifier.getPredicateFactory(), Is.is(oUnifier.getPredicateFactory()));
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
