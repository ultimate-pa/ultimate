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
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.hamcrest.core.Is;
import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.services.ToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
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
	private Term mZero, mOne, mTwo, mThree;
	private final boolean useMap = true;

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
		mThree = mScript.numeral(String.valueOf(3));

		mBasicFactory = new BasicPredicateFactory(mServices, mMgdScript, mTable, SimplificationTechnique.NONE,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
	}
	
	@Test
	public void testRestructurePredicateTrie() {
		final PredicateUnifier oUnifier = new PredicateUnifier(mLogger, mServices, mMgdScript, mBasicFactory, mTable,
				SimplificationTechnique.NONE, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		final BPredicateUnifier unifier =
				new BPredicateUnifier(mServices, mLogger, mMgdScript, mBasicFactory, mTable);

		final Term term1 = mScript.term("=", mA.getTermVariable(), mZero);
		final Term term2 = mScript.term("=", mA.getTermVariable(), mOne);
		final Term term3 = mScript.term(">", mA.getTermVariable(), mTwo);
		final Term term4 = mScript.term(">", mA.getTermVariable(), mThree);
		final Term term5 = mScript.term("=", mB.getTermVariable(), mZero);
		final Term term6 = mScript.term("=", mB.getTermVariable(), mOne);
		final Term term7 = mScript.term(">", mB.getTermVariable(), mTwo);
		final Term term8 = mScript.term(">", mB.getTermVariable(), mThree);

		unifier.getOrConstructPredicate(term1);
		oUnifier.getOrConstructPredicate(term1);
		unifier.getOrConstructPredicate(term2);
		oUnifier.getOrConstructPredicate(term2);
		unifier.getOrConstructPredicate(term3);
		oUnifier.getOrConstructPredicate(term3);
		unifier.getOrConstructPredicate(term4);
		oUnifier.getOrConstructPredicate(term4);
		unifier.getOrConstructPredicate(mScript.term("and", term4, term5));
		oUnifier.getOrConstructPredicate(mScript.term("and", term4, term5));
		unifier.getOrConstructPredicate(mScript.term("and", term4, term6));
		oUnifier.getOrConstructPredicate(mScript.term("and", term4, term6));
		unifier.getOrConstructPredicate(mScript.term("and", term4, term7));
		oUnifier.getOrConstructPredicate(mScript.term("and", term4, term7));
		unifier.getOrConstructPredicate(mScript.term("and", term4, term8));
		oUnifier.getOrConstructPredicate(mScript.term("and", term4, term8));

		mLogger.info(unifier.print(true, true));
		mLogger.info(unifier.restructurePredicateTrie());
		// mLogger.info(unifier.print(true, false));
		mLogger.info("B: " + unifier.collectPredicateUnifierStatistics());
		mLogger.info("O: " + oUnifier.collectPredicateUnifierStatistics());
		
		unifier.getOrConstructPredicate(mScript.term("or", term6, term5));
	}

	@Test
	public void testPredicateCoverageChecker() {
		final PredicateUnifier oUnifier = new PredicateUnifier(mLogger, mServices, mMgdScript, mBasicFactory, mTable,
				SimplificationTechnique.NONE, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		final BPredicateUnifier unifier =
				new BPredicateUnifier(mServices, mLogger, mMgdScript, mBasicFactory, mTable);

		final Term singleTerm1 = mScript.term("=", mA.getTermVariable(), mOne);
		final Term singleTerm2 = mScript.term(">", mA.getTermVariable(), mZero);
		final Term singleTerm3 = mScript.term("<", mA.getTermVariable(), mTwo);
		final Term singleTerm4 = mScript.term("<", mB.getTermVariable(), mOne);

		final IPredicate pred1 = unifier.getOrConstructPredicate(singleTerm1);
		final IPredicate pred2 = unifier.getOrConstructPredicate(singleTerm2);
		final IPredicate pred3 = unifier.getOrConstructPredicate(singleTerm3);

		final IPredicate oPred1 = oUnifier.getOrConstructPredicate(singleTerm1);
		final IPredicate oPred2 = oUnifier.getOrConstructPredicate(singleTerm2);
		final IPredicate oPred3 = oUnifier.getOrConstructPredicate(singleTerm3);

		Assert.assertThat("1", unifier.collectPredicateUnifierStatistics().substring(0, 99),
				Is.is(oUnifier.collectPredicateUnifierStatistics().substring(0, 99)));

		unifier.getOrConstructPredicate(singleTerm1);
		oUnifier.getOrConstructPredicate(singleTerm1);
		Assert.assertThat("2", unifier.collectPredicateUnifierStatistics().substring(0, 99),
				Is.is(oUnifier.collectPredicateUnifierStatistics().substring(0, 99)));

		unifier.getOrConstructPredicate(mScript.term("true"));
		oUnifier.getOrConstructPredicate(mScript.term("true"));
		Assert.assertThat("3", unifier.collectPredicateUnifierStatistics().substring(0, 99),
				Is.is(oUnifier.collectPredicateUnifierStatistics().substring(0, 99)));

		unifier.getOrConstructPredicate(mScript.term("and", singleTerm2, singleTerm3));
		oUnifier.getOrConstructPredicate(mScript.term("and", singleTerm2, singleTerm3));
		Assert.assertThat("4", unifier.collectPredicateUnifierStatistics().substring(0, 99),
				Is.is(oUnifier.collectPredicateUnifierStatistics().substring(0, 99)));

		unifier.getOrConstructPredicate(pred3);
		oUnifier.getOrConstructPredicate(oPred3);
		Assert.assertThat("5", unifier.collectPredicateUnifierStatistics().substring(0, 99),
				Is.is(oUnifier.collectPredicateUnifierStatistics().substring(0, 99)));

		unifier.getOrConstructPredicate(oPred3);
		oUnifier.getOrConstructPredicate(pred3);
		Assert.assertThat("6", unifier.collectPredicateUnifierStatistics().substring(0, 99),
				Is.is(oUnifier.collectPredicateUnifierStatistics().substring(0, 99)));

		final Term singleTerm5 = mScript.term("=", mOne, mA.getTermVariable());

		unifier.getOrConstructPredicate(singleTerm5);
		oUnifier.getOrConstructPredicate(singleTerm5);
		Assert.assertThat("6", unifier.collectPredicateUnifierStatistics().substring(0, 99),
				Is.is(oUnifier.collectPredicateUnifierStatistics().substring(0, 99)));

		mLogger.info(oUnifier.collectPredicateUnifierStatistics());
	}

	@Test
	public void testGetOrConstructPredicateForConjunction() {
		final PredicateUnifier oUnifier = new PredicateUnifier(mLogger, mServices, mMgdScript, mBasicFactory, mTable,
				SimplificationTechnique.NONE, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		final BPredicateUnifier unifier =
				new BPredicateUnifier(mServices, mLogger, mMgdScript, mBasicFactory, mTable);

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
		collection1.add(pred2);
		collection1.add(pred3);
		collection1.add(pred4);

		final Collection<IPredicate> oCollection1 = new HashSet<>();
		oCollection1.add(oPred2);
		oCollection1.add(oPred3);
		oCollection1.add(oPred4);

		Assert.assertThat("1", unifier.getOrConstructPredicateForConjunction(collection1).getFormula().toString(),
				Is.is(oUnifier.getOrConstructPredicateForConjunction(oCollection1).getFormula().toString()));
		Assert.assertThat("2", unifier.collectPredicateUnifierStatistics().substring(0, 99),
				Is.is(oUnifier.collectPredicateUnifierStatistics().substring(0, 99)));
	}

	@Test
	public void testGetOrConstructPredicateForDisjunction() {
		final PredicateUnifier oUnifier = new PredicateUnifier(mLogger, mServices, mMgdScript, mBasicFactory, mTable,
				SimplificationTechnique.NONE, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		final BPredicateUnifier unifier =
				new BPredicateUnifier(mServices, mLogger, mMgdScript, mBasicFactory, mTable);

		final Term singleTerm1 = mScript.term("=", mA.getTermVariable(), mTwo);
		final Term singleTerm2 = mScript.term(">", mA.getTermVariable(), mOne);
		final Term singleTerm3 = mScript.term("=", mA.getTermVariable(), mOne);
		final Term singleTerm4 = mScript.term(">", mA.getTermVariable(), mZero);

		final IPredicate pred1 = unifier.getOrConstructPredicate(singleTerm1);
		final IPredicate pred2 = unifier.getOrConstructPredicate(singleTerm2);
		final IPredicate pred3 = unifier.getOrConstructPredicate(singleTerm3);

		final IPredicate oPred1 = oUnifier.getOrConstructPredicate(singleTerm1);
		final IPredicate oPred2 = oUnifier.getOrConstructPredicate(singleTerm2);
		final IPredicate oPred3 = oUnifier.getOrConstructPredicate(singleTerm3);

		final Collection<IPredicate> collection1 = new HashSet<>();
		collection1.add(pred1);
		collection1.add(pred2);
		collection1.add(pred3);

		final Collection<IPredicate> oCollection1 = new HashSet<>();
		oCollection1.add(oPred1);
		oCollection1.add(oPred2);
		oCollection1.add(oPred3);

		Assert.assertThat("1", unifier.getOrConstructPredicateForDisjunction(collection1).getFormula().toString(),
				Is.is(oUnifier.getOrConstructPredicateForDisjunction(oCollection1).getFormula().toString()));

		Assert.assertThat("2", unifier.getOrConstructPredicate(singleTerm4).getFormula().toString(),
				Is.is(oUnifier.getOrConstructPredicate(singleTerm4).getFormula().toString()));

		Assert.assertThat("3", unifier.collectPredicateUnifierStatistics().substring(0, 99),
				Is.is(oUnifier.collectPredicateUnifierStatistics().substring(0, 99)));
	}

	@Test
	public void testCannibalize() {
		final BPredicateUnifier unifier =
				new BPredicateUnifier(mServices, mLogger, mMgdScript, mBasicFactory, mTable);
		final PredicateUnifier oUnifier = new PredicateUnifier(mLogger, mServices, mMgdScript, mBasicFactory, mTable,
				SimplificationTechnique.NONE, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		final Term singleTerm1 = mScript.term("=", mA.getTermVariable(), mOne);
		final Term singleTerm2 = mScript.term(">", mA.getTermVariable(), mZero);
		final Term singleTerm3 = mScript.term("<", mA.getTermVariable(), mTwo);
		final Term term1 = mScript.term("and", singleTerm2, singleTerm3);
		final Term term2 = mScript.term("and", singleTerm1, term1);
		final Term term3 = mScript.term("or", singleTerm2, singleTerm3);

		assertEqualSet("1", unifier.cannibalize(false, term2), oUnifier.cannibalize(false, term2));

		unifier.getOrConstructPredicate(singleTerm1);
		oUnifier.getOrConstructPredicate(singleTerm1);

		assertEqualSet("2", unifier.cannibalize(false, term2), oUnifier.cannibalize(false, term2));
		assertEqualSet("3", unifier.cannibalize(true, term2), oUnifier.cannibalize(true, term2));
		assertEqualSet("4", unifier.cannibalize(false, term1), oUnifier.cannibalize(false, term1));
		assertEqualSet("5", unifier.cannibalize(false, term3), oUnifier.cannibalize(false, term3));
		assertEqualSet("6", unifier.cannibalize(true, term3), oUnifier.cannibalize(true, term3));

		Assert.assertThat("7", unifier.collectPredicateUnifierStatistics().substring(0, 99),
				Is.is(oUnifier.collectPredicateUnifierStatistics().substring(0, 99)));
	}

	@Test
	public void testGetOrConstructPredicate() {
		final PredicateUnifier oUnifier = new PredicateUnifier(mLogger, mServices, mMgdScript, mBasicFactory, mTable,
				SimplificationTechnique.NONE, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		final BPredicateUnifier unifier =
				new BPredicateUnifier(mServices, mLogger, mMgdScript, mBasicFactory, mTable);

		final Term term1 = mScript.term("=", mA.getTermVariable(), mOne);
		final Term term2 = mScript.term(">", mA.getTermVariable(), mZero);
		final Term term3 = mScript.term("<", mA.getTermVariable(), mTwo);
		final Term term4 = mScript.term("=", mA.getTermVariable(), mTwo);

		final IPredicate pred1 = unifier.getOrConstructPredicate(term1);
		final IPredicate oPred1 = oUnifier.getOrConstructPredicate(term1);
		final IPredicate pred2 = unifier.getOrConstructPredicate(term2);
		final IPredicate oPred2 = oUnifier.getOrConstructPredicate(term2);
		final IPredicate pred3 = unifier.getOrConstructPredicate(mScript.term("and", term2, term3));
		final IPredicate oPred3 = oUnifier.getOrConstructPredicate(mScript.term("and", term2, term3));

		final IPredicate truePred = unifier.getOrConstructPredicate(mScript.term("or", term2, term3));
		final IPredicate oTruePred = oUnifier.getOrConstructPredicate(mScript.term("or", term2, term3));
		final IPredicate falsePred = unifier.getOrConstructPredicate(mScript.term("and", term1, term4));
		final IPredicate oFalsePred = oUnifier.getOrConstructPredicate(mScript.term("and", term1, term4));
		final IPredicate truePred2 = unifier.getOrConstructPredicate(mScript.term("true"));
		final IPredicate oTruePred2 = oUnifier.getOrConstructPredicate(mScript.term("true"));

		final IPredicate pred4 = unifier.getOrConstructPredicate(oPred1);
		final IPredicate oPred4 = oUnifier.getOrConstructPredicate(pred1);

		Assert.assertThat("1", pred1.getFormula().toString(), Is.is(oPred1.getFormula().toString()));
		Assert.assertThat("2", pred2.getFormula().toString(), Is.is(oPred2.getFormula().toString()));
		Assert.assertThat("3", pred3.getFormula().toString(), Is.is(oPred3.getFormula().toString()));

		Assert.assertThat("4", truePred.getFormula().toString(), Is.is(oTruePred.getFormula().toString()));
		Assert.assertThat("5", falsePred.getFormula().toString(), Is.is(oFalsePred.getFormula().toString()));
		Assert.assertThat("6", truePred2.getFormula().toString(), Is.is(oTruePred2.getFormula().toString()));
		Assert.assertThat("7", pred4.getFormula().toString(), Is.is(oPred4.getFormula().toString()));

		Assert.assertThat("8", unifier.collectPredicateUnifierStatistics().substring(0, 99),
				Is.is(oUnifier.collectPredicateUnifierStatistics().substring(0, 99)));
	}

	@Test
	public void testIsIntricatePredicate() {
		final PredicateUnifier oUnifier = new PredicateUnifier(mLogger, mServices, mMgdScript, mBasicFactory, mTable,
				SimplificationTechnique.NONE, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		final BPredicateUnifier unifier =
				new BPredicateUnifier(mServices, mLogger, mMgdScript, mBasicFactory, mTable);

		final Term term1 = mScript.term("=", mA.getTermVariable(), mOne);

		final Term termTrue = mScript.term("true");
		final Term termFalse = mScript.term("false");

		final TestPredicate predT = pred("=", mA, 1);

		final IPredicate pred1 = unifier.getOrConstructPredicate(term1);
		final IPredicate oPred1 = oUnifier.getOrConstructPredicate(term1);
		final IPredicate predTrue = unifier.getOrConstructPredicate(termTrue);
		final IPredicate oPredTrue = oUnifier.getOrConstructPredicate(termTrue);
		final IPredicate predFlase = unifier.getOrConstructPredicate(termFalse);
		final IPredicate oPredFalse = oUnifier.getOrConstructPredicate(termFalse);

		Assert.assertThat("1", unifier.isIntricatePredicate(pred1), Is.is(oUnifier.isIntricatePredicate(oPred1)));
		Assert.assertThat("4", unifier.isIntricatePredicate(predTrue), Is.is(oUnifier.isIntricatePredicate(oPredTrue)));
		Assert.assertThat("5", unifier.isIntricatePredicate(predFlase),
				Is.is(oUnifier.isIntricatePredicate(oPredFalse)));
	}

	@Test
	public void testIsRepresentative() {

		final PredicateUnifier oUnifier = new PredicateUnifier(mLogger, mServices, mMgdScript, mBasicFactory, mTable,
				SimplificationTechnique.NONE, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		final BPredicateUnifier unifier =
				new BPredicateUnifier(mServices, mLogger, mMgdScript, mBasicFactory, mTable);

		final TestPredicate pred1 = pred("=", mA, 1);
		final TestPredicate pred2 = pred("=", mA, 1);

		final IPredicate pred3 = unifier.getOrConstructPredicate(pred1);
		final IPredicate oPred3 = oUnifier.getOrConstructPredicate(pred1);

		final IPredicate pred4 = unifier.getOrConstructPredicate(and(neg(pred(">", mA, 2)), neg(pred("<", mA, 2))));
		final IPredicate oPred4 = oUnifier.getOrConstructPredicate(and(neg(pred(">", mA, 2)), neg(pred("<", mA, 2))));

		final TestPredicate pred5 = and(neg(pred(">", mA, 2)), neg(pred("<", mA, 2)));
		final TestPredicate pred6 = and(neg(pred(">", mA, 2)), (pred("<", mA, 2)));
		final IPredicate pred7 = new TestPredicate(mScript.term("true"), new HashSet<>(), mScript);

		Assert.assertThat("1", unifier.isRepresentative(pred1), Is.is(oUnifier.isRepresentative(pred1)));
		Assert.assertThat("2", unifier.isRepresentative(pred2), Is.is(oUnifier.isRepresentative(pred2)));
		Assert.assertThat("3", unifier.isRepresentative(pred3), Is.is(oUnifier.isRepresentative(oPred3)));
		Assert.assertThat("4", unifier.isRepresentative(oPred3), Is.is(oUnifier.isRepresentative(pred3)));
		Assert.assertThat("5", unifier.isRepresentative(pred4), Is.is(oUnifier.isRepresentative(oPred4)));
		Assert.assertThat("6", unifier.isRepresentative(oPred4), Is.is(oUnifier.isRepresentative(pred4)));
		Assert.assertThat("7", unifier.isRepresentative(pred5), Is.is(oUnifier.isRepresentative(pred5)));
		Assert.assertThat("8", unifier.isRepresentative(pred6), Is.is(oUnifier.isRepresentative(pred6)));
		Assert.assertThat("9", unifier.isRepresentative(pred7), Is.is(oUnifier.isRepresentative(pred7)));

		Assert.assertThat("10", unifier.collectPredicateUnifierStatistics().substring(0, 99),
				Is.is(oUnifier.collectPredicateUnifierStatistics().substring(0, 99)));
	}

	@Test
	public void testSipleGetFunctions() {
		final PredicateUnifier oUnifier = new PredicateUnifier(mLogger, mServices, mMgdScript, mBasicFactory, mTable,
				SimplificationTechnique.NONE, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		final BPredicateUnifier unifier =
				new BPredicateUnifier(mServices, mLogger, mMgdScript, mBasicFactory, mTable);

		Assert.assertThat("1", unifier.getTruePredicate().getFormula(),
				Is.is(oUnifier.getTruePredicate().getFormula()));
		Assert.assertThat("2", unifier.getFalsePredicate().getFormula(),
				Is.is(oUnifier.getFalsePredicate().getFormula()));
		Assert.assertThat("3", unifier.getPredicateFactory(), Is.is(oUnifier.getPredicateFactory()));

		Assert.assertThat("4", unifier.collectPredicateUnifierStatistics().substring(0, 99),
				Is.is(oUnifier.collectPredicateUnifierStatistics().substring(0, 99)));
	}

	private String assertEqualSet(final String s, final Set<IPredicate> a, final Set<IPredicate> b) {
		final Set<String> sa = new HashSet<>();
		final Set<String> sb = new HashSet<>();
		a.forEach(p -> sa.add(p.getFormula().toString()));
		b.forEach(p -> sb.add(p.getFormula().toString()));
		Assert.assertThat(s, sa, Is.is(sb));
		return (sa + " = " + sb);
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
