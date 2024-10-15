/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Marcel Rogg
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtilsTest Library.
 *
 * The ULTIMATE TraceCheckerUtilsTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtilsTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtilsTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtilsTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtilsTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.abstraction.IAbstraction;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.BasicInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtParserUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult.BasicRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.SemanticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Base class to test implementations of {@link IAbstraction} and {@link IRefinableAbstraction}.
 *
 * @author Marcel Rogg
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <H>
 *            The type of abstraction levels
 */
public abstract class AbstractAbstractionTestSuite<H> {

	private static final long TEST_TIMEOUT_MILLISECONDS = 10000L;
	private static final LogLevel LOG_LEVEL = LogLevel.INFO;
	private static final String SOLVER_COMMAND = "z3 SMTLIB2_COMPLIANT=true -t:1000 -memory:2024 -smt2 -in";

	protected IUltimateServiceProvider mServices;
	protected Script mScript;
	protected ManagedScript mMgdScript;
	protected final DefaultIcfgSymbolTable mSymbolTable = new DefaultIcfgSymbolTable();

	protected IPredicateUnifier mUnifier;
	protected IHoareTripleChecker mHtc;
	private IIndependenceRelation<IPredicate, BasicInternalAction> mIndependence;

	protected IAbstraction<H, BasicInternalAction> mAbstraction;

	private Sort mIntSort;
	protected IProgramVar x, y;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock(LOG_LEVEL);
		mServices.getProgressMonitorService().setDeadline(System.currentTimeMillis() + TEST_TIMEOUT_MILLISECONDS);
		final ILogger logger = mServices.getLoggingService().getLogger(VariableAbstractionTest.class);

		mScript = new HistoryRecordingScript(UltimateMocks.createSolver(SOLVER_COMMAND, LOG_LEVEL));
		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);
		mIntSort = SmtSortUtils.getIntSort(mScript);

		// generic variables
		x = constructVar("x", "Int");
		y = constructVar("y", "Int");

		// Ingredients to parse formulas and create IPredicates
		final BasicPredicateFactory predicateFactory = new BasicPredicateFactory(mServices, mMgdScript, mSymbolTable);
		mUnifier = new PredicateUnifier(logger, mServices, mMgdScript, predicateFactory, mSymbolTable,
				SimplificationTechnique.SIMPLIFY_DDA);

		// Checking Hoare triples
		final ModifiableGlobalsTable modGlobTab = new ModifiableGlobalsTable(new HashRelation<>());
		final CfgSmtToolkit toolkit =
				new CfgSmtToolkit(modGlobTab, mMgdScript, mSymbolTable, null, null, null, null, null, null);
		mHtc = HoareTripleCheckerUtils.constructEfficientHoareTripleChecker(mServices, HoareTripleChecks.MONOLITHIC,
				toolkit, mUnifier);

		// Independence relation
		mIndependence = new SemanticIndependenceRelation<>(mServices, mMgdScript, false, true);

		mAbstraction = createAbstraction();
	}

	@After
	public void tearDown() {
		mScript.exit();
	}

	protected abstract IAbstraction<H, BasicInternalAction> createAbstraction();

	/*
	 * ****************************************************************************************************************
	 * Code to parse formulas and terms.
	 * ****************************************************************************************************************
	 */

	private IProgramVar constructVar(final String name, final String sort) {
		final IProgramVar variable =
				ProgramVarUtils.constructGlobalProgramVarPair(name, mScript.sort(sort), mMgdScript, null);
		mSymbolTable.add(variable);
		return variable;
	}

	private Term parseWithVariables(final String syntax) {
		final var progVars = suffixVars("");
		final var inVars = suffixVars("_in");
		final var outVars = suffixVars("_out");
		final var auxVars = Set.of(mScript.getTheory().createTermVariable("aux", mIntSort));
		return SmtParserUtils.parseWithVariables(syntax, mServices, mMgdScript,
				DataStructureUtils.union(progVars, inVars, outVars, auxVars));
	}

	private Set<TermVariable> suffixVars(final String suffix) {
		return mSymbolTable.getGlobals().stream().map(
				pv -> mScript.getTheory().createTermVariable(pv.getTermVariable().getName() + suffix, pv.getSort()))
				.collect(Collectors.toSet());
	}

	protected IPredicate pred(final String formula) {
		return mUnifier.getOrConstructPredicate(parseWithVariables(formula));
	}

	/*
	 * ****************************************************************************************************************
	 * Code to create statements.
	 * ****************************************************************************************************************
	 */

	protected BasicInternalAction copyAction(final BasicInternalAction old,
			final UnmodifiableTransFormula newTransformula, final UnmodifiableTransFormula newTransformulaWithBE) {
		assert newTransformulaWithBE == null : "TF with branch encoders should be null";
		return createAction(newTransformula);
	}

	protected BasicInternalAction createAction(final UnmodifiableTransFormula newTransformula) {
		final String procedure = getClass().getSimpleName();
		return new BasicInternalAction(procedure, procedure, newTransformula);
	}

	public UnmodifiableTransFormula yIsXPlusY() {
		return TransFormulaBuilder.constructAssignment(List.of(y),
				List.of(SmtUtils.sum(mScript, mIntSort, x.getTerm(), y.getTerm())), mSymbolTable, mMgdScript);
	}

	public UnmodifiableTransFormula yIsXTimesTwo() {
		return TransFormulaBuilder.constructAssignment(List.of(y), List
				.of(SmtUtils.mul(mScript, mIntSort, x.getTerm(), SmtUtils.constructIntValue(mScript, BigInteger.TWO))),
				mSymbolTable, mMgdScript);
	}

	public UnmodifiableTransFormula xIsXPlusOne() {
		return TransFormulaBuilder.constructAssignment(List.of(x), List
				.of(SmtUtils.sum(mScript, mIntSort, x.getTerm(), SmtUtils.constructIntValue(mScript, BigInteger.ONE))),
				mSymbolTable, mMgdScript);
	}

	public UnmodifiableTransFormula assumeXZero() {
		return TransFormulaBuilder.constructEqualityAssumption(List.of(x),
				List.of(SmtUtils.constructIntValue(mScript, BigInteger.ZERO)), mSymbolTable, mMgdScript);
	}

	public UnmodifiableTransFormula jointHavocXandY() {
		final TermVariable aux = mMgdScript.variable("aux", mIntSort);
		final TermVariable xOut = mMgdScript.variable("x_out", mIntSort);
		final TermVariable yOut = mMgdScript.variable("y_out", mIntSort);

		final Term formula = parseWithVariables("(and (= x_out aux) (= y_out aux))");
		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, true, null, true, null, false);
		tfb.addOutVar(x, xOut);
		tfb.addOutVar(y, yOut);
		tfb.addAuxVar(aux);
		tfb.setFormula(formula);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(mMgdScript);
	}

	/*
	 * ****************************************************************************************************************
	 * Code to create IRefinementEngineResults
	 * ****************************************************************************************************************
	 */

	protected static <E1, E2, E3> Triple<E1, E2, E3> tr(final E1 e1, final E2 e2, final E3 e3) {
		return new Triple<>(e1, e2, e3);
	}

	protected <L extends IAction> IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>>
			makeRefinement(final Triple<IPredicate, L, IPredicate>... triples) {
		final NestedWordAutomaton<L, IPredicate> aut = makeAutomaton(triples);
		final List<QualifiedTracePredicates> predicates = makeTracePredicates(triples);
		return new BasicRefinementEngineResult<>(LBool.UNSAT, aut, null, false, predicates, null, null);
	}

	private <L, S> NestedWordAutomaton<L, S> makeAutomaton(final Triple<S, L, S>... triples) {
		final Set<L> alphabet = Arrays.stream(triples).map(Triple::getSecond).collect(Collectors.toSet());
		final var aut = new NestedWordAutomaton<L, S>(new AutomataLibraryServices(mServices),
				new VpAlphabet<>(alphabet), () -> null);

		final Set<S> states = Stream
				.concat(Arrays.stream(triples).map(Triple::getFirst), Arrays.stream(triples).map(Triple::getThird))
				.collect(Collectors.toSet());
		for (final S state : states) {
			aut.addState(false, false, state);
		}
		for (final var triple : triples) {
			aut.addInternalTransition(triple.getFirst(), triple.getSecond(), triple.getThird());
		}

		return aut;
	}

	private <L extends IAction> List<QualifiedTracePredicates>
			makeTracePredicates(final Triple<IPredicate, L, IPredicate>... triples) {
		return Arrays.stream(triples)
				.map(t -> new QualifiedTracePredicates(
						new TracePredicates(t.getFirst(), t.getThird(), List.of(t.getFirst(), t.getThird())),
						getClass(), false))
				.collect(Collectors.toList());
	}

	/*
	 * ****************************************************************************************************************
	 * Code to run tests
	 * ****************************************************************************************************************
	 */

	protected void testRestriction(final H current, final UnmodifiableTransFormula utf) {
		final BasicInternalAction letter = createAction(utf);

		final H restricted = mAbstraction.restrict(letter, current);
		Assert.assertTrue("Restricted level not less than input level",
				mAbstraction.getHierarchy().compare(restricted, current).isLessOrEqual());

		final UnmodifiableTransFormula abstractionCurrent =
				mAbstraction.abstractLetter(letter, current).getTransformula();
		final UnmodifiableTransFormula abstractionRestricted =
				mAbstraction.abstractLetter(letter, restricted).getTransformula();

		final LBool lessEqual =
				TransFormulaUtils.checkImplication(abstractionCurrent, abstractionRestricted, mMgdScript);
		Assert.assertNotEquals("Restricted abstraction yields non-equivalent result", LBool.SAT, lessEqual);
		final LBool greaterEqual =
				TransFormulaUtils.checkImplication(abstractionRestricted, abstractionCurrent, mMgdScript);
		Assert.assertNotEquals("Restricted abstraction yields non-equivalent result", LBool.SAT, greaterEqual);
	}

	protected void testAbstraction(final UnmodifiableTransFormula utf, final H level) {
		testAbstraction(createAction(utf), level);
	}

	protected void testAbstraction(final BasicInternalAction action, final H level) {
		final UnmodifiableTransFormula abstractedTF = createAndCheckAbstraction(action, level).getTransformula();

		final LBool subset = TransFormulaUtils.checkImplication(abstractedTF, action.getTransformula(), mMgdScript);
		Assert.assertNotEquals("Abstraction was a no-op", LBool.UNSAT, subset);
	}

	protected void testAbstractionDoesNothing(final UnmodifiableTransFormula utf, final H level) {
		testAbstractionDoesNothing(createAction(utf), level);
	}

	protected void testAbstractionDoesNothing(final BasicInternalAction action, final H level) {
		final UnmodifiableTransFormula abstractedTF = createAndCheckAbstraction(action, level).getTransformula();

		final LBool subset = TransFormulaUtils.checkImplication(abstractedTF, action.getTransformula(), mMgdScript);
		Assert.assertNotEquals("Abstraction was expected to be a no-op, but was not", LBool.SAT, subset);
	}

	protected void testWithHoareTriple(final IPredicate pre, final UnmodifiableTransFormula tf, final IPredicate post) {
		final BasicInternalAction concreteAction = createAction(tf);
		final Validity concreteValidity = mHtc.checkInternal(pre, concreteAction, post);
		assert concreteValidity == Validity.VALID : "Could not establish Hoare triple validity before abstraction";

		final BasicInternalAction abstracted =
				createAndCheckAbstraction(concreteAction, computeLevel(tr(pre, concreteAction, post)));
		final Validity abstractedValidity = mHtc.checkInternal(pre, abstracted, post);
		assert abstractedValidity == Validity.VALID : "Abstraction breaks Hoare triple";
	}

	private BasicInternalAction createAndCheckAbstraction(final BasicInternalAction action, final H level) {
		final BasicInternalAction abstracted = mAbstraction.abstractLetter(action, level);
		final UnmodifiableTransFormula abstractedTF = abstracted.getTransformula();

		final LBool superset = TransFormulaUtils.checkImplication(action.getTransformula(), abstractedTF, mMgdScript);
		Assert.assertNotEquals("Abstraction did not create a more abstract transition formula", LBool.SAT, superset);

		return abstracted;
	}

	protected H computeLevel(final Triple<IPredicate, BasicInternalAction, IPredicate>... triples) {
		final var refinable =
				(IRefinableAbstraction<NestedWordAutomaton<BasicInternalAction, IPredicate>, H, BasicInternalAction>) mAbstraction;
		return refinable.refine(mAbstraction.getHierarchy().getTop(), makeRefinement(triples));
	}

	/*
	 * ****************************************************************************************************************
	 * Actual test cases
	 * ****************************************************************************************************************
	 */

	@Test
	public void sameInOutVariableAbstractOnlyLeft() {
		testWithHoareTriple(mUnifier.getTruePredicate(), assumeXZero(), pred("(>= x 0)"));
	}

	@Test
	public void sameInOutVariableAbstractOnlyRight() {
		testWithHoareTriple(pred("(>= x 0)"), yIsXTimesTwo(), pred("(>= y 0)"));
	}
}
