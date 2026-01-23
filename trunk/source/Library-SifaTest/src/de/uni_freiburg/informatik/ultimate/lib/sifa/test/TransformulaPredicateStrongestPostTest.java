package de.uni_freiburg.informatik.ultimate.lib.sifa.test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertThrows;
import static org.junit.Assert.assertTrue;

import java.util.Collections;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.PrimedDefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.TransFormulaToPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * Tests that strongest postcondition via relational predicates matches the standard TransFormula-based approach
 */
public class TransformulaPredicateStrongestPostTest {

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private DefaultIcfgSymbolTable mSymbolTable;
	private BasicPredicateFactory mPredicateFactory;
	private Sort mIntSort;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mScript = new SMTInterpol(new DefaultLogger());
		mScript.setLogic(Logics.ALL);
		mMgdScript = new ManagedScript(mServices, mScript);
		mMgdScript.lock(this);
		mSymbolTable = new DefaultIcfgSymbolTable();
		mPredicateFactory = new BasicPredicateFactory(mServices, mMgdScript, mSymbolTable);
		mIntSort = mScript.sort("Int");
	}

	@After
	public void tearDown() {
		mMgdScript.unlock(this);
		mScript.exit();
	}

	@Test
	public void strongestPostMatchesTransformulaAndRelationalPredicate() {
		// variable x, state predicate x=0, transition x := x + 1
		final ProgramNonOldVar x = createIntVar("x");
		final IPredicate state = predicate(eq(x.getTermVariable(), num(0)));
		final UnmodifiableTransFormula tf = createIncrement(x, 1);

		// Create relational predicate machinery with symbol table
		final var primedTable = new PrimedDefaultIcfgSymbolTable(mSymbolTable, Collections.emptySet(), mMgdScript);
		final var primedFactory = new BasicPredicateFactory(mServices, mMgdScript, primedTable);
		final var translator = new TransFormulaToPredicate(mServices, mMgdScript, primedFactory, primedTable);
		final IPredicate relationPred = translator.translate(tf);

		mMgdScript.unlock(this);

		// Compute StrongestPost both ways (custom with two predicates vs standard predicate + transformula)
		final var transformer = new PredicateTransformer<>(mMgdScript,
				new TermDomainOperationProvider(mServices, mMgdScript));
		final Term spViaTransformula = transformer.strongestPostcondition(state, tf);

		final var relPost = new RelationalPredicatePostcondition(mServices, mMgdScript, mPredicateFactory, primedTable);
		final IPredicate spViaRelation = relPost.strongestPostcondition(state, relationPred);

		mMgdScript.lock(this);

		// Verify equivalence
		assertNotNull(spViaRelation);
		assertTrue(spViaRelation.getVars().contains(x));
		final IPredicate spViaTransformulaPred = mPredicateFactory.newPredicate(spViaTransformula);
		assertEquals(spViaTransformulaPred.getVars(), spViaRelation.getVars());
		assertEquivalent(spViaTransformulaPred.getClosedFormula(), spViaRelation.getClosedFormula());
		assertEquals(SmtUtils.checkEquivalence(spViaTransformulaPred.getClosedFormula(),
				spViaRelation.getClosedFormula(), mScript), LBool.UNSAT);
	}

	@Test
	public void unchangedVariablesPassThrough() {
		// State has x and y, but relation only modifies x
		// Expected: y passes through unchanged
		final ProgramNonOldVar x = createIntVar("x");
		final ProgramNonOldVar y = createIntVar("y");

		// State: x = 5 ∧ y = 10
		final IPredicate state = predicate(SmtUtils.and(mScript,
				eq(x.getTermVariable(), num(5)),
				eq(y.getTermVariable(), num(10))));

		// Relation: x' = x + 1 (only modifies x, y is unchanged)
		final var primedTable = new PrimedDefaultIcfgSymbolTable(mSymbolTable, Collections.emptySet(), mMgdScript);
		final var primedFactory = new BasicPredicateFactory(mServices, mMgdScript, primedTable);
		final TermVariable xPrimed = primedTable.getPrimedVar(x);
		final IPredicate relation = primedFactory.newPredicate(
				eq(xPrimed, mScript.term("+", x.getTermVariable(), num(1))));

		mMgdScript.unlock(this);

		final var relPost = new RelationalPredicatePostcondition(mServices, mMgdScript, mPredicateFactory, primedTable);
		final IPredicate result = relPost.strongestPostcondition(state, relation);

		mMgdScript.lock(this);

		// Expected result: x = 6 ∧ y = 10
		assertNotNull(result);
		assertTrue("Result should contain x", result.getVars().contains(x));
		assertTrue("Result should contain y", result.getVars().contains(y));

		final IPredicate expected = predicate(SmtUtils.and(mScript,
				eq(x.getTermVariable(), num(6)),
				eq(y.getTermVariable(), num(10))));
		assertEquivalent(expected.getClosedFormula(), result.getClosedFormula());
	}

	@Test
	public void unknownVariableInRelationThrowsError() {
		// State only has x, but relation references y (unknown variable)
		final ProgramNonOldVar x = createIntVar("x");
		final ProgramNonOldVar y = createIntVar("y");

		// State: x = 5 (no y)
		final IPredicate state = predicate(eq(x.getTermVariable(), num(5)));

		// Relation: x' = x + y (references y which is not in state)
		final var primedTable = new PrimedDefaultIcfgSymbolTable(mSymbolTable, Collections.emptySet(), mMgdScript);
		final var primedFactory = new BasicPredicateFactory(mServices, mMgdScript, primedTable);
		final TermVariable xPrimed = primedTable.getPrimedVar(x);
		final IPredicate relation = primedFactory.newPredicate(
				eq(xPrimed, mScript.term("+", x.getTermVariable(), y.getTermVariable())));

		mMgdScript.unlock(this);

		final var relPost = new RelationalPredicatePostcondition(mServices, mMgdScript, mPredicateFactory, primedTable);

		assertThrows(IllegalArgumentException.class, () -> {
			relPost.strongestPostcondition(state, relation);
		});

		mMgdScript.lock(this);
	}

	private ProgramNonOldVar createIntVar(final String name) {
		final ProgramNonOldVar var = ProgramVarUtils.constructGlobalProgramVarPair(name, mIntSort, mMgdScript, this);
		mSymbolTable.add(var);
		return var;
	}

	private UnmodifiableTransFormula createIncrement(final ProgramNonOldVar var, final int delta) {
		final TermVariable in = mMgdScript.constructFreshTermVariable(var.getGloballyUniqueId() + "_in", mIntSort);
		final TermVariable out = mMgdScript.constructFreshTermVariable(var.getGloballyUniqueId() + "_out", mIntSort);
		final Term formula = eq(out, mScript.term("+", in, num(delta)));
		final TransFormulaBuilder builder = new TransFormulaBuilder(null, null, true, null, true, null, true);
		builder.addInVar(var, in);
		builder.addOutVar(var, out);
		builder.setFormula(formula);
		builder.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return builder.finishConstruction(mMgdScript);
	}

	private IPredicate predicate(final Term t) {
		return mPredicateFactory.newPredicate(t);
	}

	private Term eq(final Term a, final Term b) {
		return mScript.term("=", a, b);
	}

	private Term num(final int n) {
		return mScript.numeral(String.valueOf(n));
	}

	private void assertEquivalent(final Term a, final Term b) {
		assertEquals(LBool.UNSAT, SmtUtils.checkSatTerm(mScript, SmtUtils.and(mScript, a, SmtUtils.not(mScript, b))));
		assertEquals(LBool.UNSAT, SmtUtils.checkSatTerm(mScript, SmtUtils.and(mScript, b, SmtUtils.not(mScript, a))));
	}
}
