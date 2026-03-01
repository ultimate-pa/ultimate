package de.uni_freiburg.informatik.ultimate.lib.sifa.test;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Collections;
import java.util.Map;
import java.util.Set;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.StringDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.PrimedDefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
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
 * Tests for {@link TransFormulaToInterferencePredicate}.
 */
public class SharedVariableTranslationTest {

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private DefaultIcfgSymbolTable mSymbolTable;
	private Sort mIntSort;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mScript = new SMTInterpol(new DefaultLogger());
		mScript.setLogic(Logics.ALL);
		mMgdScript = new ManagedScript(mServices, mScript);
		mMgdScript.lock(this);
		mSymbolTable = new DefaultIcfgSymbolTable();
		mIntSort = mScript.sort("Int");
	}

	@After
	public void tearDown() {
		mMgdScript.unlock(this);
		mScript.exit();
	}

	@Test
	public void translationUsesCanonicalTermVariables() {
		// One variable, two different transitions
		final ProgramNonOldVar x = createGlobalIntVar("x");
		final UnmodifiableTransFormula tf1 = createIncrement(x, 1);
		final UnmodifiableTransFormula tf2 = createIncrement(x, 2);

		// Translate both
		final var primedTable = new PrimedDefaultIcfgSymbolTable(mSymbolTable, Collections.emptySet(), mMgdScript);
		final var primedFactory = new BasicPredicateFactory(mServices, mMgdScript, primedTable);
		final var translator = new TransFormulaToInterferencePredicate(mServices, mMgdScript, primedFactory,
				primedTable, null);
		final IPredicate rel1 = translator.translateForInterference(tf1, null, null, null);
		final IPredicate rel2 = translator.translateForInterference(tf2, null, null, null);

		// Both should contain the same canonical term variables
		final TermVariable tv_x = x.getTermVariable();
		final TermVariable tv_x_primed = primedTable.getPrimedVar(x);

		assertTrue("rel1 should contain tv_x", containsSubterm(rel1.getFormula(), tv_x));
		assertTrue("rel1 should contain tv_x_primed", containsSubterm(rel1.getFormula(), tv_x_primed));
		assertTrue("rel2 should contain tv_x", containsSubterm(rel2.getFormula(), tv_x));
		assertTrue("rel2 should contain tv_x_primed", containsSubterm(rel2.getFormula(), tv_x_primed));
	}

	@Test
	public void translateToGlobalRemovesLocalVariablesFromTransFormula() {
		// TransFormula: g' = g + 1 with guard l > 0 (global g, local l)
		// After eliminating l, the guard becomes satisfiable, leaving g' = g + 1
		final ProgramNonOldVar g = createGlobalIntVar("g");
		final ILocalProgramVar l = createLocalIntVar("l", "testProc");

		final TermVariable gIn = mMgdScript.constructFreshTermVariable("g_in", mIntSort);
		final TermVariable gOut = mMgdScript.constructFreshTermVariable("g_out", mIntSort);
		final TermVariable lIn = mMgdScript.constructFreshTermVariable("l_in", mIntSort);

		// g' = g + 1 ∧ l > 0
		final Term gUpdate = mScript.term("=", gOut, mScript.term("+", gIn, mScript.numeral("1")));
		final Term lGuard = mScript.term(">", lIn, mScript.numeral("0"));
		final Term formula = mScript.term("and", gUpdate, lGuard);

		final TransFormulaBuilder builder = new TransFormulaBuilder(null, null, true, null, true, null, true);
		builder.addInVar(g, gIn);
		builder.addOutVar(g, gOut);
		builder.addInVar(l, lIn);
		builder.setFormula(formula);
		builder.setInfeasibility(Infeasibility.NOT_DETERMINED);
		final UnmodifiableTransFormula tf = builder.finishConstruction(mMgdScript);

		final var primedTable = new PrimedDefaultIcfgSymbolTable(mSymbolTable, Set.of("testProc"), mMgdScript);
		final var primedFactory = new BasicPredicateFactory(mServices, mMgdScript, primedTable);
		final var translator = new TransFormulaToInterferencePredicate(mServices, mMgdScript, primedFactory,
				primedTable, null);

		mMgdScript.unlock(this);

		// Translate (projects to global)
		final IPredicate globalRelation = translator.translateForInterference(tf, null, null, null);

		mMgdScript.lock(this);

		// Result should contain g and g' but not l
		final TermVariable gPrimed = primedTable.getPrimedVar(g);
		assertTrue("result should contain g", hasVar(globalRelation, g));
		assertTrue("result should contain g'", containsSubterm(globalRelation.getFormula(), gPrimed));
		assertFalse("result should not contain l", hasVar(globalRelation, l));
		// Should not contain the original TransFormula variables either
		assertFalse("result should not contain lIn", containsSubterm(globalRelation.getFormula(), lIn));
	}

	@Test
	public void forkInterferenceIncrementsAffectedCounter() {
		final ProgramNonOldVar x = createGlobalIntVar("x");
		final UnmodifiableTransFormula tf = createIncrement(x, 1);
		final IcfgLocation mainSource = location("main", "mainSource");
		final IcfgLocation mainTarget = location("main", "mainTarget");
		final IcfgLocation workerEntry = location("worker", "workerEntry");

		final var primedTable = new PrimedDefaultIcfgSymbolTable(mSymbolTable, Collections.emptySet(), mMgdScript);
		final var primedFactory = new BasicPredicateFactory(mServices, mMgdScript, primedTable);
		final GhostVariableManager ghostVars = createGhostVariables(
				Map.of(mainSource, 10, mainTarget, 11, workerEntry, 20), Set.of("main", "worker"),
				Map.of("main", mainSource, "worker", workerEntry), primedTable);
		final var translator = new TransFormulaToInterferencePredicate(mServices, mMgdScript, primedFactory,
				primedTable, ghostVars);

		final IPredicate rel = translator.translateForInterferenceWithFork(tf, "main", mainSource, mainTarget, "worker",
				workerEntry);
		final TermVariable workerLoc = ghostVars.getLocationTermVar("worker");
		final TermVariable workerLocPrimed = getPrimedVarFor(workerLoc, primedTable);

		final Term sat = SmtUtils.and(mScript, rel.getFormula(), eq(workerLocPrimed, num(20)));
		final Term unsat = SmtUtils.and(mScript, rel.getFormula(), eq(workerLocPrimed, num(21)));

		assertTrue("fork relation should set worker location to entry",
				SmtUtils.checkSatTerm(mScript, sat) == LBool.SAT);
		assertTrue("fork relation should forbid other worker target locations",
				SmtUtils.checkSatTerm(mScript, unsat) == LBool.UNSAT);
	}

	@Test
	public void nonForkInterferenceKeepsCounterIdentity() {
		final ProgramNonOldVar x = createGlobalIntVar("x");
		final UnmodifiableTransFormula tf = createIncrement(x, 1);
		final IcfgLocation mainSource = location("main", "mainSource");
		final IcfgLocation mainTarget = location("main", "mainTarget");
		final IcfgLocation workerEntry = location("worker", "workerEntry");

		final var primedTable = new PrimedDefaultIcfgSymbolTable(mSymbolTable, Collections.emptySet(), mMgdScript);
		final var primedFactory = new BasicPredicateFactory(mServices, mMgdScript, primedTable);
		final GhostVariableManager ghostVars = createGhostVariables(
				Map.of(mainSource, 10, mainTarget, 11, workerEntry, 20), Set.of("main", "worker"),
				Map.of("main", mainSource, "worker", workerEntry), primedTable);
		final var translator = new TransFormulaToInterferencePredicate(mServices, mMgdScript, primedFactory,
				primedTable, ghostVars);

		final IPredicate rel = translator.translateForInterference(tf, "main", mainSource, mainTarget);
		final TermVariable workerLoc = ghostVars.getLocationTermVar("worker");
		final TermVariable workerLocPrimed = getPrimedVarFor(workerLoc, primedTable);

		final Term sat = SmtUtils.and(mScript, rel.getFormula(), eq(workerLoc, num(2)), eq(workerLocPrimed, num(2)));
		final Term unsat = SmtUtils.and(mScript, rel.getFormula(), eq(workerLoc, num(2)), eq(workerLocPrimed, num(3)));

		assertTrue("non-fork relation should keep worker location unchanged",
				SmtUtils.checkSatTerm(mScript, sat) == LBool.SAT);
		assertTrue("non-fork relation should forbid worker location changes",
				SmtUtils.checkSatTerm(mScript, unsat) == LBool.UNSAT);
	}

	@Test
	public void interferenceRequiresActiveInterferingThread() {
		final ProgramNonOldVar x = createGlobalIntVar("x");
		final UnmodifiableTransFormula tf = createIncrement(x, 1);
		final IcfgLocation mainSource = location("main", "mainSource");
		final IcfgLocation mainTarget = location("main", "mainTarget");
		final IcfgLocation workerEntry = location("worker", "workerEntry");

		final var primedTable = new PrimedDefaultIcfgSymbolTable(mSymbolTable, Collections.emptySet(), mMgdScript);
		final var primedFactory = new BasicPredicateFactory(mServices, mMgdScript, primedTable);
		final GhostVariableManager ghostVars = createGhostVariables(
				Map.of(mainSource, 10, mainTarget, 11, workerEntry, 20), Set.of("main", "worker"),
				Map.of("main", mainSource, "worker", workerEntry), primedTable);
		final var translator = new TransFormulaToInterferencePredicate(mServices, mMgdScript, primedFactory,
				primedTable, ghostVars);

		final IPredicate rel = translator.translateForInterferenceWithFork(tf, "main", mainSource, mainTarget, "worker",
				workerEntry);
		final TermVariable mainLoc = ghostVars.getLocationTermVar("main");

		final Term inactive = SmtUtils.and(mScript, rel.getFormula(), eq(mainLoc, num(0)));
		final Term active = SmtUtils.and(mScript, rel.getFormula(), eq(mainLoc, num(10)));

		assertTrue("inactive interfering thread should not produce interference",
				SmtUtils.checkSatTerm(mScript, inactive) == LBool.UNSAT);
		assertTrue("active interfering thread should be allowed", SmtUtils.checkSatTerm(mScript, active) == LBool.SAT);
	}

	private IcfgLocation location(final String procedure, final String id) {
		return new IcfgLocation(new StringDebugIdentifier(id), procedure);
	}

	private GhostVariableManager createGhostVariables(final Map<IcfgLocation, Integer> locationIds,
			final Set<String> threadIds, final Map<String, IcfgLocation> entryLocations,
			final PrimedDefaultIcfgSymbolTable primedTable) {
		mMgdScript.unlock(this);
		try {
			return GhostVariableManager.create(mMgdScript, locationIds, threadIds, entryLocations, primedTable,
					Set.of(), true);
		} finally {
			mMgdScript.lock(this);
		}
	}

	private static boolean hasVar(final IPredicate pred, final IProgramVar var) {
		return pred.getVars().stream().anyMatch(v -> v.getTermVariable() == var.getTermVariable());
	}

	private static boolean containsSubterm(final Term rootTerm, final Term targetTerm) {
		if (rootTerm == targetTerm) {
			return true;
		}
		if (rootTerm instanceof ApplicationTerm) {
			for (final Term sub : ((ApplicationTerm) rootTerm).getParameters()) {
				if (containsSubterm(sub, targetTerm)) {
					return true;
				}
			}
		}
		return false;
	}

	private ProgramNonOldVar createGlobalIntVar(final String name) {
		final ProgramNonOldVar var = ProgramVarUtils.constructGlobalProgramVarPair(name, mIntSort, mMgdScript, this);
		mSymbolTable.add(var);
		return var;
	}

	private ILocalProgramVar createLocalIntVar(final String name, final String procedure) {
		final ILocalProgramVar var = ProgramVarUtils.constructLocalProgramVar(name, procedure, mIntSort, mMgdScript,
				this);
		mSymbolTable.add(var);
		return var;
	}

	private UnmodifiableTransFormula createIncrement(final ProgramNonOldVar var, final int delta) {
		final TermVariable in = mMgdScript.constructFreshTermVariable(var.getGloballyUniqueId() + "_in", mIntSort);
		final TermVariable out = mMgdScript.constructFreshTermVariable(var.getGloballyUniqueId() + "_out", mIntSort);
		final Term formula = mScript.term("=", out, mScript.term("+", in, mScript.numeral(String.valueOf(delta))));
		final TransFormulaBuilder builder = new TransFormulaBuilder(null, null, true, null, true, null, true);
		builder.addInVar(var, in);
		builder.addOutVar(var, out);
		builder.setFormula(formula);
		builder.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return builder.finishConstruction(mMgdScript);
	}

	private TermVariable getPrimedVarFor(final TermVariable baseTv, final PrimedDefaultIcfgSymbolTable primedTable) {
		final IProgramVar baseVar = primedTable.getAllGlobalBaseVars().stream()
				.filter(v -> v.getTermVariable().equals(baseTv)).findFirst()
				.orElseThrow(() -> new AssertionError("Missing base variable for " + baseTv));
		return primedTable.getPrimedVar(baseVar);
	}

	private Term eq(final Term lhs, final Term rhs) {
		return mScript.term("=", lhs, rhs);
	}

	private Term num(final int value) {
		return mScript.numeral(String.valueOf(value));
	}
}
