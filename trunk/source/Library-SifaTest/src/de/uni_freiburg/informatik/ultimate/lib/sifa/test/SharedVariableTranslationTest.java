package de.uni_freiburg.informatik.ultimate.lib.sifa.test;

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
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.PrimedDefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.TransFormulaToPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * Tests that TransFormulaToPredicate uses consistent constants for the same program variable across different
 * TransFormulas.
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
	public void translationUsesCanonicalConstants() {
		// One variable, two different transitions
		final ProgramNonOldVar x = createIntVar("x");
		final UnmodifiableTransFormula tf1 = createIncrement(x, 1);
		final UnmodifiableTransFormula tf2 = createIncrement(x, 2);

		// Translate both
		final var primedTable = new PrimedDefaultIcfgSymbolTable(mSymbolTable, Collections.emptySet(), mMgdScript);
		final var primedFactory = new BasicPredicateFactory(mServices, mMgdScript, primedTable);
		final var translator = new TransFormulaToPredicate(mMgdScript, primedFactory);
		final IPredicate rel1 = translator.translate(tf1);
		final IPredicate rel2 = translator.translate(tf2);

		// Both should contain the same canonical constants objects
		final Term c_x = x.getDefaultConstant();
		final Term c_x_primed = x.getPrimedConstant();

		assertTrue("rel1 should contain c_x", containsSubterm(rel1.getFormula(), c_x));
		assertTrue("rel1 should contain c_x_primed", containsSubterm(rel1.getFormula(), c_x_primed));
		assertTrue("rel2 should contain c_x", containsSubterm(rel2.getFormula(), c_x));
		assertTrue("rel2 should contain c_x_primed", containsSubterm(rel2.getFormula(), c_x_primed));
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

	private ProgramNonOldVar createIntVar(final String name) {
		final ProgramNonOldVar var = ProgramVarUtils.constructGlobalProgramVarPair(name, mIntSort, mMgdScript, this);
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
}
