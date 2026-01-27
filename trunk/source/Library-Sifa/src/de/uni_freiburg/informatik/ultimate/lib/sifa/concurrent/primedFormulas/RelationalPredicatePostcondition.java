package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class RelationalPredicatePostcondition {

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;
	private final PrimedDefaultIcfgSymbolTable mSymbolTable;

	public RelationalPredicatePostcondition(final IUltimateServiceProvider services, final ManagedScript managedScript,
			final BasicPredicateFactory predicateFactory, final PrimedDefaultIcfgSymbolTable symbolTable) {
		mServices = services;
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
		mSymbolTable = symbolTable;
	}

	/**
	 * Computes the strongest postcondition of a state predicate with respect to a relational predicate.
	 *
	 * The state predicate uses unprimed term variables. The relational predicate uses unprimed term variables for
	 * pre-state and primed term variables for post-state.
	 */
	public IPredicate strongestPostcondition(final IPredicate statePredicate, final IPredicate relationalPredicate) {
		// Build projection set and renaming map by inspecting relational predicate variables
		final Set<TermVariable> preVarsToProject = new HashSet<>();
		final Map<Term, Term> primedToUnprimed = new HashMap<>();
		for (final IProgramVar pv : relationalPredicate.getVars()) {
			if (mSymbolTable.isPrimedVar(pv)) {
				// Primed variable: add to renaming map
				final IProgramVar baseVar = mSymbolTable.getBaseVar(pv);
				primedToUnprimed.put(pv.getTermVariable(), baseVar.getTermVariable());
				preVarsToProject.add(baseVar.getTermVariable());
			}
		}

		// Conjoin state predicate with relation predicate
		final Term conjunction = SmtUtils.and(mManagedScript.getScript(), statePredicate.getFormula(),
				relationalPredicate.getFormula());

		// Existentially quantify pre-state variables (only those modified by the relation) and eliminate
		final Term quantified = SmtUtils.quantifier(mManagedScript.getScript(), Script.EXISTS, preVarsToProject,
				conjunction);
		final Term projected = PartialQuantifierElimination.eliminateLight(mServices, mManagedScript, quantified);

		// Rename primed variables back to unprimed term variables
		final Term renamed = Substitution.apply(mManagedScript, primedToUnprimed, projected);
		return mPredicateFactory.newPredicate(renamed);
	}

	public IUltimateServiceProvider getServices() {
		return mServices;
	}

	public ManagedScript getManagedScript() {
		return mManagedScript;
	}

	public BasicPredicateFactory getPredicateFactory() {
		return mPredicateFactory;
	}

	public PrimedDefaultIcfgSymbolTable getSymbolTable() {
		return mSymbolTable;
	}
}
