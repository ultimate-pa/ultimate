package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
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
	 *
	 * Variables in the state predicate that are not mentioned in the relational predicate pass through unchanged.
	 */
	public IPredicate strongestPostcondition(final IPredicate statePredicate, final IPredicate relationalPredicate) {
		final Set<IProgramVar> stateVars = statePredicate.getVars();

		// Build projection set and renaming map by inspecting relational predicate variables
		final Set<TermVariable> preVarsToProject = new HashSet<>();
		final Map<Term, Term> primedToUnprimed = new HashMap<>();
		for (final IProgramVar pv : relationalPredicate.getVars()) {
			if (mSymbolTable.isPrimedVar(pv)) {
				// Primed variable: add to renaming map
				final IProgramVar baseVar = mSymbolTable.getBaseVar(pv);
				primedToUnprimed.put(pv.getTermVariable(), baseVar.getTermVariable());
				preVarsToProject.add(baseVar.getTermVariable());
			} else {
				// Unprimed variable: must be in state predicate
				if (!stateVars.contains(pv)) {
					throw new IllegalArgumentException("Relational predicate references variable " + pv
							+ " which is not in the state predicate");
				}
			}
		}

		// Conjoin state predicate with relation predicate
		final Term conjunction =
				SmtUtils.and(mManagedScript.getScript(), statePredicate.getFormula(), relationalPredicate.getFormula());

		// Existentially quantify pre-state variables (only those modified by the relation) and eliminate
		final Term quantified =
				SmtUtils.quantifier(mManagedScript.getScript(), Script.EXISTS, preVarsToProject, conjunction);
		final Term projected = PartialQuantifierElimination.eliminate(mServices, mManagedScript, quantified,
				SimplificationTechnique.SIMPLIFY_DDA);

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
