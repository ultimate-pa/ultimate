package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
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

	public RelationalPredicatePostcondition(final IUltimateServiceProvider services, final ManagedScript managedScript,
			final BasicPredicateFactory predicateFactory) {
		mServices = services;
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
	}

	/**
	 * The state predicate must be over term variables (not constants). The relation predicate is be over constants (c_x
	 * for pre-state, c_x_primed for post-state) created by {@link TransFormulaToPredicate}.
	 */
	public IPredicate strongestPostcondition(final IPredicate statePredicate, final IPredicate relationPredicate,
			final Set<IProgramVar> relationVars) {
		final Map<Term, Term> relationSubstitution = new HashMap<>();
		final Map<IProgramVar, TermVariable> postVarMap = new HashMap<>();
		final Set<TermVariable> preVarsToProject = new HashSet<>();

		// Combine variables from state predicate and relation
		final Set<IProgramVar> allVars = new HashSet<>(statePredicate.getVars());
		allVars.addAll(relationVars);

		// Build substitution: constants → term variables
		for (final IProgramVar pv : allVars) {
			final TermVariable preVar = pv.getTermVariable();
			final TermVariable postVar = mManagedScript.constructFreshTermVariable(pv.getGloballyUniqueId() + "_post",
					preVar.getSort());
			relationSubstitution.put(pv.getDefaultConstant(), preVar);
			relationSubstitution.put(pv.getPrimedConstant(), postVar);
			postVarMap.put(pv, postVar);
			preVarsToProject.add(preVar);
		}

		// Substitute constants in relation predicate with term variables
		final Term substitutedRelation = Substitution.apply(mManagedScript, relationSubstitution,
				relationPredicate.getFormula());

		// Conjoin state predicate with substituted relation
		final Term conjunction = SmtUtils.and(mManagedScript.getScript(), statePredicate.getFormula(),
				substitutedRelation);

		// Existentially quantify pre-state variables and eliminate
		final Term quantified = SmtUtils.quantifier(mManagedScript.getScript(), Script.EXISTS, preVarsToProject,
				conjunction);
		// TODO:
		// Use full elimination (?)
		final Term projected = PartialQuantifierElimination.eliminate(mServices, mManagedScript, quantified,
				SimplificationTechnique.SIMPLIFY_DDA);

		// Rename post variables back to original term variables
		final Map<Term, Term> postToPre = new HashMap<>();
		for (final Map.Entry<IProgramVar, TermVariable> entry : postVarMap.entrySet()) {
			postToPre.put(entry.getValue(), entry.getKey().getTermVariable());
		}
		final Term renamed = Substitution.apply(mManagedScript, postToPre, projected);
		return mPredicateFactory.newPredicate(renamed);
	}

	public IPredicate strongestPostcondition(final IPredicate statePredicate, final TransFormula tf,
			final TransFormulaToPredicate translator) {
		final IPredicate relationPredicate = translator.translate(tf);
		final Set<IProgramVar> relationVars = extractVariables(tf);
		return strongestPostcondition(statePredicate, relationPredicate, relationVars);
	}

	public static Set<IProgramVar> extractVariables(final TransFormula tf) {
		final Set<IProgramVar> vars = new HashSet<>(tf.getInVars().keySet());
		vars.addAll(tf.getOutVars().keySet());
		return vars;
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
}
