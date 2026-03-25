package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition.PreparedRelation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats.Key;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Single-pass relational SP with equality substitution shortcut (QE fallback for remaining vars).
 * Convergence via outer fixpoint; avoids the compounding cost of an inner fixpoint loop.
 */
public final class RelationalLightInterferenceApplicator implements IInterferenceApplicator {

	private final RelationalPredicatePostcondition mPostcondition;
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;

	public RelationalLightInterferenceApplicator(final RelationalPredicatePostcondition postcondition,
			final IUltimateServiceProvider services, final ManagedScript managedScript,
			final BasicPredicateFactory predicateFactory) {
		mPostcondition = postcondition;
		mServices = services;
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
	}

	@Override
	public IPredicate apply(final IPredicate state, final Collection<GuardedPredicate> predicates, final IDomain domain,
			final int wideningThreshold, final SifaStats stats) {
		final var effects = predicates.stream().map(GuardedPredicate::effect).toList();
		final var preparedRelations = InterferenceUtils.prepareNonFalseRelations(effects, mPostcondition);
		return applySinglePass(state, preparedRelations, domain, stats);
	}

	private IPredicate applySinglePass(final IPredicate state, final List<PreparedRelation> preparedRelations,
			final IDomain domain, final SifaStats stats) {
		if (preparedRelations.isEmpty() || SmtUtils.isTrueLiteral(state.getFormula())
				|| SmtUtils.isFalseLiteral(state.getFormula())) {
			return state;
		}

		IPredicate current = state;
		for (final PreparedRelation prepared : preparedRelations) {
			stats.increment(Key.INTERFERENCE_SP_APPLICATIONS);
			stats.start(Key.INTERFERENCE_SP_TIME);
			final IPredicate post = perDisjunctSP(current, prepared, stats);
			stats.stop(Key.INTERFERENCE_SP_TIME);
			if (SmtUtils.isFalseLiteral(post.getFormula())) {
				continue;
			}
			final IPredicate joined = domain.join(current, post);
			if (!domain.isSubsetEq(joined, current).isTrueForAbstraction()) {
				current = joined;
			}
		}
		return current;
	}

	private IPredicate perDisjunctSP(final IPredicate statePredicate, final PreparedRelation prepared,
			final SifaStats stats) {
		final Term stateFormula = statePredicate.getFormula();
		if (SmtUtils.isFalseLiteral(stateFormula) || SmtUtils.isFalseLiteral(prepared.relation().getFormula())) {
			return mPredicateFactory.newPredicate(mManagedScript.getScript().term("false"));
		}

		final Term[] disjuncts = getTopLevelDisjuncts(stateFormula);
		final Script script = mManagedScript.getScript();
		final Term relationFormula = prepared.relation().getFormula();
		final Set<TermVariable> preVarsToProject = prepared.preVarsToProject();
		final Map<Term, Term> primedToUnprimed = prepared.primedToUnprimed();

		final List<Term> resultTerms = new ArrayList<>();
		for (final Term disjunct : disjuncts) {
			final Term conjunction = SmtUtils.andWithExtendedLocalSimplification(script, disjunct, relationFormula);
			if (SmtUtils.isFalseLiteral(conjunction)) {
				continue;
			}

			final Term projected;
			if (preVarsToProject.isEmpty() || !hasFreeVarIn(conjunction, preVarsToProject)) {
				projected = conjunction;
			} else {
				projected = projectPreVars(conjunction, preVarsToProject, script, stats);
			}

			final Term renamed;
			if (primedToUnprimed.isEmpty() || !hasFreeVarIn(projected, primedToUnprimed.keySet())) {
				renamed = projected;
			} else {
				renamed = Substitution.apply(mManagedScript, primedToUnprimed, projected);
			}

			if (!SmtUtils.isFalseLiteral(renamed)) {
				resultTerms.add(renamed);
			}
		}

		if (resultTerms.isEmpty()) {
			return mPredicateFactory.newPredicate(script.term("false"));
		}
		final Term combined;
		if (resultTerms.size() == 1) {
			combined = resultTerms.get(0);
		} else {
			combined = SmtUtils.or(script, resultTerms.toArray(new Term[resultTerms.size()]));
		}
		return mPredicateFactory.newPredicate(combined);
	}

	/** Substitute equalities for projected vars; fall back to QE for any that remain. */
	private Term projectPreVars(final Term conjunction, final Set<TermVariable> toProject, final Script script,
			final SifaStats stats) {
		final Term[] conjuncts = getTopLevelConjuncts(conjunction);

		final Map<Term, Term> substitution = new HashMap<>();
		for (final Term conjunct : conjuncts) {
			final TermVariable solved = solveEqualityForProjected(conjunct, toProject);
			if (solved != null && !substitution.containsKey(solved)) {
				final Term value = getEqualityOtherSide(conjunct, solved);
				if (value != null && Collections.disjoint(Arrays.asList(value.getFreeVars()), toProject)) {
					substitution.put(solved, value);
				}
			}
		}

		Term[] workingConjuncts = conjuncts;
		if (!substitution.isEmpty()) {
			workingConjuncts = new Term[conjuncts.length];
			for (int i = 0; i < conjuncts.length; i++) {
				workingConjuncts[i] = Substitution.apply(mManagedScript, substitution, conjuncts[i]);
			}
		}

		final Set<TermVariable> remaining = new HashSet<>();
		final List<Term> kept = new ArrayList<>();
		for (final Term conjunct : workingConjuncts) {
			boolean mentionsProjected = false;
			for (final TermVariable fv : conjunct.getFreeVars()) {
				if (toProject.contains(fv)) {
					mentionsProjected = true;
					remaining.add(fv);
				}
			}
			if (!mentionsProjected) {
				kept.add(conjunct);
			}
		}

		if (remaining.isEmpty()) {
			stats.increment(Key.INTERFERENCE_QE_LIGHT);
			if (kept.size() == workingConjuncts.length && substitution.isEmpty()) {
				return conjunction;
			}
			if (kept.isEmpty()) {
				return script.term("true");
			}
			if (kept.size() == 1) {
				return kept.get(0);
			}
			return SmtUtils.and(script, kept.toArray(new Term[kept.size()]));
		}

		final Term reduced;
		if (substitution.isEmpty()) {
			reduced = conjunction;
		} else {
			reduced = SmtUtils.and(script, workingConjuncts);
		}
		return RelationalPredicateUtils.existentiallyProject(reduced, remaining, mServices, mManagedScript, stats);
	}

	private static TermVariable solveEqualityForProjected(final Term term, final Set<TermVariable> toProject) {
		if (!(term instanceof final ApplicationTerm app) || !"=".equals(app.getFunction().getName())
				|| app.getParameters().length != 2) {
			return null;
		}
		final Term lhs = app.getParameters()[0];
		final Term rhs = app.getParameters()[1];
		if (lhs instanceof final TermVariable lv && toProject.contains(lv)) {
			return lv;
		}
		if (rhs instanceof final TermVariable rv && toProject.contains(rv)) {
			return rv;
		}
		return null;
	}

	private static Term getEqualityOtherSide(final Term equality, final TermVariable var) {
		final ApplicationTerm app = (ApplicationTerm) equality;
		final Term lhs = app.getParameters()[0];
		final Term rhs = app.getParameters()[1];
		if (lhs == var) {
			return rhs;
		}
		if (rhs == var) {
			return lhs;
		}
		return null;
	}

	private static Term[] getTopLevelDisjuncts(final Term formula) {
		if (formula instanceof final ApplicationTerm app && "or".equals(app.getFunction().getName())) {
			return app.getParameters();
		}
		return new Term[] { formula };
	}

	private static Term[] getTopLevelConjuncts(final Term formula) {
		if (formula instanceof final ApplicationTerm app && "and".equals(app.getFunction().getName())) {
			return app.getParameters();
		}
		return new Term[] { formula };
	}

	private static boolean hasFreeVarIn(final Term term, final Set<? extends Term> candidates) {
		for (final TermVariable freeVar : term.getFreeVars()) {
			if (candidates.contains(freeVar)) {
				return true;
			}
		}
		return false;
	}
}
