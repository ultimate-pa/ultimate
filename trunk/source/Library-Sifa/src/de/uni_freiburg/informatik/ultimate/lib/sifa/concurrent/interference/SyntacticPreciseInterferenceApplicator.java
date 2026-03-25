package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Like {@link SyntacticInterferenceApplicator} but substitutes equalities before projection, recovering precision
 * for cross-variable constraints. Still purely syntactic (no QE).
 */
public final class SyntacticPreciseInterferenceApplicator implements IInterferenceApplicator {

	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;

	public SyntacticPreciseInterferenceApplicator(final ManagedScript managedScript,
			final BasicPredicateFactory predicateFactory) {
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
	}

	@Override
	public IPredicate apply(final IPredicate state, final Collection<GuardedPredicate> predicates, final IDomain domain,
			final int wideningThreshold, final SifaStats stats) {
		if (predicates.isEmpty() || SmtUtils.isTrueLiteral(state.getFormula())
				|| SmtUtils.isFalseLiteral(state.getFormula())) {
			return state;
		}
		IPredicate current = state;
		for (final GuardedPredicate gp : predicates) {
			final IPredicate effect = gp.effect();
			if (SmtUtils.isFalseLiteral(effect.getFormula())) {
				continue;
			}
			if (gp.hasGuard() && !guardOverlaps(current, gp.guard())) {
				continue;
			}
			final IPredicate interfered = computeInterferedPerDisjunct(current, gp);
			if (interfered == null || SmtUtils.isFalseLiteral(interfered.getFormula())) {
				continue;
			}
			final IPredicate joined = domain.join(current, interfered);
			if (!domain.isSubsetEq(joined, current).isTrueForAbstraction()) {
				current = joined;
			}
		}
		return current;
	}

	private IPredicate computeInterferedPerDisjunct(final IPredicate current, final GuardedPredicate gp) {
		final Script script = mManagedScript.getScript();
		final Term[] disjuncts = getTopLevelDisjuncts(current.getFormula());

		final List<Term> interferedTerms = new ArrayList<>();
		for (final Term disjunct : disjuncts) {
			Term working = disjunct;
			if (gp.hasGuard()) {
				working = SmtUtils.andWithExtendedLocalSimplification(script, disjunct, gp.guard().getFormula());
				if (SmtUtils.isFalseLiteral(working)) {
					continue;
				}
			}
			if (gp.hasModifiedGlobals() && !gp.modifiedGlobals().isEmpty()) {
				final Term projected = substituteThenProject(working, gp.modifiedGlobals(), script);
				final Term met = SmtUtils.and(script, projected, gp.effect().getFormula());
				if (!SmtUtils.isFalseLiteral(met)) {
					interferedTerms.add(met);
				}
			} else {
				interferedTerms.add(gp.effect().getFormula());
			}
		}

		if (interferedTerms.isEmpty()) {
			return null;
		}
		final Term combined;
		if (interferedTerms.size() == 1) {
			combined = interferedTerms.get(0);
		} else {
			combined = SmtUtils.or(script, interferedTerms.toArray(new Term[interferedTerms.size()]));
		}
		return mPredicateFactory.newPredicate(combined);
	}

	/** Substitute equalities for projected variables, then drop remaining conjuncts that mention them. */
	private Term substituteThenProject(final Term formula, final Set<TermVariable> toProject, final Script script) {
		final Term[] conjuncts = getTopLevelConjuncts(formula);

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

		final List<Term> kept = new ArrayList<>();
		for (final Term conjunct : workingConjuncts) {
			if (Collections.disjoint(Arrays.asList(conjunct.getFreeVars()), toProject)) {
				kept.add(conjunct);
			}
		}
		if (kept.size() == workingConjuncts.length && substitution.isEmpty()) {
			return formula;
		}
		if (kept.isEmpty()) {
			return script.term("true");
		}
		if (kept.size() == 1) {
			return kept.get(0);
		}
		return SmtUtils.and(script, kept.toArray(new Term[kept.size()]));
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

	private boolean guardOverlaps(final IPredicate state, final IPredicate guard) {
		final var script = mManagedScript.getScript();
		final var conjunction =
				SmtUtils.andWithExtendedLocalSimplification(script, state.getFormula(), guard.getFormula());
		return !SmtUtils.isFalseLiteral(conjunction);
	}
}
