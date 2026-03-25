package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Guarded transformer with purely syntactic projection: drops conjuncts mentioning projected variables.
 * No QE, no SMT calls. Exact for atomic constraints, sound over-approximation otherwise.
 */
public final class SyntacticInterferenceApplicator implements IInterferenceApplicator {

	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;

	public SyntacticInterferenceApplicator(final ManagedScript managedScript,
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
				final Term projected = syntacticProject(working, gp.modifiedGlobals(), script);
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

	/** Drop all top-level conjuncts that mention any variable in {@code toProject}. Sound over-approximation. */
	private static Term syntacticProject(final Term formula, final Set<TermVariable> toProject, final Script script) {
		final Term[] conjuncts = getTopLevelConjuncts(formula);
		final List<Term> kept = new ArrayList<>();
		for (final Term conjunct : conjuncts) {
			if (Collections.disjoint(Arrays.asList(conjunct.getFreeVars()), toProject)) {
				kept.add(conjunct);
			}
		}
		if (kept.size() == conjuncts.length) {
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
