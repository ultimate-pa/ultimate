package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.ArrayList;
import java.util.Collection;
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

/** Intersect with guard, drop conjuncts mentioning modified variables, conjoin effect. */
public final class GuardedOverwriteInterferenceApplicator implements IInterferenceApplicator {

	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;

	public GuardedOverwriteInterferenceApplicator(final ManagedScript managedScript,
			final BasicPredicateFactory predicateFactory) {
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
	}

	@Override
	public IPredicate apply(final IPredicate state, final Collection<GuardedPredicate> predicates, final IDomain domain,
			final int wideningThreshold, final SifaStats stats) {
		return InterferenceUtils.applyUntilFixpoint(state, predicates, domain, wideningThreshold, stats,
				this::applyGuardedOverwrite);
	}

	private IPredicate applyGuardedOverwrite(final IPredicate frontier, final GuardedPredicate predicate) {
		final Script script = mManagedScript.getScript();

		if (SmtUtils.isFalseLiteral(predicate.effect().getFormula())) {
			return mPredicateFactory.newPredicate(script.term("false"));
		}

		final Term[] frontierDisjuncts = InterferenceUtils.getTopLevelDisjuncts(frontier.getFormula());
		final Term[] guardDisjuncts = predicate.hasGuard()
				? InterferenceUtils.getTopLevelDisjuncts(predicate.guard().getFormula())
				: null;

		final List<Term> results = new ArrayList<>();
		for (final Term fd : frontierDisjuncts) {
			if (guardDisjuncts != null) {
				for (final Term gd : guardDisjuncts) {
					final Term result = applyToConjunctivePair(fd, gd, predicate, script);
					if (result != null) {
						results.add(result);
					}
				}
			} else {
				final Term result = applyToConjunctivePair(fd, null, predicate, script);
				if (result != null) {
					results.add(result);
				}
			}
		}

		if (results.isEmpty()) {
			return mPredicateFactory.newPredicate(script.term("false"));
		}
		final Term combined = results.size() == 1 ? results.get(0)
				: SmtUtils.or(script, results.toArray(new Term[0]));
		return mPredicateFactory.newPredicate(combined);
	}

	/** Returns null if the pair is contradictory. */
	private Term applyToConjunctivePair(final Term state, final Term guard, final GuardedPredicate predicate,
			final Script script) {
		final List<Term> allConjuncts = new ArrayList<>();
		InterferenceUtils.collectConjuncts(state, allConjuncts);
		if (guard != null) {
			InterferenceUtils.collectConjuncts(guard, allConjuncts);
		}

		if (InterferenceUtils.hasEqualityContradiction(allConjuncts)) {
			return null;
		}

		final Term guardedState = allConjuncts.size() == 1 ? allConjuncts.get(0)
				: SmtUtils.and(script, allConjuncts.toArray(new Term[0]));
		if (SmtUtils.isFalseLiteral(guardedState)) {
			return null;
		}

		final Set<TermVariable> changedSharedVars = predicate.modifiedGlobalsOrEmpty();
		final Term projected = !changedSharedVars.isEmpty()
				? forgetChangedConjuncts(guardedState, changedSharedVars, script)
				: guardedState;
		return SmtUtils.and(script, projected, predicate.effect().getFormula());
	}

	/** Drop conjuncts mentioning any changed shared variable (sound over-approximation). */
	private static Term forgetChangedConjuncts(final Term formula, final Set<TermVariable> changedVars,
			final Script script) {
		final Term[] conjuncts = getTopLevelConjuncts(formula);
		final List<Term> kept = new ArrayList<>();
		for (final Term conjunct : conjuncts) {
			if (!mentionsAny(conjunct, changedVars)) {
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

	private static boolean mentionsAny(final Term term, final Set<TermVariable> variables) {
		for (final TermVariable fv : term.getFreeVars()) {
			if (variables.contains(fv)) {
				return true;
			}
		}
		return false;
	}

	private static Term[] getTopLevelConjuncts(final Term formula) {
		if (formula instanceof final ApplicationTerm app && "and".equals(app.getFunction().getName())) {
			return app.getParameters();
		}
		return new Term[] { formula };
	}
}
