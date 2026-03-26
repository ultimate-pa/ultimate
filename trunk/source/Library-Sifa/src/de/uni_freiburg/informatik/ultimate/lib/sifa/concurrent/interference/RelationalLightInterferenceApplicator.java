package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition.PreparedRelation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats.Key;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

/**
 * Single-pass relational SP with per-disjunct splitting and equality substitution shortcut.
 * Convergence via outer fixpoint; avoids the compounding cost of an inner fixpoint loop.
 */
public final class RelationalLightInterferenceApplicator implements IInterferenceApplicator {

	private final RelationalPredicatePostcondition mPostcondition;

	public RelationalLightInterferenceApplicator(final RelationalPredicatePostcondition postcondition) {
		mPostcondition = postcondition;
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
			final IPredicate post = InterferenceUtils.perDisjunctSP(current, prepared, mPostcondition, stats);
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
}
