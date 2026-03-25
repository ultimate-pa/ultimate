package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

/** Applies non-relational post-state interference via domain join. Ignores guards. */
public final class PostStateInterferenceApplicator implements IInterferenceApplicator {

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
			final IPredicate joined = domain.join(current, effect);
			if (!domain.isSubsetEq(joined, current).isTrueForAbstraction()) {
				current = joined;
			}
		}
		return current;
	}
}
