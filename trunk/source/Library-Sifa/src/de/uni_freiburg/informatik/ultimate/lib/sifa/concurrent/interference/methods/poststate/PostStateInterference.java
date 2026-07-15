package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.poststate;

import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGroupKey;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.KeyedInterferenceSet;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

public final class PostStateInterference extends KeyedInterferenceSet<IPredicate> {

	public PostStateInterference(final Map<InterferenceGroupKey, IPredicate> summaryByKey,
			final Map<String, Set<IcfgLocation>> preForkSourcesByThread) {
		super(summaryByKey, preForkSourcesByThread);
	}

	@Override
	public IPredicate applyUntilFixpoint(final IPredicate state, final String observerThreadId,
			final Set<String> activeThreadIds, final Set<String> observerLockset, final IDomain domain,
			final int wideningThreshold, final SifaStats stats) {
		final List<Entry<InterferenceGroupKey, IPredicate>> applicable =
				selectApplicableSummaries(observerThreadId, activeThreadIds, observerLockset, stats);
		if (applicable.isEmpty()) {
			return state;
		}
		IPredicate result = state;
		for (final Entry<InterferenceGroupKey, IPredicate> entry : applicable) {
			result = domain.join(result, entry.getValue());
		}
		return result;
	}

	@Override
	protected IPredicate widenSummaries(final IPredicate left, final IPredicate right, final IDomain domain) {
		return domain.widen(left, right);
	}

	@Override
	protected boolean isTrivialSummary(final IPredicate summary) {
		return SmtUtils.isFalseLiteral(summary.getFormula());
	}

	@Override
	protected boolean summaryIsSubsumedBy(final IPredicate left, final IPredicate right, final IDomain domain) {
		return domain.isSubsetEq(left, right).isTrueForAbstraction();
	}

	@Override
	protected KeyedInterferenceSet<IPredicate> withSummaries(final Map<InterferenceGroupKey, IPredicate> summaries) {
		return new PostStateInterference(summaries, mPreForkSourcesByThread);
	}
}
