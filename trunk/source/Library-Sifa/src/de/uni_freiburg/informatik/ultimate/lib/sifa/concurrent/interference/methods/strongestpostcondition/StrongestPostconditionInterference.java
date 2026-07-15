package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.strongestpostcondition;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGroupKey;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping.AbstractLocationPair;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.KeyedInterferenceSet;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.RelationalPredicatePostcondition.PreparedRelation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats.Key;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public final class StrongestPostconditionInterference
		extends KeyedInterferenceSet<StrongestPostconditionInterference.RelationalInterference> {

	public record RelationalInterference(IPredicate relationalInterference,
			PreparedRelation preparedRelationalInterference, IPredicate unconditionalPostState) {
	}

	private final RelationalPredicatePostcondition mPostcondition;
	private final boolean mIsWidened;
	private final IdentityHashMap<PreparedRelation, IdentityHashMap<Term, IPredicate>> mSpCache =
			new IdentityHashMap<>();

	public StrongestPostconditionInterference(
			final Map<InterferenceGroupKey, RelationalInterference> summaryByKey,
			final Map<String, Set<IcfgLocation>> preForkSourcesByThread,
			final RelationalPredicatePostcondition postcondition) {
		this(summaryByKey, preForkSourcesByThread, postcondition, false);
	}

	private StrongestPostconditionInterference(
			final Map<InterferenceGroupKey, RelationalInterference> summaryByKey,
			final Map<String, Set<IcfgLocation>> preForkSourcesByThread,
			final RelationalPredicatePostcondition postcondition, final boolean isWidened) {
		super(summaryByKey, preForkSourcesByThread);
		mPostcondition = postcondition;
		mIsWidened = isWidened;
	}

	@Override
	public IPredicate applyUntilFixpoint(final IPredicate state, final String observerThreadId,
			final Set<String> activeThreadIds, final Set<String> observerLockset, final IDomain domain,
			final int wideningThreshold, final SifaStats stats) {
		if (mSummaryByKey.isEmpty() || SmtUtils.isTrueLiteral(state.getFormula())
				|| SmtUtils.isFalseLiteral(state.getFormula())) {
			return state;
		}
		final List<Entry<InterferenceGroupKey, RelationalInterference>> applicable =
				selectApplicableSummaries(observerThreadId, activeThreadIds, observerLockset, stats);
		if (applicable.isEmpty()) {
			return state;
		}
		final List<RelationalInterference> merged = mergeByLocationPair(applicable, domain);
		final Set<RelationalInterference> fallbackApplied =
				mIsWidened ? Collections.newSetFromMap(new IdentityHashMap<>()) : Set.of();
		IPredicate current = state;
		IPredicate frontier = state;
		for (int iteration = 1;; iteration++) {
			stats.increment(Key.INTERFERENCE_INNER_ITERATIONS);
			boolean hasGenerated = false;
			IPredicate generated = state;
			for (final RelationalInterference summary : merged) {
				final IPredicate post = applySummaryToState(frontier, summary, fallbackApplied);
				if (SmtUtils.isFalseLiteral(post.getFormula())) {
					continue;
				}
				if (!hasGenerated) {
					generated = post;
					hasGenerated = true;
				} else {
					generated = domain.join(generated, post);
				}
			}
			if (!hasGenerated || domain.isSubsetEq(generated, current).isTrueForAbstraction()) {
				return current;
			}

			final IPredicate expanded = domain.join(current, generated);
			final IPredicate next;
			if (iteration > wideningThreshold) {
				next = domain.widen(current, expanded);
				stats.increment(Key.INTERFERENCE_INNER_WIDENINGS);
			} else {
				next = expanded;
			}
			if (domain.isSubsetEq(next, current).isTrueForAbstraction()) {
				return current;
			}
			current = next;
			frontier = generated;
		}
	}

	private record LocationPairKey(String threadId, AbstractLocationPair pair) {
	}

	private List<RelationalInterference> mergeByLocationPair(
			final List<Entry<InterferenceGroupKey, RelationalInterference>> applicable, final IDomain domain) {
		final Map<LocationPairKey, RelationalInterference> byPair = new LinkedHashMap<>();
		for (final Entry<InterferenceGroupKey, RelationalInterference> entry : applicable) {
			final LocationPairKey pairKey =
					new LocationPairKey(entry.getKey().threadId(), entry.getKey().abstractLocations());
			byPair.merge(pairKey, entry.getValue(), (a, b) -> joinRelationalInterferences(a, b, domain));
		}
		return new ArrayList<>(byPair.values());
	}

	private RelationalInterference joinRelationalInterferences(final RelationalInterference left,
			final RelationalInterference right, final IDomain domain) {
		final IPredicate joinedRelation = domain.join(left.relationalInterference(), right.relationalInterference());
		final IPredicate joinedPostState = domain.join(left.unconditionalPostState(), right.unconditionalPostState());
		return new RelationalInterference(joinedRelation, mPostcondition.prepareRelation(joinedRelation),
				joinedPostState);
	}

	private IPredicate applySummaryToState(final IPredicate frontier, final RelationalInterference summary,
			final Set<RelationalInterference> fallbackApplied) {
		final PreparedRelation prepared = summary.preparedRelationalInterference();
		final IPredicate sp = mSpCache.computeIfAbsent(prepared, k -> new IdentityHashMap<>())
				.computeIfAbsent(frontier.getFormula(), k -> mPostcondition.strongestPostcondition(frontier, prepared));
		if (!SmtUtils.isFalseLiteral(sp.getFormula()) || !mIsWidened || !fallbackApplied.add(summary)) {
			return sp;
		}
		return summary.unconditionalPostState();
	}

	@Override
	protected RelationalInterference widenSummaries(final RelationalInterference left,
			final RelationalInterference right, final IDomain domain) {
		final IPredicate widenedRelation =
				domain.widen(left.relationalInterference(), right.relationalInterference());
		final IPredicate widenedPostState =
				domain.widen(left.unconditionalPostState(), right.unconditionalPostState());
		return new RelationalInterference(widenedRelation, mPostcondition.prepareRelation(widenedRelation),
				widenedPostState);
	}

	@Override
	protected boolean isTrivialSummary(final RelationalInterference summary) {
		return SmtUtils.isFalseLiteral(summary.relationalInterference().getFormula());
	}

	@Override
	protected boolean summaryIsSubsumedBy(final RelationalInterference left, final RelationalInterference right,
			final IDomain domain) {
		return domain.isSubsetEq(left.relationalInterference(), right.relationalInterference())
				.isTrueForAbstraction();
	}

	@Override
	protected KeyedInterferenceSet<RelationalInterference> withSummaries(
			final Map<InterferenceGroupKey, RelationalInterference> summaries) {
		return new StrongestPostconditionInterference(summaries, mPreForkSourcesByThread, mPostcondition, true);
	}
}
