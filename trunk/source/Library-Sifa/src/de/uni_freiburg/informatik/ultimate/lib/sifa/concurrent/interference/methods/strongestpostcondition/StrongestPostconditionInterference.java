package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.strongestpostcondition;

import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.IThreadLocalDomainContext;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain.BucketDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping.AbstractLocationPair;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping.ThreadedKey;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition.PreparedRelation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats.Key;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public final class StrongestPostconditionInterference implements IInterference {

	public record RelationalInterference(IPredicate relationalInterference,
			PreparedRelation preparedRelationalInterference) {
	}

	private final Map<ThreadedKey, RelationalInterference> mInterferenceByKey;
	private final RelationalPredicatePostcondition mPostcondition;
	private final BucketDomain mBucketDomain;
	// Per-relation cache: PreparedRelation identity → (state Term identity → SP result).
	private final IdentityHashMap<PreparedRelation, IdentityHashMap<Term, IPredicate>> mSpCache =
			new IdentityHashMap<>();

	public StrongestPostconditionInterference(
			final Map<ThreadedKey, RelationalInterference> interferenceByKey,
			final RelationalPredicatePostcondition postcondition, final BucketDomain bucketDomain) {
		mInterferenceByKey = Map.copyOf(interferenceByKey);
		mPostcondition = postcondition;
		mBucketDomain = bucketDomain;
	}

	@Override
	public IPredicate applyUntilFixpoint(final IPredicate state, final Set<String> activeThreadIds,
			final IDomain domain, final int wideningThreshold, final SifaStats stats) {
		if (mInterferenceByKey.isEmpty() || SmtUtils.isTrueLiteral(state.getFormula())
				|| SmtUtils.isFalseLiteral(state.getFormula())) {
			return state;
		}
		final Map<AbstractLocationPair, RelationalInterference> filtered = buildFiltered(activeThreadIds);
		if (filtered.isEmpty()) {
			return state;
		}
		if (mBucketDomain != null && mBucketDomain.hasCurrentBuckets()) {
			return mBucketDomain.applyUntilFixpoint(state, domain, wideningThreshold, stats,
					filtered, (frontier, group, __) -> applyGroupToFrontier(frontier, group));
		}
		IPredicate current = state;
		IPredicate frontier = state;
		for (int iteration = 1;; iteration++) {
			stats.increment(Key.INTERFERENCE_INNER_ITERATIONS);
			boolean hasGenerated = false;
			IPredicate generated = state;
			for (final RelationalInterference group : filtered.values()) {
				final IPredicate post = applyGroupToFrontier(frontier, group);
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

	private Map<AbstractLocationPair, RelationalInterference> buildFiltered(final Set<String> activeThreadIds) {
		final Map<AbstractLocationPair, RelationalInterference> filtered = new LinkedHashMap<>();
		for (final Entry<ThreadedKey, RelationalInterference> e : mInterferenceByKey.entrySet()) {
			if (activeThreadIds.contains(e.getKey().threadId())) {
				filtered.put(e.getKey().pair(), e.getValue());
			}
		}
		return filtered;
	}

	private IPredicate applyGroupToFrontier(final IPredicate frontier,
			final RelationalInterference relationalInterference) {
		final PreparedRelation prepared = relationalInterference.preparedRelationalInterference();
		return mSpCache.computeIfAbsent(prepared, k -> new IdentityHashMap<>())
				.computeIfAbsent(frontier.getFormula(),
						k -> mPostcondition.strongestPostcondition(frontier, prepared));
	}

	@Override
	public boolean isEmpty() {
		return mInterferenceByKey.isEmpty();
	}

	@Override
	public Set<String> threadIds() {
		final Set<String> ids = new LinkedHashSet<>();
		mInterferenceByKey.keySet().forEach(k -> ids.add(k.threadId()));
		return Set.copyOf(ids);
	}

	@Override
	public IInterference widen(final IInterference other, final IDomain domain) {
		if (!(other instanceof final StrongestPostconditionInterference typedOther)) {
			throw new IllegalArgumentException(
					"Cannot widen StrongestPostconditionInterference with " + other.getClass().getSimpleName());
		}
		final Map<ThreadedKey, RelationalInterference> widened = new LinkedHashMap<>();
		for (final Entry<ThreadedKey, RelationalInterference> entry : mInterferenceByKey.entrySet()) {
			IThreadLocalDomainContext.setIfApplicable(domain, entry.getKey().threadId());
			final RelationalInterference otherGroup = typedOther.mInterferenceByKey.get(entry.getKey());
			final RelationalInterference widenedGroup;
			if (otherGroup == null) {
				widenedGroup = entry.getValue();
			} else {
				final IPredicate widenedRelationalInterference =
						domain.widen(entry.getValue().relationalInterference(), otherGroup.relationalInterference());
				widenedGroup = new RelationalInterference(widenedRelationalInterference,
						mPostcondition.prepareRelation(widenedRelationalInterference));
			}
			if (!SmtUtils.isFalseLiteral(widenedGroup.relationalInterference().getFormula())) {
				widened.put(entry.getKey(), widenedGroup);
			}
		}
		for (final Entry<ThreadedKey, RelationalInterference> entry : typedOther.mInterferenceByKey.entrySet()) {
			if (!widened.containsKey(entry.getKey())
					&& !SmtUtils.isFalseLiteral(entry.getValue().relationalInterference().getFormula())) {
				widened.put(entry.getKey(), entry.getValue());
			}
		}
		return widened.isEmpty() ? null
				: new StrongestPostconditionInterference(widened, mPostcondition, mBucketDomain);
	}

	@Override
	public boolean isSubsumedBy(final IInterference other, final IDomain domain) {
		if (!(other instanceof final StrongestPostconditionInterference typedOther)) {
			return false;
		}
		for (final Entry<ThreadedKey, RelationalInterference> entry : mInterferenceByKey.entrySet()) {
			IThreadLocalDomainContext.setIfApplicable(domain, entry.getKey().threadId());
			final RelationalInterference otherGroup = typedOther.mInterferenceByKey.get(entry.getKey());
			if (otherGroup == null || !domain.isSubsetEq(entry.getValue().relationalInterference(),
					otherGroup.relationalInterference()).isTrueForAbstraction()) {
				return false;
			}
		}
		return true;
	}

}
