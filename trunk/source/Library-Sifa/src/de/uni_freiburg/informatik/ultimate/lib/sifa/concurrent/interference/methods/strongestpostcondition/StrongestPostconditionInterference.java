package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.strongestpostcondition;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain.BucketContext;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping.AbstractLocationPair;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition.PreparedRelation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats.Key;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

public final class StrongestPostconditionInterference implements IInterference {

	public record RelationalInterference(IPredicate relationalInterference,
			PreparedRelation preparedRelationalInterference) {
	}

	private final Map<AbstractLocationPair, RelationalInterference> mInterferenceByAbstractLocationPair;
	private final RelationalPredicatePostcondition mPostcondition;
	private final BucketContext mBucketContext;

	public StrongestPostconditionInterference(
			final Map<AbstractLocationPair, RelationalInterference> interferenceByAbstractLocationPair,
			final RelationalPredicatePostcondition postcondition, final BucketContext bucketContext) {
		mInterferenceByAbstractLocationPair = Map.copyOf(interferenceByAbstractLocationPair);
		mPostcondition = postcondition;
		mBucketContext = bucketContext;
	}

	@Override
	public IPredicate applyUntilFixpoint(final IPredicate state, final IDomain domain, final int wideningThreshold,
			final SifaStats stats) {
		if (mInterferenceByAbstractLocationPair.isEmpty() || SmtUtils.isTrueLiteral(state.getFormula())
				|| SmtUtils.isFalseLiteral(state.getFormula())) {
			return state;
		}
		if (mBucketContext != null && mBucketContext.hasCurrentBuckets()) {
			return mBucketContext.applyUntilFixpoint(state, domain, wideningThreshold, stats,
					mInterferenceByAbstractLocationPair, (frontier, group, __) -> applyGroupToFrontier(frontier, group));
		}
		IPredicate current = state;
		IPredicate frontier = state;
		for (int iteration = 1;; iteration++) {
			stats.increment(Key.INTERFERENCE_INNER_ITERATIONS);
			boolean hasGenerated = false;
			IPredicate generated = state;
			for (final RelationalInterference group : mInterferenceByAbstractLocationPair.values()) {
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

	private IPredicate applyGroupToFrontier(final IPredicate frontier, final RelationalInterference relationalInterference) {
		return mPostcondition.strongestPostcondition(frontier,
				relationalInterference.preparedRelationalInterference());
	}

	@Override
	public IInterference widen(final IInterference other, final IDomain domain) {
		if (!(other instanceof final StrongestPostconditionInterference typedOther)) {
			throw new IllegalArgumentException(
					"Cannot widen StrongestPostconditionInterference with " + other.getClass().getSimpleName());
		}
		final Map<AbstractLocationPair, RelationalInterference> widened = new LinkedHashMap<>();
		for (final Entry<AbstractLocationPair, RelationalInterference> entry : mInterferenceByAbstractLocationPair.entrySet()) {
			final RelationalInterference otherGroup = typedOther.mInterferenceByAbstractLocationPair.get(entry.getKey());
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
		for (final Entry<AbstractLocationPair, RelationalInterference> entry : typedOther.mInterferenceByAbstractLocationPair.entrySet()) {
			if (!widened.containsKey(entry.getKey()) && !SmtUtils.isFalseLiteral(entry.getValue().relationalInterference().getFormula())) {
				widened.put(entry.getKey(), entry.getValue());
			}
		}
		return widened.isEmpty() ? null
				: new StrongestPostconditionInterference(widened, mPostcondition, mBucketContext);
	}

	@Override
	public boolean isSubsumedBy(final IInterference other, final IDomain domain) {
		if (!(other instanceof final StrongestPostconditionInterference typedOther)) {
			return false;
		}
		for (final Entry<AbstractLocationPair, RelationalInterference> entry : mInterferenceByAbstractLocationPair.entrySet()) {
			final RelationalInterference otherGroup = typedOther.mInterferenceByAbstractLocationPair.get(entry.getKey());
			if (otherGroup == null || !domain.isSubsetEq(entry.getValue().relationalInterference(),
					otherGroup.relationalInterference()).isTrueForAbstraction()) {
				return false;
			}
		}
		return true;
	}

}
