package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.strongestpostcondition;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.IThreadLocalDomainContext;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain.AbstractLocationPartitionedDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain.AbstractLocationPartitionedPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain.GlobalLocationState;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
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
			PreparedRelation preparedRelationalInterference, IPredicate unconditionalPostState) {
	}

	private final Map<ThreadedKey, RelationalInterference> mInterferenceByKey;
	private final Map<String, String> mLocationVarNameByThread;
	private final RelationalPredicatePostcondition mPostcondition;
	// True once this object was created by widen(). Widening can narrow the
	// relational pre-state, causing SP=false for actually-feasible interferences.
	// The fallback to unconditionalPostState is only sound to use after widening.
	private final boolean mIsWidened;
	// Per-relation cache: PreparedRelation identity → (state Term identity → SP result).
	private final IdentityHashMap<PreparedRelation, IdentityHashMap<Term, IPredicate>> mSpCache =
			new IdentityHashMap<>();

	public StrongestPostconditionInterference(
			final Map<ThreadedKey, RelationalInterference> interferenceByKey,
			final Map<String, String> locationVarNameByThread, final RelationalPredicatePostcondition postcondition) {
		this(interferenceByKey, locationVarNameByThread, postcondition, false);
	}

	private StrongestPostconditionInterference(
			final Map<ThreadedKey, RelationalInterference> interferenceByKey,
			final Map<String, String> locationVarNameByThread, final RelationalPredicatePostcondition postcondition,
			final boolean isWidened) {
		mInterferenceByKey = Map.copyOf(interferenceByKey);
		mLocationVarNameByThread = Map.copyOf(locationVarNameByThread);
		mPostcondition = postcondition;
		mIsWidened = isWidened;
	}

	@Override
	public IPredicate applyUntilFixpoint(final IPredicate state, final Set<String> activeThreadIds,
			final IDomain domain, final int wideningThreshold, final SifaStats stats) {
		if (mInterferenceByKey.isEmpty()
				|| (!(state instanceof AbstractLocationPartitionedPredicate) && SmtUtils.isTrueLiteral(state.getFormula()))
				|| SmtUtils.isFalseLiteral(state.getFormula())) {
			return state;
		}
		final List<Entry<ThreadedKey, RelationalInterference>> active = buildActive(activeThreadIds);
		if (active.isEmpty()) {
			return state;
		}
		IPredicate current = state;
		IPredicate frontier = state;
		for (int iteration = 1;; iteration++) {
			stats.increment(Key.INTERFERENCE_INNER_ITERATIONS);
			boolean hasGenerated = false;
			IPredicate generated = state;
			for (final Entry<ThreadedKey, RelationalInterference> entry : active) {
				final IPredicate post = applyGroupToFrontier(frontier, entry.getKey(), entry.getValue(), domain);
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

	private List<Entry<ThreadedKey, RelationalInterference>> buildActive(final Set<String> activeThreadIds) {
		final List<Entry<ThreadedKey, RelationalInterference>> active = new ArrayList<>();
		for (final Entry<ThreadedKey, RelationalInterference> e : mInterferenceByKey.entrySet()) {
			if (activeThreadIds.contains(e.getKey().threadId())) {
				active.add(e);
			}
		}
		return active;
	}

	private IPredicate applyGroupToFrontier(final IPredicate frontier, final ThreadedKey key,
			final RelationalInterference relationalInterference, final IDomain domain) {
		if (frontier instanceof final AbstractLocationPartitionedPredicate partitionedFrontier
				&& domain instanceof final AbstractLocationPartitionedDomain partitionedDomain) {
			return applyGroupToPartitionedFrontier(partitionedFrontier, key, relationalInterference, partitionedDomain);
		}
		return applyGroupToState(frontier, relationalInterference, true);
	}

	// Apply per partition, update partition key directly from interference metadata -- no DNF re-split.
	private IPredicate applyGroupToPartitionedFrontier(final AbstractLocationPartitionedPredicate frontier,
			final ThreadedKey key, final RelationalInterference relationalInterference,
			final AbstractLocationPartitionedDomain partitionedDomain) {
		final String locationVarName = mLocationVarNameByThread.get(key.threadId());
		final int sourceLocation = key.pair().sourceAbstractLocation();
		final int targetLocation = key.pair().targetAbstractLocation();
		final Map<GlobalLocationState, IPredicate> result = new LinkedHashMap<>();
		for (final Entry<GlobalLocationState, IPredicate> entry : frontier.partitions().entrySet()) {
			if (locationVarName != null && contradictsSourceLocation(entry.getKey(), locationVarName, sourceLocation)) {
				continue;
			}
			final IPredicate post = applyGroupToState(entry.getValue(), relationalInterference, false);
			if (SmtUtils.isFalseLiteral(post.getFormula())) {
				continue;
			}
			final GlobalLocationState newKey = withUpdatedLocation(entry.getKey(), locationVarName, targetLocation);
			result.merge(newKey, post, partitionedDomain.underlyingDomain()::join);
		}
		if (result.isEmpty()) {
			return mPostcondition.getPredicateFactory().newPredicate(
					mPostcondition.getManagedScript().getScript().term("false"));
		}
		return partitionedDomain.buildPredicateFromPartitionsMap(result);
	}

	private static GlobalLocationState withUpdatedLocation(final GlobalLocationState key,
			final String locationVarName, final int newLocation) {
		if (locationVarName == null) {
			return key;
		}
		final Map<String, Integer> updated = new LinkedHashMap<>(key.locs());
		updated.put(locationVarName, newLocation);
		return new GlobalLocationState(updated);
	}

	private static boolean contradictsSourceLocation(final GlobalLocationState partitionKey,
			final String locationVarName, final int sourceLocation) {
		final Integer partitionLocation = partitionKey.locs().get(locationVarName);
		return partitionLocation != null && partitionLocation.intValue() != sourceLocation;
	}

	private IPredicate applyGroupToState(final IPredicate frontier,
			final RelationalInterference relationalInterference, final boolean allowWidenedFallback) {
		final PreparedRelation prepared = relationalInterference.preparedRelationalInterference();
		final IPredicate sp = mSpCache.computeIfAbsent(prepared, k -> new IdentityHashMap<>())
				.computeIfAbsent(frontier.getFormula(),
						k -> mPostcondition.strongestPostcondition(frontier, prepared));
		if (!SmtUtils.isFalseLiteral(sp.getFormula())) {
			return sp;
		}
		if (!mIsWidened || !allowWidenedFallback) {
			return sp;
		}
		// After outer-fixpoint widening the pre-state component can be narrowed, causing
		// SP=false for actually-feasible interferences. Fall back to SP(true, R).
		return relationalInterference.unconditionalPostState();
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
				final IPredicate widenedPostState =
						domain.widen(entry.getValue().unconditionalPostState(), otherGroup.unconditionalPostState());
				widenedGroup = new RelationalInterference(widenedRelationalInterference,
						mPostcondition.prepareRelation(widenedRelationalInterference), widenedPostState);
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
				: new StrongestPostconditionInterference(widened, mLocationVarNameByThread, mPostcondition, true);
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
