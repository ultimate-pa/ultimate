package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.prepost;

import java.util.ArrayList;
import java.util.Iterator;
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
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats.Key;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public final class PrePostInterference implements IInterference {

	public record PrePostPair(IPredicate preState, IPredicate postState) {
	}

	private final Map<ThreadedKey, PrePostPair> mInterferenceByKey;
	private final ManagedScript mManagedScript;
	private final BucketDomain mBucketDomain;
	private final IPredicate mFalsePredicate;

	public PrePostInterference(final Map<ThreadedKey, PrePostPair> interferenceByKey,
			final ManagedScript managedScript, final BucketDomain bucketDomain, final IPredicate falsePredicate) {
		mInterferenceByKey = Map.copyOf(interferenceByKey);
		mManagedScript = managedScript;
		mBucketDomain = bucketDomain;
		mFalsePredicate = falsePredicate;
	}

	@Override
	public IPredicate applyUntilFixpoint(final IPredicate state, final Set<String> activeThreadIds,
			final IDomain domain, final int wideningThreshold, final SifaStats stats) {
		if (mInterferenceByKey.isEmpty() || SmtUtils.isTrueLiteral(state.getFormula())
				|| SmtUtils.isFalseLiteral(state.getFormula())) {
			return state;
		}
		final Map<AbstractLocationPair, PrePostPair> filtered = buildFiltered(activeThreadIds);
		if (filtered.isEmpty()) {
			return state;
		}
		if (mBucketDomain != null && mBucketDomain.hasCurrentBuckets()) {
			return mBucketDomain.applyUntilFixpoint(state, domain, wideningThreshold, stats,
					filtered, (frontier, pair, __) ->
							intersects(frontier, pair.preState()) ? pair.postState() : mFalsePredicate);
		}
		IPredicate current = state;
		IPredicate frontier = state;
		final ArrayList<PrePostPair> remaining = new ArrayList<>(filtered.values());
		for (int iteration = 1;; iteration++) {
			stats.increment(Key.INTERFERENCE_INNER_ITERATIONS);
			boolean hasGenerated = false;
			IPredicate generated = state;
			for (final Iterator<PrePostPair> iterator = remaining.iterator(); iterator.hasNext();) {
				final PrePostPair pair = iterator.next();
				if (!SmtUtils.isTrueLiteral(pair.preState().getFormula()) && !intersects(frontier, pair.preState())) {
					continue;
				}
				iterator.remove();
				if (SmtUtils.isFalseLiteral(pair.postState().getFormula())) {
					continue;
				}
				if (!hasGenerated) {
					generated = pair.postState();
					hasGenerated = true;
				} else {
					generated = domain.join(generated, pair.postState());
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

	private Map<AbstractLocationPair, PrePostPair> buildFiltered(final Set<String> activeThreadIds) {
		final Map<AbstractLocationPair, PrePostPair> filtered = new LinkedHashMap<>();
		for (final Entry<ThreadedKey, PrePostPair> e : mInterferenceByKey.entrySet()) {
			if (activeThreadIds.contains(e.getKey().threadId())) {
				filtered.put(e.getKey().pair(), e.getValue());
			}
		}
		return filtered;
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
		if (!(other instanceof final PrePostInterference typedOther)) {
			throw new IllegalArgumentException(
					"Cannot widen PrePostInterference with " + other.getClass().getSimpleName());
		}
		final Map<ThreadedKey, PrePostPair> widened = new LinkedHashMap<>();
		for (final Entry<ThreadedKey, PrePostPair> entry : mInterferenceByKey.entrySet()) {
			IThreadLocalDomainContext.setIfApplicable(domain, entry.getKey().threadId());
			final PrePostPair otherGroup = typedOther.mInterferenceByKey.get(entry.getKey());
			final PrePostPair widenedGroup = otherGroup == null ? entry.getValue()
					: new PrePostPair(domain.widen(entry.getValue().preState(), otherGroup.preState()),
							domain.widen(entry.getValue().postState(), otherGroup.postState()));
			if (!isTrivialPair(widenedGroup)) {
				widened.put(entry.getKey(), widenedGroup);
			}
		}
		for (final Entry<ThreadedKey, PrePostPair> entry : typedOther.mInterferenceByKey.entrySet()) {
			if (!widened.containsKey(entry.getKey()) && !isTrivialPair(entry.getValue())) {
				widened.put(entry.getKey(), entry.getValue());
			}
		}
		return widened.isEmpty() ? null
				: new PrePostInterference(widened, mManagedScript, mBucketDomain, mFalsePredicate);
	}

	@Override
	public boolean isSubsumedBy(final IInterference other, final IDomain domain) {
		if (!(other instanceof final PrePostInterference typedOther)) {
			return false;
		}
		for (final Entry<ThreadedKey, PrePostPair> entry : mInterferenceByKey.entrySet()) {
			IThreadLocalDomainContext.setIfApplicable(domain, entry.getKey().threadId());
			final PrePostPair otherGroup = typedOther.mInterferenceByKey.get(entry.getKey());
			if (otherGroup == null
					|| !domain.isSubsetEq(entry.getValue().preState(), otherGroup.preState()).isTrueForAbstraction()
					|| !domain.isSubsetEq(entry.getValue().postState(), otherGroup.postState())
							.isTrueForAbstraction()) {
				return false;
			}
		}
		return true;
	}

	private boolean intersects(final IPredicate state, final IPredicate preState) {
		final Script script = mManagedScript.getScript();
		final Term guardedState =
				SmtUtils.andWithExtendedLocalSimplification(script, state.getFormula(), preState.getFormula());
		return !SmtUtils.isFalseLiteral(guardedState)
				&& SmtUtils.checkSatTerm(script, guardedState) != Script.LBool.UNSAT;
	}

	private static boolean isTrivialPair(final PrePostPair pair) {
		return SmtUtils.isFalseLiteral(pair.preState().getFormula())
				|| SmtUtils.isFalseLiteral(pair.postState().getFormula());
	}
}
