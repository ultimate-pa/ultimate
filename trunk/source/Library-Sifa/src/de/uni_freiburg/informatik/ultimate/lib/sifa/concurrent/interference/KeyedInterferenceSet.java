package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.IThreadLocalDomainContext;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats.Key;

public abstract class KeyedInterferenceSet<G> implements IInterferenceSet {

	protected final Map<InterferenceGroupKey, G> mSummaryByKey;
	protected final Map<String, Set<IcfgLocation>> mPreForkSourcesByThread;

	protected KeyedInterferenceSet(final Map<InterferenceGroupKey, G> summaryByKey,
			final Map<String, Set<IcfgLocation>> preForkSourcesByThread) {
		mSummaryByKey = Collections.unmodifiableMap(new LinkedHashMap<>(summaryByKey));
		mPreForkSourcesByThread = Collections.unmodifiableMap(new LinkedHashMap<>(preForkSourcesByThread));
	}

	@Override
	public final boolean isEmpty() {
		return mSummaryByKey.isEmpty();
	}

	@Override
	public final int summaryCount() {
		return mSummaryByKey.size();
	}

	@Override
	public final Set<String> threadIds() {
		final Set<String> ids = new LinkedHashSet<>();
		mSummaryByKey.keySet().forEach(key -> ids.add(key.threadId()));
		return Set.copyOf(ids);
	}

	protected final List<Entry<InterferenceGroupKey, G>> selectApplicableSummaries(final String observerThreadId,
			final Set<String> activeThreadIds, final Set<String> observerLockset, final SifaStats stats) {
		final List<Entry<InterferenceGroupKey, G>> applicable = new ArrayList<>();
		for (final Entry<InterferenceGroupKey, G> entry : mSummaryByKey.entrySet()) {
			final InterferenceGroupKey key = entry.getKey();
			if (!activeThreadIds.contains(key.threadId())) {
				continue;
			}
			if (observerThreadId.equals(key.forkedThreadId())) {
				continue;
			}
			if (happensBeforeObserverFork(observerThreadId, key.sourceLocations())) {
				continue;
			}
			if (excludedByMutualExclusion(key.lockset(), observerLockset)) {
				stats.increment(Key.INTERFERENCE_LOCKSET_FILTERED);
				continue;
			}
			applicable.add(entry);
		}
		stats.add(Key.INTERFERENCE_SUMMARIES_APPLIED, applicable.size());
		return applicable;
	}

	private boolean happensBeforeObserverFork(final String observerThreadId, final Set<IcfgLocation> sourceLocations) {
		final Set<IcfgLocation> preForkSources = mPreForkSourcesByThread.getOrDefault(observerThreadId, Set.of());
		return !sourceLocations.isEmpty() && preForkSources.containsAll(sourceLocations);
	}

	private static boolean excludedByMutualExclusion(final Set<String> writerLockset,
			final Set<String> observerLockset) {
		if (observerLockset.isEmpty()) {
			return false;
		}
		return !writerLockset.isEmpty() && !Collections.disjoint(writerLockset, observerLockset);
	}

	@Override
	public final IInterferenceSet widen(final IInterferenceSet other, final IDomain domain) {
		if (getClass() != other.getClass()) {
			throw new IllegalArgumentException(
					"Cannot widen " + getClass().getSimpleName() + " with " + other.getClass().getSimpleName());
		}
		final KeyedInterferenceSet<G> typedOther = (KeyedInterferenceSet<G>) other;
		final Map<InterferenceGroupKey, G> widened = new LinkedHashMap<>();
		for (final Entry<InterferenceGroupKey, G> entry : mSummaryByKey.entrySet()) {
			IThreadLocalDomainContext.setIfApplicable(domain, entry.getKey().threadId());
			final G otherSummary = typedOther.mSummaryByKey.get(entry.getKey());
			final G widenedSummary;
			if (otherSummary == null) {
				widenedSummary = entry.getValue();
			} else if (summaryIsSubsumedBy(otherSummary, entry.getValue(), domain)) {
				widenedSummary = entry.getValue();
			} else {
				widenedSummary = widenSummaries(entry.getValue(), otherSummary, domain);
			}
			if (!isTrivialSummary(widenedSummary)) {
				widened.put(entry.getKey(), widenedSummary);
			}
		}
		for (final Entry<InterferenceGroupKey, G> entry : typedOther.mSummaryByKey.entrySet()) {
			if (!widened.containsKey(entry.getKey()) && !isTrivialSummary(entry.getValue())) {
				widened.put(entry.getKey(), entry.getValue());
			}
		}
		return widened.isEmpty() ? null : withSummaries(widened);
	}

	@Override
	public final boolean isSubsumedBy(final IInterferenceSet other, final IDomain domain) {
		if (getClass() != other.getClass()) {
			return false;
		}
		final KeyedInterferenceSet<G> typedOther = (KeyedInterferenceSet<G>) other;
		for (final Entry<InterferenceGroupKey, G> entry : mSummaryByKey.entrySet()) {
			IThreadLocalDomainContext.setIfApplicable(domain, entry.getKey().threadId());
			final G otherSummary = typedOther.mSummaryByKey.get(entry.getKey());
			if (otherSummary == null || !summaryIsSubsumedBy(entry.getValue(), otherSummary, domain)) {
				return false;
			}
		}
		return true;
	}

	protected abstract G widenSummaries(G left, G right, IDomain domain);

	protected abstract boolean isTrivialSummary(G summary);

	protected abstract boolean summaryIsSubsumedBy(G left, G right, IDomain domain);

	protected abstract KeyedInterferenceSet<G> withSummaries(Map<InterferenceGroupKey, G> summaries);
}
