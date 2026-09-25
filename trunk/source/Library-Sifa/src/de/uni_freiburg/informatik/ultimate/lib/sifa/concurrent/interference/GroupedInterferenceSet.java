/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
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
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.domain.IThreadLocalDomainContext;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats.Key;

public abstract class GroupedInterferenceSet<I> implements IInterferenceSet {

	protected final Map<InterferenceGroupKey, I> mInterferenceByGroup;
	protected final Map<String, Set<IcfgLocation>> mSourcesBeforeForkByThread;

	protected GroupedInterferenceSet(final Map<InterferenceGroupKey, I> interferenceByGroup,
			final Map<String, Set<IcfgLocation>> sourcesBeforeForkByThread) {
		mInterferenceByGroup = Collections.unmodifiableMap(new LinkedHashMap<>(interferenceByGroup));
		mSourcesBeforeForkByThread = Collections.unmodifiableMap(new LinkedHashMap<>(sourcesBeforeForkByThread));
	}

	@Override
	public final boolean isEmpty() {
		return mInterferenceByGroup.isEmpty();
	}

	@Override
	public final int groupCount() {
		return mInterferenceByGroup.size();
	}

	@Override
	public final Set<String> threadIds() {
		final Set<String> ids = new LinkedHashSet<>();
		mInterferenceByGroup.keySet().forEach(key -> ids.add(key.threadId()));
		return Set.copyOf(ids);
	}

	protected final List<Entry<InterferenceGroupKey, I>> selectApplicableInterference(final String observerThreadId,
			final Set<String> activeThreadIds, final Set<String> observerLockset, final SifaStats stats) {
		final List<Entry<InterferenceGroupKey, I>> applicable = new ArrayList<>();
		for (final Entry<InterferenceGroupKey, I> entry : mInterferenceByGroup.entrySet()) {
			final InterferenceGroupKey key = entry.getKey();
			if (!activeThreadIds.contains(key.threadId())) {
				continue;
			}
			if (observerThreadId.equals(key.forkedThreadId())) {
				continue;
			}
			if (allSourcesPrecedeObserverFork(observerThreadId, key.sourceLocations())) {
				continue;
			}
			if (haveCommonLock(key.lockset(), observerLockset)) {
				stats.increment(Key.INTERFERENCE_LOCKSET_FILTERED);
				continue;
			}
			applicable.add(entry);
		}
		stats.add(Key.INTERFERENCE_SUMMARIES_APPLIED, applicable.size());
		return applicable;
	}

	private boolean allSourcesPrecedeObserverFork(final String observerThreadId, final Set<IcfgLocation> sourceLocations) {
		final Set<IcfgLocation> sourcesBeforeFork = mSourcesBeforeForkByThread.getOrDefault(observerThreadId, Set.of());
		return !sourceLocations.isEmpty() && sourcesBeforeFork.containsAll(sourceLocations);
	}

	private static boolean haveCommonLock(final Set<String> writerLockset,
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
		final GroupedInterferenceSet<I> typedOther = (GroupedInterferenceSet<I>) other;
		final Map<InterferenceGroupKey, I> widened = new LinkedHashMap<>();
		for (final Entry<InterferenceGroupKey, I> entry : mInterferenceByGroup.entrySet()) {
			IThreadLocalDomainContext.setIfApplicable(domain, entry.getKey().threadId());
			final I otherInterference = typedOther.mInterferenceByGroup.get(entry.getKey());
			final I widenedInterference;
			if (otherInterference == null) {
				widenedInterference = entry.getValue();
			} else if (isInterferenceSubsumedBy(otherInterference, entry.getValue(), domain)) {
				widenedInterference = entry.getValue();
			} else {
				widenedInterference = widenInterference(entry.getValue(), otherInterference, domain);
			}
			if (!isBottomInterference(widenedInterference)) {
				widened.put(entry.getKey(), widenedInterference);
			}
		}
		for (final Entry<InterferenceGroupKey, I> entry : typedOther.mInterferenceByGroup.entrySet()) {
			if (!widened.containsKey(entry.getKey()) && !isBottomInterference(entry.getValue())) {
				widened.put(entry.getKey(), entry.getValue());
			}
		}
		return widened.isEmpty() ? null : withInterference(widened);
	}

	@Override
	public final boolean isSubsumedBy(final IInterferenceSet other, final IDomain domain) {
		if (getClass() != other.getClass()) {
			return false;
		}
		final GroupedInterferenceSet<I> typedOther = (GroupedInterferenceSet<I>) other;
		for (final Entry<InterferenceGroupKey, I> entry : mInterferenceByGroup.entrySet()) {
			IThreadLocalDomainContext.setIfApplicable(domain, entry.getKey().threadId());
			final I otherInterference = typedOther.mInterferenceByGroup.get(entry.getKey());
			if (otherInterference == null || !isInterferenceSubsumedBy(entry.getValue(), otherInterference, domain)) {
				return false;
			}
		}
		return true;
	}

	protected abstract I widenInterference(I left, I right, IDomain domain);

	protected abstract boolean isBottomInterference(I interference);

	protected abstract boolean isInterferenceSubsumedBy(I left, I right, IDomain domain);

	protected abstract GroupedInterferenceSet<I> withInterference(Map<InterferenceGroupKey, I> interferenceByGroup);
}
