package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.mergers;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

/**
 * Limits interferences per thread to N by partitioning into buckets and joining.
 */
public class BoundedInterferenceMerger implements IInterferenceMerger {

	private static final int DEFAULT_MAX_PER_THREAD = 10;
	private final int mMaxPerThread;
	private final boolean mApplyAlpha;

	public BoundedInterferenceMerger() {
		this(DEFAULT_MAX_PER_THREAD, true);
	}

	public BoundedInterferenceMerger(final int maxPerThread) {
		this(maxPerThread, true);
	}

	public BoundedInterferenceMerger(final int maxPerThread, final boolean applyAlpha) {
		if (maxPerThread < 1) {
			throw new IllegalArgumentException("maxPerThread must be at least 1");
		}
		mMaxPerThread = maxPerThread;
		mApplyAlpha = applyAlpha;
	}

	@Override
	public InterferenceAbstraction merge(final InterferenceAbstraction interferences, final IDomain domain) {
		final Map<String, Set<IPredicate>> result = new HashMap<>();
		for (final String threadId : interferences.getThreadIds()) {
			final Set<IPredicate> threadItfs = interferences.getInterferencesProducedBy(threadId);
			if (threadItfs.size() <= mMaxPerThread) {
				result.put(threadId, new HashSet<>(threadItfs));
			} else {
				result.put(threadId, mergeIntoBuckets(new ArrayList<>(threadItfs), domain));
			}
		}
		return InterferenceAbstraction.of(result);
	}

	private Set<IPredicate> mergeIntoBuckets(final List<IPredicate> itfs, final IDomain domain) {
		final int total = itfs.size();
		final Set<IPredicate> result = new HashSet<>();

		for (int bucket = 0; bucket < mMaxPerThread; bucket++) {
			final int start = bucket * total / mMaxPerThread;
			final int end = (bucket + 1) * total / mMaxPerThread;
			if (start >= end) {
				continue;
			}

			IPredicate merged = itfs.get(start);
			for (int i = start + 1; i < end; i++) {
				merged = domain.join(merged, itfs.get(i));
			}
			if (mApplyAlpha) {
				merged = domain.alpha(merged);
			}
			result.add(merged);
		}
		return result;
	}
}
