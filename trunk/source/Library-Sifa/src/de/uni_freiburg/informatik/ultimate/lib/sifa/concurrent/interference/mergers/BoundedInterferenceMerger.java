package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.mergers;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
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
				result.put(threadId, mergeByFolding(threadItfs, domain));
			}
		}
		return InterferenceAbstraction.of(result);
	}

	private Set<IPredicate> mergeByFolding(final Set<IPredicate> threadItfs, final IDomain domain) {
		final List<IPredicate> work = new ArrayList<>(threadItfs);
		work.sort(Comparator.comparing(IPredicate::toString));

		while (work.size() > mMaxPerThread) {
			final int last = work.size() - 1;
			final IPredicate p = work.remove(last);
			final IPredicate q = work.remove(last - 1);

			IPredicate merged = domain.join(q, p);
			if (mApplyAlpha) {
				merged = domain.alpha(merged);
			}
			work.add(merged);
		}
		return new HashSet<>(work);
	}
}
