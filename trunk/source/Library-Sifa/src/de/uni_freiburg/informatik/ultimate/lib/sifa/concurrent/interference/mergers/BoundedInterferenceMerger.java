package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.mergers;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

/**
 * Limits interferences to N by partitioning into buckets and joining.
 */
public class BoundedInterferenceMerger implements IInterferenceMerger {

	private static final int DEFAULT_MAX = 10;
	private final int mMax;
	private final boolean mApplyAlpha;

	public BoundedInterferenceMerger() {
		this(DEFAULT_MAX, true);
	}

	public BoundedInterferenceMerger(final int max) {
		this(max, true);
	}

	public BoundedInterferenceMerger(final int max, final boolean applyAlpha) {
		if (max < 1) {
			throw new IllegalArgumentException("max must be at least 1");
		}
		mMax = max;
		mApplyAlpha = applyAlpha;
	}

	@Override
	public Set<IPredicate> merge(final Set<IPredicate> interferences, final IDomain domain) {
		if (interferences.size() <= mMax) {
			return new HashSet<>(interferences);
		}
		return mergeByFolding(interferences, domain);
	}

	private Set<IPredicate> mergeByFolding(final Set<IPredicate> interferences, final IDomain domain) {
		final List<IPredicate> work = new ArrayList<>(interferences);
		work.sort(Comparator.comparing(IPredicate::toString));

		while (work.size() > mMax) {
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
