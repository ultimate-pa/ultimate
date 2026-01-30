package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.mergers;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

/**
 * Joins all interferences into one predicate.
 */
public class JoiningInterferenceMerger implements IInterferenceMerger {

	private final boolean mApplyAlpha;

	public JoiningInterferenceMerger() {
		this(true);
	}

	public JoiningInterferenceMerger(final boolean applyAlpha) {
		mApplyAlpha = applyAlpha;
	}

	@Override
	public Set<IPredicate> merge(final Set<IPredicate> interferences, final IDomain domain) {
		if (interferences.isEmpty()) {
			return new HashSet<>();
		}

		IPredicate merged = null;
		for (final IPredicate itf : interferences) {
			merged = merged == null ? itf : domain.join(merged, itf);
		}

		if (mApplyAlpha && merged != null) {
			merged = domain.alpha(merged);
		}

		final Set<IPredicate> result = new HashSet<>();
		if (merged != null) {
			result.add(merged);
		}
		return result;
	}
}
