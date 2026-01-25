package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.mergers;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

/**
 * Joins all interferences per thread into one predicate.
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
	public InterferenceAbstraction merge(final InterferenceAbstraction interferences, final IDomain domain) {
		final Map<String, Set<IPredicate>> result = new HashMap<>();

		for (final String threadId : interferences.getThreadIds()) {
			final Set<IPredicate> threadItfs = interferences.getInterferencesProducedBy(threadId);
			if (threadItfs.isEmpty()) {
				result.put(threadId, new HashSet<>());
				continue;
			}

			IPredicate merged = null;
			for (final IPredicate itf : threadItfs) {
				merged = merged == null ? itf : domain.join(merged, itf);
			}
			if (mApplyAlpha && merged != null) {
				merged = domain.alpha(merged);
			}

			final Set<IPredicate> singleton = new HashSet<>();
			if (merged != null) {
				singleton.add(merged);
			}
			result.put(threadId, singleton);
		}

		return InterferenceAbstraction.of(result);
	}
}
