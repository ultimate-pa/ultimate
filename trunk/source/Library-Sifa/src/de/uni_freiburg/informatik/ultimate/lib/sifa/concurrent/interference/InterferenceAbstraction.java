package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Maps each thread to the interferences it produced.
 */
public class InterferenceAbstraction {

	private final Map<String, Set<IPredicate>> mInterferencesByThread;

	private InterferenceAbstraction(final Map<String, Set<IPredicate>> interferences) {
		mInterferencesByThread = new HashMap<>(interferences);
	}

	public static InterferenceAbstraction empty() {
		return new InterferenceAbstraction(new HashMap<>());
	}

	public static InterferenceAbstraction of(final Map<String, Set<IPredicate>> interferences) {
		return new InterferenceAbstraction(interferences);
	}

	public Set<IPredicate> getInterferencesProducedBy(final String threadId) {
		return mInterferencesByThread.getOrDefault(threadId, Collections.emptySet());
	}

	/**
	 * Returns interferences from all threads except the given one.
	 */
	public Set<IPredicate> getInterferencesForOtherThreads(final String excludeThread) {
		final Set<IPredicate> result = new HashSet<>();
		for (final Map.Entry<String, Set<IPredicate>> entry : mInterferencesByThread.entrySet()) {
			if (!entry.getKey().equals(excludeThread)) {
				result.addAll(entry.getValue());
			}
		}
		return result;
	}

	public Set<String> getThreadIds() {
		return Collections.unmodifiableSet(mInterferencesByThread.keySet());
	}

	public boolean isEmpty() {
		return mInterferencesByThread.isEmpty() || mInterferencesByThread.values().stream().allMatch(Set::isEmpty);
	}

}
