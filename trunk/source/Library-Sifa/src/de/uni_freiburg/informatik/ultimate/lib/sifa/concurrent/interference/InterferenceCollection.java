package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.IThreadLocalDomainContext;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class InterferenceCollection {

	private final Map<String, IInterference> mInterferencesByThread;

	private InterferenceCollection(final Map<String, IInterference> interferences) {
		mInterferencesByThread = Map.copyOf(interferences);
	}

	public static InterferenceCollection empty() {
		return new InterferenceCollection(Map.of());
	}

	public static InterferenceCollection of(final Map<String, IInterference> interferences) {
		return new InterferenceCollection(interferences);
	}

	public Set<String> getThreadIds() {
		return Set.copyOf(mInterferencesByThread.keySet());
	}

	public int getInterferenceCount(final String threadId) {
		final IInterference itf = mInterferencesByThread.get(threadId);
		return itf == null ? 0 : itf.size();
	}

	public boolean isEmpty() {
		return mInterferencesByThread.isEmpty();
	}

	public IInterference getInterferenceForThread(final String threadId) {
		return mInterferencesByThread.get(threadId);
	}

	public boolean hasConverged(final InterferenceCollection previous, final IDomain domain) {
		final Set<String> allThreads = DataStructureUtils.union(mInterferencesByThread.keySet(),
				previous.mInterferencesByThread.keySet());
		for (final String threadId : allThreads) {
			configureDomainContext(domain, threadId);
			final IInterference newItf = mInterferencesByThread.get(threadId);
			final IInterference oldItf = previous.mInterferencesByThread.get(threadId);
			if (newItf == null) {
				// Missing entry means trivial interference; always subsumed
				continue;
			}
			if (oldItf == null || !newItf.isSubsumedBy(oldItf, domain)) {
				return false;
			}
		}
		return true;
	}

	public InterferenceCollection widen(final InterferenceCollection other, final IDomain domain) {
		final Set<String> allThreads = DataStructureUtils.union(mInterferencesByThread.keySet(),
				other.mInterferencesByThread.keySet());
		final Map<String, IInterference> widened = new HashMap<>();

		for (final String threadId : allThreads) {
			configureDomainContext(domain, threadId);
			final IInterference thisItf = mInterferencesByThread.get(threadId);
			final IInterference otherItf = other.mInterferencesByThread.get(threadId);

			final IInterference widenedItf;
			if (thisItf == null) {
				widenedItf = otherItf;
			} else if (otherItf == null) {
				widenedItf = thisItf;
			} else {
				widenedItf = thisItf.widen(otherItf, domain);
			}

			if (widenedItf != null && !widenedItf.isTrivial()) {
				widened.put(threadId, widenedItf);
			}
		}

		return new InterferenceCollection(widened);
	}

	private static void configureDomainContext(final IDomain domain, final String threadId) {
		if (domain instanceof final IThreadLocalDomainContext threadLocalDomainContext) {
			threadLocalDomainContext.setCurrentThreadId(threadId);
		}
	}
}
