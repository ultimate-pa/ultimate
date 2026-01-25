package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceOrchestrator;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

/**
 * Wrapper domain for thread-modular analysis.
 *
 * Applies interference abstraction in the alpha function to account for possible interleavings from other threads.
 */
public class ConcurrentDomain implements IDomain {

	private final IDomain mUnderlyingDomain;
	private final InterferenceOrchestrator mInterferenceOrchestrator;
	private final String mThreadId;

	/**
	 * Creates a concurrent domain for analyzing a specific thread.
	 *
	 * @param underlyingDomain         The base abstract domain.
	 * @param interferenceOrchestrator The shared interference abstraction.
	 * @param threadId                 The thread being analyzed.
	 */
	public ConcurrentDomain(final IDomain underlyingDomain, final InterferenceOrchestrator interferenceOrchestrator,
			final String threadId) {
		mUnderlyingDomain = underlyingDomain;
		mInterferenceOrchestrator = interferenceOrchestrator;
		mThreadId = threadId;
	}

	@Override
	public IPredicate join(final IPredicate lhs, final IPredicate rhs) {
		return mUnderlyingDomain.join(lhs, rhs);
	}

	@Override
	public IPredicate widen(final IPredicate old, final IPredicate widenWith) {
		return mUnderlyingDomain.widen(old, widenWith);
	}

	@Override
	public ResultForAlteredInputs isEqBottom(final IPredicate pred) {
		return mUnderlyingDomain.isEqBottom(pred);
	}

	@Override
	public ResultForAlteredInputs isSubsetEq(final IPredicate subset, final IPredicate superset) {
		return mUnderlyingDomain.isSubsetEq(subset, superset);
	}

	@Override
	public IPredicate alpha(final IPredicate pred) {
		final IPredicate abstracted = mUnderlyingDomain.alpha(pred);
		return mInterferenceOrchestrator.itfFixpoint(abstracted, mThreadId);
	}

	public IDomain getUnderlyingDomain() {
		return mUnderlyingDomain;
	}

	public InterferenceOrchestrator getInterferenceOrchestrator() {
		return mInterferenceOrchestrator;
	}

	public String getThreadId() {
		return mThreadId;
	}
}
