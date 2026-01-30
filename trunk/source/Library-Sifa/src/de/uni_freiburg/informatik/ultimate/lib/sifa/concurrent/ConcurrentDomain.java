package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

/**
 * Wrapper domain that applies interferences in alpha.
 */
public class ConcurrentDomain implements IDomain {

	private final IDomain mUnderlyingDomain;
	private final String mThreadId;
	private IInterferenceAbstraction mInterferences;

	public ConcurrentDomain(final IDomain underlyingDomain, final IInterferenceAbstraction interferences,
			final String threadId) {
		mUnderlyingDomain = underlyingDomain;
		mInterferences = interferences;
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
		final IPredicate itfState = mInterferences.applyToState(pred, mThreadId, mUnderlyingDomain);
		return mUnderlyingDomain.alpha(itfState);
	}

	public void setInterferences(final IInterferenceAbstraction interferences) {
		mInterferences = interferences;
	}

	public IInterferenceAbstraction getInterferences() {
		return mInterferences;
	}

	public IDomain getUnderlyingDomain() {
		return mUnderlyingDomain;
	}

	public String getThreadId() {
		return mThreadId;
	}
}
