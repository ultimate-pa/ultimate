package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

public class ConcurrentDomain implements ILocationAwareDomain {

	private final IDomain mUnderlyingDomain;
	private final String mThreadId;
	private IInterferenceAbstraction mInterferences;
	private Set<IcfgLocation> mInterferenceLocations;

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

	public void setInterferenceLocations(final Set<IcfgLocation> locations) {
		mInterferenceLocations = locations;
	}

	@Override
	public IPredicate alpha(final IPredicate pred) {
		return alpha(pred, null);
	}

	@Override
	public IPredicate alpha(final IPredicate pred, final IcfgLocation location) {
		IPredicate state = pred;
		if (shouldApplyInterferences(location)) {
			state = mInterferences.applyToState(state, mThreadId, mUnderlyingDomain, location);
		}
		// TODO: alpha before or after interference fixpoint?
		return mUnderlyingDomain.alpha(state);
	}

	private boolean shouldApplyInterferences(final IcfgLocation location) {
		if (mInterferenceLocations == null) {
			return true;
		}
		return location != null && mInterferenceLocations.contains(location);
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
