package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.poststate;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping.AbstractLocationPair;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceMethodHelpers;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

public final class PostStateInterference implements IInterference {

	private final Map<AbstractLocationPair, IPredicate> mInterferenceByAbstractLocationPair;

	public PostStateInterference(final Map<AbstractLocationPair, IPredicate> interferenceByAbstractLocationPair) {
		mInterferenceByAbstractLocationPair = Map.copyOf(interferenceByAbstractLocationPair);
	}

	@Override
	public IPredicate applyUntilFixpoint(final IPredicate state, final IDomain domain, final int wideningThreshold,
			final SifaStats stats) {
		IPredicate result = state;
		for (final IPredicate groupedInterference : mInterferenceByAbstractLocationPair.values()) {
			result = domain.join(result, groupedInterference);
		}
		return result;
	}

	@Override
	public IInterference widen(final IInterference other, final IDomain domain) {
		if (!(other instanceof final PostStateInterference typedOther)) {
			throw new IllegalArgumentException(
					"Cannot widen PostStateInterference with " + other.getClass().getSimpleName());
		}
		return new PostStateInterference(InterferenceMethodHelpers.widen(mInterferenceByAbstractLocationPair,
				typedOther.mInterferenceByAbstractLocationPair, domain::widen));
	}

	@Override
	public boolean isSubsumedBy(final IInterference other, final IDomain domain) {
		return other instanceof final PostStateInterference typedOther && InterferenceMethodHelpers.isSubsumed(
				mInterferenceByAbstractLocationPair, typedOther.mInterferenceByAbstractLocationPair,
				(left, right) -> domain.isSubsetEq(left, right).isTrueForAbstraction());
	}

	@Override
	public boolean isTrivial() {
		return mInterferenceByAbstractLocationPair.isEmpty() || mInterferenceByAbstractLocationPair.values().stream()
				.allMatch(predicate -> SmtUtils.isFalseLiteral(predicate.getFormula()));
	}

	@Override
	public int size() {
		return mInterferenceByAbstractLocationPair.size();
	}
}
