package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.poststate;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping.AbstractLocationPair;
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
		final Map<AbstractLocationPair, IPredicate> widened = new LinkedHashMap<>();
		for (final Entry<AbstractLocationPair, IPredicate> entry : mInterferenceByAbstractLocationPair.entrySet()) {
			final IPredicate otherGroup = typedOther.mInterferenceByAbstractLocationPair.get(entry.getKey());
			final IPredicate widenedGroup = otherGroup == null ? entry.getValue() : domain.widen(entry.getValue(), otherGroup);
			if (!isFalseLiteral(widenedGroup)) {
				widened.put(entry.getKey(), widenedGroup);
			}
		}
		for (final Entry<AbstractLocationPair, IPredicate> entry : typedOther.mInterferenceByAbstractLocationPair.entrySet()) {
			if (!widened.containsKey(entry.getKey()) && !isFalseLiteral(entry.getValue())) {
				widened.put(entry.getKey(), entry.getValue());
			}
		}
		return widened.isEmpty() ? null : new PostStateInterference(widened);
	}

	@Override
	public boolean isSubsumedBy(final IInterference other, final IDomain domain) {
		if (!(other instanceof final PostStateInterference typedOther)) {
			return false;
		}
		for (final Entry<AbstractLocationPair, IPredicate> entry : mInterferenceByAbstractLocationPair.entrySet()) {
			final IPredicate otherGroup = typedOther.mInterferenceByAbstractLocationPair.get(entry.getKey());
			if (otherGroup == null || !domain.isSubsetEq(entry.getValue(), otherGroup).isTrueForAbstraction()) {
				return false;
			}
		}
		return true;
	}

	private static boolean isFalseLiteral(final IPredicate predicate) {
		return SmtUtils.isFalseLiteral(predicate.getFormula());
	}
}
