package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.poststate;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.IThreadLocalDomainContext;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping.ThreadedKey;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

public final class PostStateInterference implements IInterference {

	private final Map<ThreadedKey, IPredicate> mInterferenceByKey;

	public PostStateInterference(final Map<ThreadedKey, IPredicate> interferenceByKey) {
		mInterferenceByKey = Map.copyOf(interferenceByKey);
	}

	@Override
	public IPredicate applyUntilFixpoint(final IPredicate state, final Set<String> activeThreadIds,
			final IDomain domain, final int wideningThreshold, final SifaStats stats) {
		final Collection<IPredicate> filtered = buildFiltered(activeThreadIds);
		if (filtered.isEmpty()) {
			return state;
		}
		IPredicate result = state;
		for (final IPredicate groupedInterference : filtered) {
			result = domain.join(result, groupedInterference);
		}
		return result;
	}

	private Collection<IPredicate> buildFiltered(final Set<String> activeThreadIds) {
		final List<IPredicate> filtered = new ArrayList<>();
		for (final Entry<ThreadedKey, IPredicate> e : mInterferenceByKey.entrySet()) {
			if (activeThreadIds.contains(e.getKey().threadId())) {
				filtered.add(e.getValue());
			}
		}
		return filtered;
	}

	@Override
	public boolean isEmpty() {
		return mInterferenceByKey.isEmpty();
	}

	@Override
	public Set<String> threadIds() {
		final Set<String> ids = new LinkedHashSet<>();
		mInterferenceByKey.keySet().forEach(k -> ids.add(k.threadId()));
		return Set.copyOf(ids);
	}

	@Override
	public IInterference widen(final IInterference other, final IDomain domain) {
		if (!(other instanceof final PostStateInterference typedOther)) {
			throw new IllegalArgumentException(
					"Cannot widen PostStateInterference with " + other.getClass().getSimpleName());
		}
		final Map<ThreadedKey, IPredicate> widened = new LinkedHashMap<>();
		for (final Entry<ThreadedKey, IPredicate> entry : mInterferenceByKey.entrySet()) {
			IThreadLocalDomainContext.setIfApplicable(domain, entry.getKey().threadId());
			final IPredicate otherGroup = typedOther.mInterferenceByKey.get(entry.getKey());
			final IPredicate widenedGroup = otherGroup == null ? entry.getValue()
					: domain.widen(entry.getValue(), otherGroup);
			if (!SmtUtils.isFalseLiteral(widenedGroup.getFormula())) {
				widened.put(entry.getKey(), widenedGroup);
			}
		}
		for (final Entry<ThreadedKey, IPredicate> entry : typedOther.mInterferenceByKey.entrySet()) {
			if (!widened.containsKey(entry.getKey())
					&& !SmtUtils.isFalseLiteral(entry.getValue().getFormula())) {
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
		for (final Entry<ThreadedKey, IPredicate> entry : mInterferenceByKey.entrySet()) {
			IThreadLocalDomainContext.setIfApplicable(domain, entry.getKey().threadId());
			final IPredicate otherGroup = typedOther.mInterferenceByKey.get(entry.getKey());
			if (otherGroup == null
					|| !domain.isSubsetEq(entry.getValue(), otherGroup).isTrueForAbstraction()) {
				return false;
			}
		}
		return true;
	}

}
