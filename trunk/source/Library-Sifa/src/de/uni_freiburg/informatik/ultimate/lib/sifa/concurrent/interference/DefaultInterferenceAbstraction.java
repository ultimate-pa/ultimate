package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

public class DefaultInterferenceAbstraction implements IInterferenceAbstraction {

	private static final int DEFAULT_WIDENING_THRESHOLD = 3;

	private final Map<String, Map<IcfgLocation, IPredicate>> mInterferencesByThread;
	private final RelationalPredicatePostcondition mPostcondition;
	private final int mWideningThreshold;

	private DefaultInterferenceAbstraction(final Map<String, Map<IcfgLocation, IPredicate>> interferences,
			final RelationalPredicatePostcondition postcondition, final int wideningThreshold) {
		mInterferencesByThread = new HashMap<>(interferences);
		mPostcondition = postcondition;
		mWideningThreshold = wideningThreshold;
	}

	private static boolean isTrue(final IPredicate pred) {
		return SmtUtils.isTrueLiteral(pred.getFormula());
	}

	private static boolean isFalse(final IPredicate pred) {
		return SmtUtils.isFalseLiteral(pred.getFormula());
	}

	private static boolean isTrivial(final IPredicate pred) {
		return isTrue(pred) || isFalse(pred);
	}

	public static DefaultInterferenceAbstraction empty(final RelationalPredicatePostcondition postcondition) {
		return new DefaultInterferenceAbstraction(new HashMap<>(), postcondition, DEFAULT_WIDENING_THRESHOLD);
	}

	public static DefaultInterferenceAbstraction of(final Map<String, Map<IcfgLocation, IPredicate>> interferences,
			final RelationalPredicatePostcondition postcondition) {
		return new DefaultInterferenceAbstraction(interferences, postcondition, DEFAULT_WIDENING_THRESHOLD);
	}

	public Map<IcfgLocation, IPredicate> getInterferencesProducedBy(final String threadId) {
		return mInterferencesByThread.getOrDefault(threadId, Collections.emptyMap());
	}

	public int getInterferenceCount(final String threadId) {
		return getInterferencesProducedBy(threadId).size();
	}

	@Override
	public Set<IPredicate> getInterferencesForOtherThreads(final String excludeThread) {
		final Set<IPredicate> result = new HashSet<>();
		for (final Map.Entry<String, Map<IcfgLocation, IPredicate>> entry : mInterferencesByThread.entrySet()) {
			if (!entry.getKey().equals(excludeThread)) {
				result.addAll(entry.getValue().values());
			}
		}
		return result;
	}

	public Set<String> getThreadIds() {
		return Collections.unmodifiableSet(mInterferencesByThread.keySet());
	}

	@Override
	public boolean isEmpty() {
		return mInterferencesByThread.isEmpty() || mInterferencesByThread.values().stream().allMatch(Map::isEmpty);
	}

	/**
	 * Repeatedly applies interferences until the state stabilizes.
	 * Switches from join to widen after {@link #mWideningThreshold} iterations to ensure termination.
	 */
	@Override
	public IPredicate applyToState(final IPredicate state, final String threadId, final IDomain domain) {
		if (isEmpty() || isTrue(state)) {
			return state;
		}

		final Set<IPredicate> interferences = getInterferencesForOtherThreads(threadId);
		final Set<IPredicate> nonTrivialInterferences = interferences.stream().filter(itf -> !isTrivial(itf))
				.collect(Collectors.toSet());

		if (nonTrivialInterferences.isEmpty()) {
			return state;
		}

		IPredicate current = state;
		boolean changed = true;
		int iteration = 0;

		while (changed) {
			changed = false;
			iteration++;

			final IPredicate postState = applyOnce(current, nonTrivialInterferences, domain);
			final boolean widen = iteration > mWideningThreshold;
			final IPredicate combined = widen ? domain.widen(current, postState) : domain.join(current, postState);

			if (!domain.isSubsetEq(combined, current).isTrueForAbstraction()) {
				current = combined;
				changed = true;
			}
		}

		return current;
	}

	private IPredicate applyOnce(final IPredicate state, final Set<IPredicate> interferences, final IDomain domain) {
		if (interferences.isEmpty()) {
			return state;
		}

		IPredicate joinedPost = null;
		for (final IPredicate interference : interferences) {
			final IPredicate postState = mPostcondition.strongestPostcondition(state, interference);
			joinedPost = joinedPost == null ? postState : domain.join(joinedPost, postState);
		}
		return joinedPost == null ? state : joinedPost;
	}

	@Override
	public boolean hasConverged(final IInterferenceAbstraction previous, final IDomain domain) {
		return hasConverged(previous, domain, null);
	}

	/** Converged iff every new interference is subsumed by the corresponding old one. */
	public boolean hasConverged(final IInterferenceAbstraction previous, final IDomain domain,
			final de.uni_freiburg.informatik.ultimate.core.model.services.ILogger logger) {
		if (!(previous instanceof DefaultInterferenceAbstraction)) {
			throw new IllegalArgumentException("Cannot compare different abstraction types");
		}
		final DefaultInterferenceAbstraction prev = (DefaultInterferenceAbstraction) previous;

		for (final String threadId : mInterferencesByThread.keySet()) {
			final Map<IcfgLocation, IPredicate> newMap = getInterferencesProducedBy(threadId);
			final Map<IcfgLocation, IPredicate> oldMap = prev.getInterferencesProducedBy(threadId);

			for (final Map.Entry<IcfgLocation, IPredicate> entry : newMap.entrySet()) {
				final IcfgLocation loc = entry.getKey();
				final IPredicate newItf = entry.getValue();
				final IPredicate oldItf = oldMap.get(loc);

				if (oldItf == null || !domain.isSubsetEq(newItf, oldItf).isTrueForAbstraction()) {
					if (logger != null) {
						logger.info("  Thread %s at %s: interference not subsumed: %s", threadId, loc,
								newItf.getFormula());
					}
					return false;
				}
			}
		}
		return true;
	}

	public static DefaultInterferenceAbstraction ofForTesting(
			final Map<String, Map<IcfgLocation, IPredicate>> interferences) {
		return new DefaultInterferenceAbstraction(interferences, null, DEFAULT_WIDENING_THRESHOLD);
	}

	@Override
	public boolean canApply(final IPredicate state, final String threadId, final IDomain domain) {
		return false;
	}

	@Override
	public IInterferenceAbstraction widen(final IInterferenceAbstraction other, final IDomain domain) {
		if (!(other instanceof DefaultInterferenceAbstraction)) {
			throw new UnsupportedOperationException("Can only widen with DefaultInterferenceAbstraction");
		}
		final DefaultInterferenceAbstraction otherDefault = (DefaultInterferenceAbstraction) other;
		final Map<String, Map<IcfgLocation, IPredicate>> widenedInterferences = new HashMap<>();

		final Set<String> allThreads = DataStructureUtils.union(mInterferencesByThread.keySet(),
				otherDefault.mInterferencesByThread.keySet());

		for (final String threadId : allThreads) {
			final Map<IcfgLocation, IPredicate> thisMap = mInterferencesByThread.getOrDefault(threadId, Map.of());
			final Map<IcfgLocation, IPredicate> otherMap = otherDefault.mInterferencesByThread.getOrDefault(threadId,
					Map.of());

			final Map<IcfgLocation, IPredicate> widenedMap = new HashMap<>();

			final Set<IcfgLocation> allLocs = DataStructureUtils.union(thisMap.keySet(), otherMap.keySet());

			for (final IcfgLocation loc : allLocs) {
				final IPredicate thisPred = thisMap.get(loc);
				final IPredicate otherPred = otherMap.get(loc);

				final IPredicate widened;
				if (thisPred == null) {
					widened = otherPred;
				} else if (otherPred == null) {
					widened = thisPred;
				} else {
					widened = domain.widen(thisPred, otherPred);
				}

				if (!isTrivial(widened)) {
					widenedMap.put(loc, widened);
				}
			}

			if (!widenedMap.isEmpty()) {
				widenedInterferences.put(threadId, widenedMap);
			}
		}

		return new DefaultInterferenceAbstraction(widenedInterferences, mPostcondition, mWideningThreshold);
	}
}
