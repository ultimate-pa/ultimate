package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

public class DefaultInterferenceAbstraction implements IInterferenceAbstraction {

	private static final int DEFAULT_WIDENING_THRESHOLD = 3;

	private final Map<String, Set<IPredicate>> mInterferencesByThread;
	private final RelationalPredicatePostcondition mPostcondition;
	private final int mWideningThreshold;

	private DefaultInterferenceAbstraction(final Map<String, Set<IPredicate>> interferences,
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

	public static DefaultInterferenceAbstraction of(final Map<String, Set<IPredicate>> interferences,
			final RelationalPredicatePostcondition postcondition) {
		return new DefaultInterferenceAbstraction(interferences, postcondition, DEFAULT_WIDENING_THRESHOLD);
	}

	public Set<IPredicate> getInterferencesProducedBy(final String threadId) {
		return mInterferencesByThread.getOrDefault(threadId, Collections.emptySet());
	}

	@Override
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

	@Override
	public boolean isEmpty() {
		return mInterferencesByThread.isEmpty() || mInterferencesByThread.values().stream().allMatch(Set::isEmpty);
	}

	@Override
	public IPredicate applyToState(final IPredicate state, final String threadId, final IDomain domain) {
		return applyToState(state, threadId, domain, null);
	}

	@Override
	public IPredicate applyToState(final IPredicate state, final String threadId, final IDomain domain,
			final IcfgLocation location) {
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

	public boolean hasConverged(final IInterferenceAbstraction previous, final IDomain domain,
			final de.uni_freiburg.informatik.ultimate.core.model.services.ILogger logger) {
		if (!(previous instanceof DefaultInterferenceAbstraction)) {
			throw new IllegalArgumentException("Cannot compare different abstraction types");
		}
		final DefaultInterferenceAbstraction prev = (DefaultInterferenceAbstraction) previous;

		for (final String threadId : mInterferencesByThread.keySet()) {
			final Set<IPredicate> newSet = getInterferencesProducedBy(threadId);
			final Set<IPredicate> oldSet = prev.getInterferencesProducedBy(threadId);

			for (final IPredicate newItf : newSet) {
				if (!isSubsumedByAny(newItf, oldSet, domain)) {
					if (logger != null) {
						logger.info("  Thread %s: interference not subsumed: %s", threadId, newItf.getFormula());
						logger.info("    Old set size: %d, New set size: %d", oldSet.size(), newSet.size());
					}
					return false;
				}
			}
		}
		return true;
	}

	private static boolean isSubsumedByAny(final IPredicate pred, final Set<IPredicate> set, final IDomain domain) {
		for (final IPredicate candidate : set) {
			if (domain.isSubsetEq(pred, candidate).isTrueForAbstraction()) {
				return true;
			}
		}
		return false;
	}

	public static DefaultInterferenceAbstraction ofForTesting(final Map<String, Set<IPredicate>> interferences) {
		return new DefaultInterferenceAbstraction(interferences, null, DEFAULT_WIDENING_THRESHOLD);
	}
}
