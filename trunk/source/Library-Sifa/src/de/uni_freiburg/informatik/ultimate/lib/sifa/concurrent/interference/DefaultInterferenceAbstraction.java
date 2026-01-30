package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

/**
 * Maps each thread to its interferences. Handles application with internal fixpoint.
 */
public class DefaultInterferenceAbstraction implements IInterferenceAbstraction {

	private static final int DEFAULT_WIDENING_THRESHOLD = 3;

	private final Map<String, Set<IPredicate>> mInterferencesByThread;
	private final RelationalPredicatePostcondition mPostcondition;
	private final int mWideningThreshold;

	// Debug logging (removable)
	private ILogger mLogger;

	private DefaultInterferenceAbstraction(final Map<String, Set<IPredicate>> interferences,
			final RelationalPredicatePostcondition postcondition, final int wideningThreshold) {
		mInterferencesByThread = new HashMap<>(interferences);
		mPostcondition = postcondition;
		mWideningThreshold = wideningThreshold;
	}

	public void setLogger(final ILogger logger) {
		mLogger = logger;
	}

	private static boolean isTrue(final IPredicate pred) {
		return SmtUtils.isTrueLiteral(pred.getFormula());
	}

	public static DefaultInterferenceAbstraction empty(final RelationalPredicatePostcondition postcondition) {
		return new DefaultInterferenceAbstraction(new HashMap<>(), postcondition, DEFAULT_WIDENING_THRESHOLD);
	}

	public static DefaultInterferenceAbstraction of(final Map<String, Set<IPredicate>> interferences,
			final RelationalPredicatePostcondition postcondition) {
		return new DefaultInterferenceAbstraction(interferences, postcondition, DEFAULT_WIDENING_THRESHOLD);
	}

	public static DefaultInterferenceAbstraction of(final Map<String, Set<IPredicate>> interferences,
			final RelationalPredicatePostcondition postcondition, final int wideningThreshold) {
		return new DefaultInterferenceAbstraction(interferences, postcondition, wideningThreshold);
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
		if (isEmpty() || isTrue(state)) {
			return state;
		}

		if (mLogger != null) {
			mLogger.info("[ITF] Thread %s: starting state = %s", threadId, state.getFormula());
		}

		IPredicate current = state;
		boolean changed = true;
		int iteration = 0;

		while (changed) {
			changed = false;
			iteration++;

			final IPredicate postState = applyOnce(current, threadId, domain);
			final IPredicate combined = iteration > mWideningThreshold ? domain.widen(current, postState)
					: domain.join(current, postState);

			if (mLogger != null) {
				mLogger.info("[ITF] Thread %s iter %d: after join/widen = %s", threadId, iteration,
						combined.getFormula());
			}

			if (!domain.isSubsetEq(combined, current).isTrueForAbstraction()) {
				current = combined;
				changed = true;
			}
		}

		if (mLogger != null) {
			mLogger.info("[ITF] Thread %s: final state = %s", threadId, current.getFormula());
		}

		return current;
	}

	private IPredicate applyOnce(final IPredicate state, final String threadId, final IDomain domain) {
		final Set<IPredicate> interferences = getInterferencesForOtherThreads(threadId);
		if (interferences.isEmpty()) {
			return state;
		}

		IPredicate joinedPost = null;
		int itfIndex = 0;
		for (final IPredicate interference : interferences) {
			if (isTrue(interference)) {
				if (mLogger != null) {
					mLogger.info("[ITF]   skipping itf[%d]: TRUE (no-op)", itfIndex);
				}
				itfIndex++;
				continue;
			}
			final IPredicate postState = mPostcondition.strongestPostcondition(state, interference);
			if (mLogger != null) {
				mLogger.info("[ITF]   applying itf[%d]: %s", itfIndex, interference.getFormula());
				mLogger.info("[ITF]   -> SP result: %s", postState.getFormula());
			}
			joinedPost = joinedPost == null ? postState : domain.join(joinedPost, postState);
			itfIndex++;
		}
		return joinedPost == null ? state : joinedPost;
	}

	@Override
	public boolean hasConverged(final IInterferenceAbstraction previous, final IDomain domain) {
		if (!(previous instanceof DefaultInterferenceAbstraction)) {
			throw new IllegalArgumentException("Cannot compare different abstraction types");
		}
		final DefaultInterferenceAbstraction prev = (DefaultInterferenceAbstraction) previous;

		for (final String threadId : mInterferencesByThread.keySet()) {
			final Set<IPredicate> newSet = getInterferencesProducedBy(threadId);
			final Set<IPredicate> oldSet = prev.getInterferencesProducedBy(threadId);

			for (final IPredicate newItf : newSet) {
				if (!isSubsumedByAny(newItf, oldSet, domain)) {
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
