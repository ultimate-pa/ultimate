package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.fixpoint;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

/**
 * Basic fixpoint: join for first N iterations, then widen to ensure termination.
 */
public class BasicFixpointStrategy implements IInterferenceFixpointStrategy {

	private static final int DEFAULT_WIDENING_THRESHOLD = 3;
	private final int mWideningThreshold;

	public BasicFixpointStrategy() {
		this(DEFAULT_WIDENING_THRESHOLD);
	}

	public BasicFixpointStrategy(final int wideningThreshold) {
		mWideningThreshold = wideningThreshold;
	}

	@Override
	public IPredicate computeFixpoint(final IPredicate state, final Set<IPredicate> interferences,
			final IDomain domain, final RelationalPredicatePostcondition postcondition) {
		if (interferences.isEmpty()) {
			return state;
		}

		IPredicate current = state;
		boolean changed = true;
		int iteration = 0;

		while (changed) {
			changed = false;
			iteration++;

			for (final IPredicate interference : interferences) {
				final IPredicate postState = postcondition.strongestPostcondition(current, interference);
				final IPredicate combined = iteration > mWideningThreshold
						? domain.widen(current, postState)
						: domain.join(current, postState);

				if (!domain.isSubsetEq(combined, current).isTrueForAbstraction()) {
					current = combined;
					changed = true;
				}
			}
		}

		return current;
	}
}
