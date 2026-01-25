package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.fixpoint;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

/**
 * Converged when each new interference is subsumed by some old interference.
 */
public class SubsumptionConvergenceCheck {

	public boolean hasConverged(final InterferenceAbstraction newInterferences, final InterferenceAbstraction oldInterferences,
			final IDomain domain) {
		for (final String threadId : newInterferences.getThreadIds()) {
			final Set<IPredicate> newSet = newInterferences.getInterferencesProducedBy(threadId);
			final Set<IPredicate> oldSet = oldInterferences.getInterferencesProducedBy(threadId);

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
}
