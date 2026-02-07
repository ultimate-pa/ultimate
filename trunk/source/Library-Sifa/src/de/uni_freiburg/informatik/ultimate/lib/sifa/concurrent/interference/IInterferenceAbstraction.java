package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

public interface IInterferenceAbstraction {

	IPredicate applyToState(IPredicate state, String threadId, IDomain domain);

	boolean hasConverged(IInterferenceAbstraction previous, IDomain domain);

	/** Convergence check with optional logging of what changed. */
	default boolean hasConverged(final IInterferenceAbstraction previous, final IDomain domain, final ILogger logger) {
		return hasConverged(previous, domain);
	}

	boolean isEmpty();

	boolean canApply(IPredicate state, String threadId, IDomain domain);

	Set<IPredicate> getInterferencesForOtherThreads(String excludeThread);

	IInterferenceAbstraction widen(IInterferenceAbstraction other, IDomain domain);

	/** Thread IDs that produce interferences. */
	Set<String> getThreadIds();

	/** Number of interference predicates for a given thread. */
	default int getInterferenceCount(final String threadId) {
		return getInterferencesForOtherThreads(null).size();
	}
}
