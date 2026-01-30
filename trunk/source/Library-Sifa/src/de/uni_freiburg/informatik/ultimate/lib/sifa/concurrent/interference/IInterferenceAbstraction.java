package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

/**
 * Opaque abstraction of thread interferences. Handles applying interferences to states and checking convergence.
 */
public interface IInterferenceAbstraction {

	IPredicate applyToState(IPredicate state, String threadId, IDomain domain);

	boolean hasConverged(IInterferenceAbstraction previous, IDomain domain);

	boolean isEmpty();

	Set<IPredicate> getInterferencesForOtherThreads(String excludeThread);
}
