package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

public interface IInterferenceAbstraction {

	IPredicate applyToState(IPredicate state, String threadId, IDomain domain);

	boolean hasConverged(IInterferenceAbstraction previous, IDomain domain);

	boolean isEmpty();

	boolean canApply(IPredicate state, String threadId, IDomain domain);

	Set<IPredicate> getInterferencesForOtherThreads(String excludeThread);

	IInterferenceAbstraction widen(IInterferenceAbstraction other, IDomain domain);
}
