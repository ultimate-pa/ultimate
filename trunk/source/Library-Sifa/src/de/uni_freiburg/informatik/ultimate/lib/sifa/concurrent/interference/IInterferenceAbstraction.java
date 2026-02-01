package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

public interface IInterferenceAbstraction {

	IPredicate applyToState(IPredicate state, String threadId, IDomain domain);

	default IPredicate applyToState(final IPredicate state, final String threadId, final IDomain domain,
			final IcfgLocation location) {
		return applyToState(state, threadId, domain);
	}

	boolean hasConverged(IInterferenceAbstraction previous, IDomain domain);

	boolean isEmpty();

	Set<IPredicate> getInterferencesForOtherThreads(String excludeThread);
}
