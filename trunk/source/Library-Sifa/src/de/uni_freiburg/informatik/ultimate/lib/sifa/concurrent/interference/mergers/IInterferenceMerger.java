package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.mergers;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

/**
 * Reduces interference predicates per thread (e.g., by joining or limiting count).
 */
public interface IInterferenceMerger {

	Set<IPredicate> merge(Set<IPredicate> interferences, IDomain domain);

	static IInterferenceMerger identity() {
		return (interferences, domain) -> interferences;
	}
}
