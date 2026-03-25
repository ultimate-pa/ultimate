package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;

public interface IInterference {
	Collection<IPredicate> getPredicates();

	boolean isTrivial();

	boolean isSubsumedBy(IInterference other, IDomain domain);

	IInterference widen(IInterference other, IDomain domain);

	int size();

	/** Apply this interference relation until a local fixpoint, using the configured applicator. */
	IPredicate applyUntilFixpoint(IPredicate state, IDomain domain, int wideningThreshold, SifaStats stats);
}
