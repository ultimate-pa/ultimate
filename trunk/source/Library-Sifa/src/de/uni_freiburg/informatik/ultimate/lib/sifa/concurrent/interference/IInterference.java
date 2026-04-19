package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;

public interface IInterference {

	IPredicate applyUntilFixpoint(IPredicate state, IDomain domain, int wideningThreshold, SifaStats stats);

	IInterference widen(IInterference other, IDomain domain);

	boolean isSubsumedBy(IInterference other, IDomain domain);
}
