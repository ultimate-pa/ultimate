package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/** Interference predicate with source/target locations, guard, and modified globals. */
public record PredicateWithSrcAndTrgt(IcfgLocation source, IcfgLocation target, IPredicate predicate,
		IPredicate preStateGuard, Set<TermVariable> modifiedGlobals) {
}
