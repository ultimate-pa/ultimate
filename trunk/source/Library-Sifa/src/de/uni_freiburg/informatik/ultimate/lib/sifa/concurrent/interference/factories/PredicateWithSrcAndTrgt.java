package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.factories;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.GuardedPredicate;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public record PredicateWithSrcAndTrgt(IcfgLocation source, IcfgLocation target, IPredicate predicate,
		IPredicate preStateGuard, Set<TermVariable> modifiedGlobals, GuardedPredicate precomputedGuardedPredicate) {

	public PredicateWithSrcAndTrgt(final IcfgLocation source, final IcfgLocation target, final IPredicate predicate,
			final IPredicate preStateGuard, final Set<TermVariable> modifiedGlobals) {
		this(source, target, predicate, preStateGuard, modifiedGlobals, null);
	}
}
