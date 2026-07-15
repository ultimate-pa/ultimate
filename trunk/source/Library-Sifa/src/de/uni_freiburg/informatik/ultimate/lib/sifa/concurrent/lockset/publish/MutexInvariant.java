package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.publish;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

record MutexInvariant(Set<IProgramVar> protectedGlobals, Set<IcfgEdge> publishEdges, IPredicate published) {

	MutexInvariant withChangedPublished(final IPredicate newPublished) {
		return new MutexInvariant(protectedGlobals, publishEdges, newPublished);
	}
}
