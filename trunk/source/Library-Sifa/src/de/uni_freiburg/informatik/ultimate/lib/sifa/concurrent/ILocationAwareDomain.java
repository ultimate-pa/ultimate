package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

public interface ILocationAwareDomain extends IDomain {

	IPredicate alpha(IPredicate pred, IcfgLocation location);
}
