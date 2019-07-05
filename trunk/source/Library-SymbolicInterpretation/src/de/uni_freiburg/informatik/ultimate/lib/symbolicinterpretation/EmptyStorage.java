package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

public class EmptyStorage implements ILoiPredicateStorage {

	@Override
	public void storePredicateIfLoi(final IcfgLocation location, final IPredicate addPred) {
		// nothing to do
	}

}
