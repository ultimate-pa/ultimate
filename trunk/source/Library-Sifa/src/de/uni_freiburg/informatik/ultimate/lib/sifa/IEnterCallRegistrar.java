package de.uni_freiburg.informatik.ultimate.lib.sifa;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

public interface IEnterCallRegistrar {

	void registerEnterCall(final String callee, final IPredicate calleeInput);
}
