package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

public interface IEnterCallRegistrar {

	void registerEnterCall(final String callee, final IPredicate calleeInput);
}
