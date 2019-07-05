package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

public class ErrorOnEnterCall implements IEnterCallRegistrar {

	@Override
	public void registerEnterCall(final String callee, final IPredicate calleeInput) {
		throw new AssertionError(String.format("Did not expect any enter calls "
				+ "but received enter call %s with input %s.", callee, calleeInput));
	}

}
