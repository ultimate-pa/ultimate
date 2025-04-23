package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

public class FunctionContract {

	protected IPredicate precondition;
	protected IPredicate postcondition;

	public FunctionContract(final IPredicate precondition, final IPredicate postcondition) {
		this.precondition = precondition;
		this.postcondition = postcondition;
	}

	public IPredicate getPrecondition() {
		return precondition;
	}

	public IPredicate getPostcondition() {
		return postcondition;
	}

	@Override
	public String toString() {
		return "[" + precondition + " -> " + postcondition + "]";
	}

}
