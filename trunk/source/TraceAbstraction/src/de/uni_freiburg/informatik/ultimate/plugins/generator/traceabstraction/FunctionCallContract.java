package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

public class FunctionCallContract {

	protected IPredicate precondition;
	protected IPredicate postcondition;

	public FunctionCallContract() {
		// TODO Auto-generated constructor stub
	}

	public static FunctionCallContract forSummary(final Summary summary, final FunctionContract functionContract) {
		return null;
	}

}
