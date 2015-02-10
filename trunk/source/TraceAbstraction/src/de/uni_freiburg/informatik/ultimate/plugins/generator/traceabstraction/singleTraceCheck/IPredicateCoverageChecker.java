package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker.Validity;

public interface IPredicateCoverageChecker {
	
	/**
	 * Returns validity of the implication 
	 * lhs.getFormula() ==> rhs.getFormula().
	 */
	public Validity isCovered(IPredicate lhs, IPredicate rhs);

}
