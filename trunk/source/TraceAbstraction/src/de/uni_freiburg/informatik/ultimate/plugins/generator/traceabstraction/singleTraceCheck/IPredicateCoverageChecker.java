package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;

public interface IPredicateCoverageChecker {
	
	/**
	 * Returns UNSAT if we can prove that lhs is covered by rhs (i.e., 
	 * lhs.getFormula() implies rhs.getFormula()),
	 * returns SAT if we can prove that lhs is not covered by rhs,
	 * return UNKNOWN if can neither prove nor refute one of the above cases.
	 */
	public LBool isCovered(IPredicate lhs, IPredicate rhs);

}
