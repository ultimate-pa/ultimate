package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker.Validity;

public interface IPredicateCoverageChecker {
	
	/**
	 * Returns validity of the implication 
	 * lhs.getFormula() ==> rhs.getFormula().
	 */
	public Validity isCovered(IPredicate lhs, IPredicate rhs);

	/**
	 * Returns all known predicates that cover the predicate pred
	 * (i.e. all predicates that are implied by pred).
	 */
	public abstract Set<IPredicate> getCoveredPredicates(IPredicate pred);

	/**
	 * Returns all known predicates that are covered by the predicate pred
	 * (i.e. all predicates that are imply pred).
	 */
	public abstract Set<IPredicate> getCoveringPredicates(IPredicate pred);

}
