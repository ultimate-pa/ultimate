package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.biesenb;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateCoverageChecker;

public interface IImplicationGraph<T extends IPredicate> extends IPredicateCoverageChecker{

	/**
	 * Insert a predicate into the implication graph
	 *
	 * @param predicate
	 * @return the implication-vertex it is stored in
	 */
	public boolean unifyPredicate(final T predicate);
	
	/**
	 * removes all predicates form the collection, that are implied within the collection
	 */
	public Collection<T>  removeImpliedVerticesFromCollection(final Collection<T> collection);
	
	/**
	 * removes all predicates form the collection, that imply other predicates in the collection
	 */
	public Collection<T> removeImplyingVerticesFromCollection(final Collection<T> collection);
}
