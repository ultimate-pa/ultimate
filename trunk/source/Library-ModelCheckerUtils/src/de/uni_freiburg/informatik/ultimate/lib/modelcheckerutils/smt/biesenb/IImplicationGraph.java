package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.biesenb;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateCoverageChecker;

public interface IImplicationGraph<T extends IPredicate> extends IPredicateCoverageChecker {

	/**
	 * Insert a predicate into the implication graph
	 *
	 * @param predicate
	 * @return the implication-vertex it is stored in
	 */
	boolean unifyPredicate(final T predicate);

	/**
	 * removes all predicates form the collection, that are implied within the collection
	 */
	Collection<T> removeImpliedVerticesFromCollection(final Collection<T> collection);

	/**
	 * removes all predicates form the collection, that imply other predicates in the collection
	 */
	Collection<T> removeImplyingVerticesFromCollection(final Collection<T> collection);
}
