package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import java.util.Collection;
import java.util.Set;

/**
 * Represents the co-Relation in Ocurrence nets.
 * 
 * it is updated when an event is added to a branching-process.
 * 
 * Two Nodes x,y are in <i>co-relation</i> if all of the following conditions
 * are false:
 * <ul>
 * <li>x&lt;y</li>
 * <li>y&lt;x</li>
 * <li>y#x</li>
 * </ul>
 * whereas &lt; is the causal relation and # the conflict-relation.
 * 
 * Since the relation is only needed on Conditions, only related Methods exist.
 * 
 * @author iari
 * 
 */
public interface ICoRelation<S, C> {
	/**
	 * Updates the Co-relation regarding an event that just has been added to
	 * the branching process.
	 * 
	 * @param e
	 *            the Event that has been added.
	 */
	void update(Event<S, C> e);

	/**
	 * checks, if 2 Conditions are in co-relation.
	 * 
	 * @param c1
	 * @param c2
	 * @return
	 */
	boolean isInCoRelation(Condition<S, C> c1, Condition<S, C> c2);
	
	/**
	 * gets the number of co-relation queries that have been issued.
	 * @return
	 */
	int getCoRelationQueries();

	/**
	 * All initial Conditions in a branchin process are in co relation. Hence,
	 * all pairs of Conditions from <code>initialConditions</code> are added.
	 * 
	 * @param initialMarking
	 */
	void initialize(Set<Condition<S, C>> initialConditions);

	/**
	 * given the co-set <code>coSet</code>, checks whether the unification with
	 * condition <code>c</code> is still a co-set.
	 * 
	 * @param coSet
	 * @param c
	 * @return
	 */
	boolean isCoset(Collection<Condition<S, C>> coSet, Condition<S, C> c);
}
