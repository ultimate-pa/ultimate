/*
 * Copyright (C) 2011-2015 Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.Collection;
import java.util.Set;

/**
 * Represents the co-Relation in Occurrence nets.
 * <p>
 * It is updated when an event is added to a branching-process.
 * <p>
 * Two Nodes x,y are in <i>co-relation</i> if all of the following conditions are false:
 * <ul>
 * <li>x&lt;y</li>
 * <li>y&lt;x</li>
 * <li>y#x</li>
 * </ul>
 * whereas &lt; is the causal relation and # the conflict-relation.
 * <p>
 * Since the relation is only needed on Conditions, only related Methods exist.
 * 
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @param <S>
 *            symbol type
 * @param <C>
 *            place content type
 */
public interface ICoRelation<S, C> {
	/**
	 * Updates the Co-relation regarding an event that just has been added to the branching process.
	 * 
	 * @param event
	 *            the Event that has been added.
	 */
	void update(Event<S, C> event);

	/**
	 * @param cond1
	 *            One condition.
	 * @param cond2
	 *            Another condition.
	 * @return {@code true} iff 2 Conditions are in co-relation.
	 */
	boolean isInCoRelation(Condition<S, C> cond1, Condition<S, C> cond2);

	/**
	 * @return The number of co-relation queries that have been issued.
	 */
	int getCoRelationQueries();

	/**
	 * All initial Conditions in a branchin process are in co relation. Hence, all pairs of Conditions from
	 * <code>initialConditions</code> are added.
	 * 
	 * @param initialConditions
	 *            set of initial conditions
	 */
	void initialize(Set<Condition<S, C>> initialConditions);

	/**
	 * @param coSet
	 *            A co-set.
	 * @param cond
	 *            condition
	 * @return {@code true} iff, given the co-set <code>coSet</code>, the unification with condition <code>c</code> is
	 *         still a co-set.
	 */
	boolean isCoset(Collection<Condition<S, C>> coSet, Condition<S, C> cond);
}
