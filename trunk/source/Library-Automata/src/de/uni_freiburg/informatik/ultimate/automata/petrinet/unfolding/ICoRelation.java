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

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TreeHashRelation;

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
 * @param <LETTER>
 *            symbol type
 * @param <PLACE>
 *            place content type
 */
public interface ICoRelation<LETTER, PLACE> {
	/**
	 * Updates the Co-relation regarding an event that just has been added to the branching process.
	 *
	 * @param event
	 *            the Event that has been added.
	 */
	void update(Event<LETTER, PLACE> event);

	/**
	 * @param cond1
	 *            One condition.
	 * @param cond2
	 *            Another condition.
	 * @return {@code true} iff 2 Conditions are in co-relation.
	 */
	boolean isInCoRelation(Condition<LETTER, PLACE> cond1, Condition<LETTER, PLACE> cond2);

	/**
	 * @param event
	 *            A condition.
	 * @param event
	 *            An event.
	 * @return The event and the condition are in co-relation.
	 */
	boolean isInCoRelation(final Condition<LETTER, PLACE> condition, final Event<LETTER, PLACE> event);

	/**
	 * @return The number of co-relation queries whose response was "yes".
	 */
	long getQueryCounterYes();

	/**
	 * @return The number of co-relation queries whose response was "no".
	 */
	long getQueryCounterNo();


	/**
	 * All initial Conditions in a branchin process are in co relation. Hence, all pairs of Conditions from
	 * <code>initialConditions</code> are added.
	 *
	 * @param initialConditions
	 *            set of initial conditions
	 */
	void initialize(Set<Condition<LETTER, PLACE>> initialConditions);

	/**
	 * @param coSet
	 *            A co-set.
	 * @param cond
	 *            condition
	 * @return {@code true} iff, given the co-set <code>coSet</code>, the unification with condition <code>c</code> is
	 *         still a co-set.
	 */
	boolean isCoset(Collection<Condition<LETTER, PLACE>> coSet, Condition<LETTER, PLACE> cond);


	/**
	 * Warning:
	 * <ul>
	 * <li>This is not a getter. The set is computed each time anew.
	 * <li>The result is NOT backed by the {@link BranchingProcess}. After an update
	 * of the {@link BranchingProcess} the set that you obtained might be outdated.
	 * </ul>
	 *
	 * @return Set of all {@link Condition}s that are in co-relation to the
	 *         {@link Condition} cond.
	 */
	Set<Condition<LETTER, PLACE>> computeCoRelatatedConditions(Condition<LETTER, PLACE> cond);

	/**
	 * Warning:
	 * <ul>
	 * <li>This is not a getter. The set is computed each time anew.
	 * <li>The result is NOT backed by the {@link BranchingProcess}. After an update
	 * of the {@link BranchingProcess} the set that you obtained might be outdated.
	 * </ul>
	 *
	 * @return Set of all {@link Condition}s that are in co-relation to the
	 *         {@link Condition} cond and whose {@link Condition#getPlace()}
	 *         is p.
	 */
	Set<Condition<LETTER, PLACE>> computeCoRelatatedConditions(Condition<LETTER, PLACE> cond, PLACE p);


	/**
	 * Compute <pre>max {numberOfCoRelated(c)|c ∈ C}</pre> where C is the set
	 * of all conditions and numberOfCoRelated is the function that assigns
	 * to a condition c the number of all conditions that are in co-relation
	 * to c.
	 */
	int computeMaximalDegree();

	Set<Event<LETTER, PLACE>> computeCoRelatatedEvents(Event<LETTER, PLACE> e);

	Set<Condition<LETTER, PLACE>> computeNonCutoffCoRelatatedConditions(Condition<LETTER, PLACE> cond);

	Set<Event<LETTER, PLACE>> computeCoRelatatedEvents(Condition<LETTER, PLACE> c);

	default TreeHashRelation<Integer, Condition<LETTER, PLACE>> computeHistogramOfDegree(
			final Iterable<Condition<LETTER, PLACE>> conditions) {
		final TreeHashRelation<Integer, Condition<LETTER, PLACE>> result = new TreeHashRelation<>();
		for (final Condition<LETTER, PLACE> c : conditions) {
			result.addPair(computeCoRelatatedConditions(c).size(), c);
		}
		return result;
	}
}
