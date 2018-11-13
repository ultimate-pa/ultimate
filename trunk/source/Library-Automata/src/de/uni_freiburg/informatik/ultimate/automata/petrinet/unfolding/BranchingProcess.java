/*
 * Copyright (C) 2011-2015 Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
import java.util.Comparator;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.BranchingProcessToUltimateModel;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            symbol type
 * @param <PLACE>
 *            place content type
 */
public final class BranchingProcess<LETTER, PLACE> implements IAutomaton<LETTER, PLACE> {
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;

	private final Collection<Condition<LETTER, PLACE>> mConditions;
	private final Collection<Event<LETTER, PLACE>> mEvents;

	private final ICoRelation<LETTER, PLACE> mCoRelation;

	private final HashRelation<PLACE, Condition<LETTER, PLACE>> mPlace2Conds;

	/**
	 * Dummy root event with all initial conditions as successors.
	 * Unlike all other events in this branching process, the root does not correspond to any transition of {@link #mNet}.
	 */
	private final Event<LETTER, PLACE> mDummyRoot;

	/**
	 * Net associated with this branching process.
	 * Places of this branching process correspond to places of the net.
	 * Events of this branching process correspond to transitions of the net.
	 */
	private final IPetriNetSuccessorProvider<LETTER, PLACE> mNet;

	private final IOrder<LETTER, PLACE> mOrder;
	
	private int mConditionSerialnumberCounter = 0;

	public BranchingProcess(final AutomataLibraryServices services, final IPetriNetSuccessorProvider<LETTER, PLACE> net,
			final IOrder<LETTER, PLACE> order) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mNet = net;
		mOrder = order;
		mPlace2Conds = new HashRelation<>();
		mConditions = new HashSet<>();
		mEvents = new HashSet<>();
		mCoRelation = new ConditionEventsCoRelation<>(this);

		// add a dummy event as root. its successors are the initial conditions.
		mDummyRoot = new Event<>(this);
		addEvent(mDummyRoot);
	}

	/**
	 * @return dummy root event with all initial conditions as successors.
	 *        Is not associated with any transition from the net.
	 */
	public Event<LETTER, PLACE> getDummyRoot() {
		return mDummyRoot;
	}

	public Condition<LETTER, PLACE> constructCondition(final Event<LETTER, PLACE> predecessor, final PLACE place) {
		return new Condition<LETTER, PLACE>(predecessor, place, mConditionSerialnumberCounter++);
	}

	/**
	 * Adds an Event to the Branching Process with all outgoing Conditions.
	 * <p>
	 * updates the Co-Relation.
	 * </p>
	 *
	 * @param event
	 *            event
	 * @return true iff some successor of e corresponds to an accepting place
	 */
	boolean addEvent(final Event<LETTER, PLACE> event) {
		mEvents.add(event);
		for (final Condition<LETTER, PLACE> c : event.getPredecessorConditions()) {
			assert !c.getPredecessorEvent().isCutoffEvent() : "Cut-off events must not have successors.";
			c.addSuccesssor(event);
		}
		boolean someSuccessorIsAccepting = false;
		for (final Condition<LETTER, PLACE> c : event.getSuccessorConditions()) {
			mConditions.add(c);
			mPlace2Conds.addPair(c.getPlace(), c);
			if (mNet.isAccepting(c.getPlace())) {
				someSuccessorIsAccepting = true;
			}
		}
		mCoRelation.update(event);
		assert checkOneSafety(event) : "Net is not one safe!";
		return someSuccessorIsAccepting;
	}

	private boolean checkOneSafety(final Event<LETTER, PLACE> event) {
		for (final Condition<LETTER, PLACE> condition : event.getSuccessorConditions()) {
			final Set<Condition<LETTER, PLACE>> existing = mPlace2Conds.getImage(condition.getPlace());
			for (final Condition<LETTER, PLACE> c : existing) {
				if (c != condition && mCoRelation.isInCoRelation(c, condition)) {
					mLogger.debug(c + " in coRelation with " + condition + " but they belong to the same place.");
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * Checks if a new event {@code event}, with regards to {@code order} is a cut-off event. In that case, companions
	 * are computed as a side-effect.
	 *
	 * @param event
	 *            event
	 * @param order
	 *            order
	 * @param sameTransitionCutOff
	 *            {@code true} iff events belong to the same transition
	 * @return true iff event is cut-off
	 * @see Event#checkCutOffSetCompanion(Event, Comparator, boolean)
	 */
	public boolean isCutoffEvent(final Event<LETTER, PLACE> event, final Comparator<Event<LETTER, PLACE>> order,
			final boolean sameTransitionCutOff) {
		// TODO possibly optimize
		for (final Event<LETTER, PLACE> ev : getEvents()) {
			if (event.checkCutOffSetCompanion(ev, order, sameTransitionCutOff)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * @param place
	 *            place
	 * @return all conditions c s.t. p is the corresponding place of c.
	 */
	public Set<Condition<LETTER, PLACE>> place2cond(final PLACE place) {
		return mPlace2Conds.getImage(place);
	}

	public ICoRelation<LETTER, PLACE> getCoRelation() {
		return mCoRelation;
	}

	public Collection<Condition<LETTER, PLACE>> getConditions() {
		return mConditions;
	}

	public Collection<Event<LETTER, PLACE>> getEvents() {
		return mEvents;
	}

	/**
	 * @return The initial conditions.
	 */
	public Collection<Condition<LETTER, PLACE>> initialConditions() {
		return mDummyRoot.getSuccessorConditions();
	}

	/**
	 * Returns all minimal events of this branching process with respect to the causal order.
	 * An event is causally minimal iff all its predecessors are initial conditions.
	 * Events with a non-initial preceding condition c cannot be minimal.
	 * Because c is non-initial it has to be preceded by another event which is causally smaller.
	 *
	 * @return The causally minimal events
	 */
	public Collection<Event<LETTER, PLACE>> minEvents() {
		final Set<Event<LETTER, PLACE>> eventsConnectedToInitConditions = new HashSet<>();
		for (final Condition<LETTER, PLACE> initCondition : initialConditions()) {
			eventsConnectedToInitConditions.addAll(initCondition.getSuccessorEvents());
		}
		final Set<Event<LETTER, PLACE>> minEvents = new HashSet<>();
		for (final Event<LETTER, PLACE> succEvent : eventsConnectedToInitConditions) {
			if (initialConditions().containsAll(succEvent.getPredecessorConditions())) {
				minEvents.add(succEvent);
			}
		}
		return minEvents;
	}

	/**
	 * Returns the net associated with this branching process.
	 * @return Net associated with this branching process
	 */
	public IPetriNetSuccessorProvider<LETTER, PLACE> getNet() {
		return mNet;
	}

	/**
	 * Check if the Conditions c1 and c2 are in causal relation. Conditions c1 and c2 are in causal relation if
	 * <ul>
	 * <li>c1 != c2 and c1 is ancestor of c2</li>
	 * <li>or c1 != c2 and c2 is ancestor of c1</li>
	 * </ul>
	 *
	 * @param c1
	 *            first condition
	 * @param c2
	 *            second condition
	 * @return {@code true} iff the conditions are in causal relation
	 */
	public boolean inCausalRelation(final Condition<LETTER, PLACE> c1, final Condition<LETTER, PLACE> c2) {
		if (c1 == c2) {
			return false;
		}
		final Set<Object> c1Ancestors = ancestorNodes(c1);
		if (c1Ancestors.contains(c2)) {
			return true;
		}
		final Set<Object> c2Ancestors = ancestorNodes(c2);
		return c2Ancestors.contains(c1);
	}

	/**
	 * Check if Condition and Event are in causal relation. This is the case if
	 * <ul>
	 * <li>the condition is an ancestor of the event</li>
	 * <li>or the event is ancestor of the condition.</li>
	 * </ul>
	 *
	 * @param condition
	 *            condition
	 * @param event
	 *            event
	 * @return {@code true} iff condition and event are in causal relation
	 */
	public boolean inCausalRelation(final Condition<LETTER, PLACE> condition, final Event<LETTER, PLACE> event) {
		final Set<Object> cAncestors = ancestorNodes(condition);
		if (cAncestors.contains(event)) {
			return true;
		}
		final Set<Object> eAncestors = ancestorNodes(event);
		return eAncestors.contains(condition);
	}

	/**
	 * Check if the Conditions c1 and c2 are in conflict. In a branching process Conditions c1 and c2 are in conflict
	 * iff c1 != c2 and there exist two paths leading to c1 and c2 which start at the same condition and diverge
	 * immediately and never converge again.
	 *
	 * @param c1
	 *            first condition
	 * @param c2
	 *            second condition
	 * @return {@code true} iff the conditions are in conflict
	 */
	public boolean inConflict(final Condition<LETTER, PLACE> c1, final Condition<LETTER, PLACE> c2) {
		if (c1 == c2) {
			return false;
		}
		final Set<Object> c2Ancestors = ancestorNodes(c2);
		return conflictPathCheck(c1, c2, c2Ancestors);
	}

	/**
	 * @return if c1 != c2 and c2 is no ancestor of c1 the result is true iff there is a path from a condition in
	 *         c2Ancestors to c1 that does not contain other elements of c2Ancestors.
	 */
	private boolean conflictPathCheck(final Condition<LETTER, PLACE> c1, final Condition<LETTER, PLACE> c2,
			final Set<Object> c2Ancestors) {
		if (c1 == c2) {
			throw new IllegalArgumentException(c1 + " ancestor of " + c2);
		}
		if (c2Ancestors.contains(c1)) {
			return true;
		}
		final Event<LETTER, PLACE> pred = c1.getPredecessorEvent();
		if (c2Ancestors.contains(pred)) {
			return false;
		}
		if (pred == mDummyRoot) {
			return false;
		}
		boolean result = false;
		for (final Condition<LETTER, PLACE> cPred : pred.getPredecessorConditions()) {
			result = result || conflictPathCheck(cPred, c2, c2Ancestors);
		}
		return result;
	}

	/**
	 * @return Set containing all Conditions and Events which are (strict) ancestors of a Condition. The dummyRoot is
	 *         not considered as an ancestor.
	 */
	private Set<Object> ancestorNodes(final Condition<LETTER, PLACE> condition) {
		final Set<Object> ancestorConditionAndEvents = new HashSet<>();
		addAllAncestors(condition, ancestorConditionAndEvents);
		return ancestorConditionAndEvents;
	}

	/**
	 * @return Set containing all Conditions and Events which are ancestors of an Event. The dummyRoot is not considered
	 *         as an ancestor.
	 */
	private Set<Object> ancestorNodes(final Event<LETTER, PLACE> event) {
		final Set<Object> ancestorConditionAndEvents = new HashSet<>();
		addAllAncestors(event, ancestorConditionAndEvents);
		return ancestorConditionAndEvents;
	}

	/**
	 * Add to a set that contains only Conditions and Events the Condition and all (strict) ancestors. The dummyRoot is
	 * not considered as an ancestor.
	 */
	private void addAllAncestors(final Condition<LETTER, PLACE> condition, final Set<Object> setOfConditionsAndEvents) {
		final Event<LETTER, PLACE> pred = condition.getPredecessorEvent();
		setOfConditionsAndEvents.add(pred);
		addAllAncestors(pred, setOfConditionsAndEvents);
	}

	/**
	 * Add to a set that contains only Conditions and Events the Event and all (strict) ancestors. The dummyRoot is not
	 * considered as an ancestor.
	 */
	private void addAllAncestors(final Event<LETTER, PLACE> event, final Set<Object> setOfConditionsAndEvents) {
		if (event == mDummyRoot) {
			return;
		}
		for (final Condition<LETTER, PLACE> pred : event.getPredecessorConditions()) {
			setOfConditionsAndEvents.add(pred);
			addAllAncestors(pred, setOfConditionsAndEvents);
		}
	}

	/**
	 * @param conditions
	 *            The conditions.
	 * @return {@code true} iff all elements are pairwise in conflict or in co-relation
	 */
	public boolean pairwiseConflictOrCausalRelation(final Collection<Condition<LETTER, PLACE>> conditions) {
		if (conditions.isEmpty()) {
			throw new IllegalArgumentException("method only defined for non-empty set of conditions");
		}
		boolean result = true;
		for (final Condition<LETTER, PLACE> c1 : conditions) {
			for (final Condition<LETTER, PLACE> c2 : conditions) {
				if (!inCausalRelation(c1, c2) && !inConflict(c1, c2)) {
					result = false;
				}
			}
		}
		return result;
	}

	@Override
	public String sizeInformation() {
		return "has " + mConditions.size() + "conditions, " + mEvents.size() + " events.";
	}

	public IOrder<LETTER, PLACE> getOrder() {
		return mOrder;
	}

	@Override
	public int size() {
		return mConditions.size();
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mNet.getAlphabet();
	}

	@Override
	public IElement transformToUltimateModel(final AutomataLibraryServices services)
			throws AutomataOperationCanceledException {
		return new BranchingProcessToUltimateModel<LETTER, PLACE>().transformToUltimateModel(this);
	}
}
