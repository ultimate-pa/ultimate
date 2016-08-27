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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public class BranchingProcess<S, C> implements IAutomaton<S, C> {
	
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	
	private final Collection<Condition<S, C>> mConditions;
	private final Collection<Event<S, C>> mEvents;

	private final ICoRelation<S, C> mCoRelation;

	private final Map<Place<S, C>, Set<Condition<S, C>>> mPlace2cond;

	private final Event<S, C> mDummyRoot;

	private final PetriNetJulian<S, C> mNet;
	
	private final Order<S,C> mOrder;

	public BranchingProcess(final AutomataLibraryServices services,
			final PetriNetJulian<S, C> net, final Order<S, C> order) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		this.mNet = net;
		this.mOrder = order;
		this.mPlace2cond = new HashMap<Place<S, C>, Set<Condition<S, C>>>();
		for (final Place<S, C> p : net.getPlaces()) {
			mPlace2cond.put(p, new HashSet<Condition<S, C>>());
		}
		this.mConditions = new HashSet<Condition<S, C>>();
		this.mEvents = new HashSet<Event<S, C>>();
		this.mCoRelation = new ConditionEventsCoRelation<S, C>(this);

		// add a dummy event as root. its successors are the initial conditions.
		this.mDummyRoot = new Event<S, C>(net);
		addEvent(mDummyRoot);
	}

	/**
	 * @return Gets the "root" event, which is a dummy (has no transition
	 *     associated) with all initial conditions as successors.
	 */
	public Event<S, C> getDummyRoot() {
		return mDummyRoot;
	}

	/**
	 * adds an Event to the Branching Process with all outgoing Conditions.
	 * <p>
	 * updates the Co-Relation.
	 * </p>
	 * 
	 * @param e event
	 * @return true iff some successor of e corresponds to an accepting place
	 */
	boolean addEvent(final Event<S, C> e) {
		mEvents.add(e);
		for (final Condition<S, C> c : e.getPredecessorConditions()) {
			c.addSuccesssor(e);
		}
		boolean someSuccessorIsAccepting = false;
		for (final Condition<S, C> c : e.getSuccessorConditions()) {
			mConditions.add(c);
			mPlace2cond.get(c.getPlace()).add(c);
			if (isAccepting(c)) {
				someSuccessorIsAccepting = true;
			}
		}
		mCoRelation.update(e);
		assert checkOneSafety(e) : "Net is not one safe!";
		return someSuccessorIsAccepting;
	}

	private boolean checkOneSafety(final Event<S, C> e) {
		for (final Condition<S, C> condition : e.getSuccessorConditions()) {
			final Set<Condition<S, C>> existing = mPlace2cond
					.get(condition.getPlace());
			for (final Condition<S, C> c : existing) {
				if (c != condition && isInCoRelation(c, condition)) {
					mLogger.debug(c + " in coRelation with " + condition
							+ " but they belong to the same place.");
					return false;
				}
			}
		}
		return true;
	}

	boolean isAccepting(final Condition<S, C> c) {
		return mNet.getAcceptingPlaces().contains(c.getPlace());
	}

	/**
	 * checks if a new event {@code e}, with regards to {@code order} is a
	 * cut-off event. In that case, companions are computed as a side-effect.
	 * 
	 * @see Event#checkCutOffSetCompanion(Event, Comparator, boolean)
	 * @return true iff event is cut-off
	 */
	public boolean isCutoffEvent(final Event<S, C> e, final Comparator<Event<S, C>> order,
			final boolean sameTransitionCutOff) {
		// TODO possibly optimize
		for (final Event<S, C> ev : getEvents()) {
			if (e.checkCutOffSetCompanion(ev, order, sameTransitionCutOff)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * return all conditions c s.t. p is the corresponding place of c.
	 */
	public Set<Condition<S, C>> place2cond(final Place<S, C> p) {
		return mPlace2cond.get(p);
	}

	public boolean isInCoRelation(final Condition<S, C> c1, final Condition<S, C> c2) {
		return mCoRelation.isInCoRelation(c1, c2);
	}

	public int getCoRelationQueries() {
		return mCoRelation.getCoRelationQueries();
	}

	@SuppressWarnings("unused")
	private boolean isInCoRelationChecker(final Condition<S, C> c1, final Condition<S, C> c2) {
		/**
		 * Christian 2016-08-16: Probably a bug: isAncestorChecker(c1, c2)
		 *                       is repeated twice.
		 */
		return !(isAncestorChecker(c1, c2)
				|| isAncestorChecker(c1, c2)
				|| inConflict(c1, c2));
	}

	private boolean isAncestorChecker(final Condition<S, C> leaf,
			final Condition<S, C> ancestor) {
		if (leaf == ancestor) {
			return true;
		}
		final Event<S, C> p = leaf.getPredecessorEvent();
		if (p == null || p.getPredecessorConditions() == null) {
			return false;
		}
		for (final Condition<S, C> parentOfLeaf : p.getPredecessorConditions()) {
			if (isAncestorChecker(parentOfLeaf, ancestor)) {
				return true;
			}
		}
		return false;
	}

	// private boolean inConflict(Condition<S, C> c1, Condition<S, C> c2) {
	// Set<Condition<S, C>> pred =
	// c1.getPredecessorEvent().getPredecessorConditions();
	// if (pred== null) return false;
	// for (Condition<S, C> condition : pred) {
	// // TODO finish checker Method
	// }
	// return false;
	// }

	boolean isCoset(final Collection<Condition<S, C>> coSet, final Condition<S, C> c) {
		return mCoRelation.isCoset(coSet, c);
	}

	public Collection<Condition<S, C>> getConditions() {
		return mConditions;
	}

	public Collection<Event<S, C>> getEvents() {
		return mEvents;
	}

	public Collection<Condition<S, C>> initialConditions() {
		return mDummyRoot.getSuccessorConditions();
	}

	/**
	 * returns all minimal events of the branching process with respect to the
	 * causal order.
	 * 
	 * @return all minimal events
	 */
	public Collection<Event<S, C>> getMinEvents() {
		final HashSet<Event<S, C>> h = new HashSet<Event<S, C>>();
		final HashSet<Event<S, C>> min = new HashSet<Event<S, C>>();
		for (final Condition<S, C> c : initialConditions()) {
			h.addAll(c.getSuccessorEvents());
		}
		for (final Event<S, C> e : h) {
			if (initialConditions().containsAll(e.getPredecessorConditions())) {
				min.add(e);
			}
		}
		return min;
	}

	/**
	 * gets the net associated with the branching process.
	 * 
	 * @return the net associated with the branching process
	 */
	public PetriNetJulian<S, C> getNet() {
		return mNet;
	}

	/**
	 * Check if the Conditions c1 and c2 are in causal relation. Conditions c1
	 * and c2 are in causal relation if
	 * <ul>
	 * <li>c1 != c2 and c1 is ancestor of c2</li>
	 * <li>or c1 != c2 and c2 is ancestor of c1</li>
	 * </ul>
	 */
	public boolean inCausalRelation(final Condition<S, C> c1, final Condition<S, C> c2) {
		if (c1 == c2) {
			return false;
		}
		final Set<Object> c1Ancestors = ancestorNodes(c1);
		if (c1Ancestors.contains(c2)) {
			return true;
		}
		final Set<Object> c2Ancestors = ancestorNodes(c2);
		if (c2Ancestors.contains(c1)) {
			return true;
		}
		return false;
	}

	/**
	 * Check if Condition c and Event e are in causal relation. Conditions c and
	 * Event e are in causal relation if
	 * <ul>
	 * <li>c is ancestor of e</li>
	 * <li>or e is ancestor of c</li>
	 * </ul>
	 */
	public boolean inCausalRelation(final Condition<S, C> c, final Event<S, C> e) {
		final Set<Object> cAncestors = ancestorNodes(c);
		if (cAncestors.contains(e)) {
			return true;
		}
		final Set<Object> eAncestors = ancestorNodes(e);
		if (eAncestors.contains(c)) {
			return true;
		}
		return false;
	}

	/**
	 * Check if the Conditions c1 and c2 are in conflict. In a branching process
	 * Conditions c1 and c2 are in conflict iff c1 != c2 and there exist two
	 * paths leading to c1 and c2 which start at the same condition and diverge
	 * immediately and never converge again.
	 */
	public boolean inConflict(final Condition<S, C> c1, final Condition<S, C> c2) {
		if (c1 == c2) {
			return false;
		}
		final Set<Object> c2Ancestors = ancestorNodes(c2);
		return conflictPathCheck(c1, c2, c2Ancestors);
	}

	/**
	 * @return if c1 != c2 and c2 is no ancestor of c1 the result is true iff
	 *         there is a path from a condition in c2Ancestors to c1 that does
	 *         not contain other elements of c2Ancestors.
	 */
	private boolean conflictPathCheck(final Condition<S, C> c1, final Condition<S, C> c2,
			final Set<Object> c2Ancestors) {
		if (c1 == c2) {
			throw new IllegalArgumentException(c1 + " ancestor of " + c2);
		}
		if (c2Ancestors.contains(c1)) {
			return true;
		}
		final Event<S, C> pred = c1.getPredecessorEvent();
		if (c2Ancestors.contains(pred)) {
			return false;
		}
		if (pred == mDummyRoot) {
			return false;
		}
		boolean result = false;
		for (final Condition<S, C> cPred : pred.getPredecessorConditions()) {
			result = result || conflictPathCheck(cPred, c2, c2Ancestors);
		}
		return result;
	}

	/**
	 * @return Set containing all Conditions and Events which are (strict)
	 *         ancestors of Condition c. The dummyRoot is not considered as an
	 *         ancestor.
	 */
	private Set<Object> ancestorNodes(final Condition<S, C> c) {
		final Set<Object> ancestorConditionAndEvents = new HashSet<Object>();
		addAllAncestors(c, ancestorConditionAndEvents);
		return ancestorConditionAndEvents;
	}

	/**
	 * @return Set containing all Conditions and Events which are ancestors of
	 *         Event e. The dummyRoot is not considered as an ancestor.
	 */
	private Set<Object> ancestorNodes(final Event<S, C> e) {
		final Set<Object> ancestorConditionAndEvents = new HashSet<Object>();
		addAllAncestors(e, ancestorConditionAndEvents);
		return ancestorConditionAndEvents;
	}

	/**
	 * Add to a set that contains only Conditions and Events the Condition c and
	 * all (strict) ancestors of c. The dummyRoot is not considered as an
	 * ancestor.
	 */
	private void addAllAncestors(final Condition<S, C> c,
			final Set<Object> setOfConditionsAndEvents) {
		final Event<S, C> pred = c.getPredecessorEvent();
		setOfConditionsAndEvents.add(pred);
		addAllAncestors(pred, setOfConditionsAndEvents);
	}

	/**
	 * Add to a set that contains only Conditions and Events the Event e and all
	 * (strict) ancestors of e. The dummyRoot is not considered as an ancestor.
	 */
	private void addAllAncestors(final Event<S, C> e,
			final Set<Object> setOfConditionsAndEvents) {
		if (e == mDummyRoot) {
			return;
		} else {
			for (final Condition<S, C> pred : e.getPredecessorConditions()) {
				setOfConditionsAndEvents.add(pred);
				addAllAncestors(pred, setOfConditionsAndEvents);
			}
		}
	}

	/**
	 * Given a set <i>conditions</i> returns true iff all elements are pairwise
	 * in conflict or in co-relation;
	 */
	public boolean pairwiseConflictOrCausalRelation(
			final Collection<Condition<S, C>> conditions) {
		if (conditions.isEmpty()) {
			throw new IllegalArgumentException(
					"method only defined for non-empty set of conditions");
		}
		boolean result = true;
		for (final Condition<S, C> c1 : conditions) {
			for (final Condition<S, C> c2 : conditions) {
				if (!inCausalRelation(c1, c2) && !inConflict(c1, c2)) {
					result = false;
				}
			}
		}
		return result;
	}

	@Override
	public String sizeInformation() {
		return "has " + mConditions.size() + "conditions, " + mEvents.size()
				+ " events";
	}

	public Order<S,C> getOrder() {
		return mOrder;
	}

	@Override
	public int size() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Set<S> getAlphabet() {
		return mNet.getAlphabet();
	}

	@Override
	public IStateFactory<C> getStateFactory() {
		throw new UnsupportedOperationException();
	}

}
