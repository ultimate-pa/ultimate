/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import java.io.Serializable;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;

public class Event<S, C> implements Serializable {
	private static final long serialVersionUID = 7162664880110047121L;

	private final int m_HashCode;

	private final Set<Condition<S, C>> m_Predecessors;
	private final Set<Condition<S, C>> m_Successors;
	private final Configuration<S, C> m_LocalConfiguration;
	// private final Event<S, C>[] m_LocalConfiguration;
	// private final ArrayList<Event<S, C>> m_LocalConfiguration;
	private final Marking<S, C> m_Mark;
	private final ConditionMarking<S, C> m_ConditionMark;

	private Event<S, C> m_Companion;
	private final Transition<S, C> m_Transition;

	/**
	 * Creates an Event from its predecessor conditions and the transition from
	 * the net system it is mapped to by the homomorphism. Its successor
	 * conditions are automatically created. The given set not be referenced
	 * directly, but copied.
	 * 
	 * @param predecessors
	 * @param transition
	 */
	public Event(Collection<Condition<S, C>> predecessors,
			Transition<S, C> transition) {
		assert conditionToPlaceEqual(predecessors, transition.getPredecessors()) : "An event was created with inappropriate predecessors.\n  "
				+ "transition: "
				+ transition.toString()
				+ "\n  events predecessors: "
				+ predecessors.toString()
				+ "\n  "
				+ "transitions predecessors:"
				+ transition.getPredecessors();
		this.m_Predecessors = new HashSet<Condition<S, C>>(predecessors);
		// HashSet<Event<S, C>> localConfiguration = new HashSet<Event<S, C>>();
		this.m_LocalConfiguration = new Configuration<S, C>(
				new HashSet<Event<S, C>>());
		this.m_Transition = transition;
		Set<Condition<S, C>> conditionMarkSet = new HashSet<Condition<S, C>>();

		Set<Event<S, C>> predecessorEvents = new HashSet<Event<S, C>>();
		for (Condition<S, C> c : predecessors) {
			Event<S, C> e = c.getPredecessorEvent();
			if (predecessorEvents.contains(e))
				continue;
			predecessorEvents.add(e);
			// Collections.addAll(localConfiguration, e.m_LocalConfiguration);
			m_LocalConfiguration.addAll(e.m_LocalConfiguration);
			e.m_ConditionMark.addTo(conditionMarkSet);
		}

		m_LocalConfiguration.add(this);

		this.m_Successors = new HashSet<Condition<S, C>>();
		for (Place<S, C> p : transition.getSuccessors()) {
			this.m_Successors.add(new Condition<S, C>(this, p));
		}
		for (Event<S, C> a : m_LocalConfiguration) {
			conditionMarkSet.removeAll(a.getPredecessorConditions());
		}
		conditionMarkSet.addAll(m_Successors);
		this.m_ConditionMark = new ConditionMarking<S, C>(conditionMarkSet);
		this.m_Mark = m_ConditionMark.getMarking();
		m_HashCode = computeHashCode();
	}

	/**
	 * returns the Set of all successor conditions of {@code events}
	 * 
	 * @param events
	 * @return
	 */
	public static <S, C> Set<Condition<S, C>> getDot(Set<Event<S, C>> events) {
		HashSet<Condition<S, C>> result = new HashSet<Condition<S, C>>();
		for (Event<S, C> e : events) {
			result.addAll(e.getSuccessorConditions());
		}
		return result;
	}

	/**
	 * returns the Set of all successor events of all successor conditions of
	 * the event
	 */
	public Set<Event<S, C>> getSuccessorEvents() {
		HashSet<Event<S, C>> result = new HashSet<Event<S, C>>();
		for (Condition<S, C> c : this.getSuccessorConditions()) {
			result.addAll(c.getSuccessorEvents());
		}
		return result;
	}

	/**
	 * returns the Set of all successor events of all successor conditions of
	 * {@code events}
	 * 
	 * @param events
	 * @return
	 */
	public static <S, C> Set<Event<S, C>> getSuccessorEvents(
			Set<Event<S, C>> events) {
		HashSet<Event<S, C>> result = new HashSet<Event<S, C>>();
		for (Event<S, C> e : events) {
			result.addAll(e.getSuccessorEvents());
		}
		return result;
	}

	/**
	 * returns the Set of all predecessor events of all predecessor conditions
	 * of {@code events}
	 * 
	 * @param events
	 * @return
	 */
	public static <S, C> Set<Event<S, C>> getPredecessorEvents(
			Set<Event<S, C>> events) {
		HashSet<Event<S, C>> result = new HashSet<Event<S, C>>();
		for (Event<S, C> e : events) {
			result.addAll(e.getPredecessorEvents());
		}
		return result;
	}

	/**
	 * returns the Set of all predecessor events of all predecessor conditions
	 * of the event
	 */
	public Set<Event<S, C>> getPredecessorEvents() {
		HashSet<Event<S, C>> result = new HashSet<Event<S, C>>();
		for (Condition<S, C> c : this.getPredecessorConditions()) {
			result.add(c.getPredecessorEvent());
		}
		return result;
	}

	/**
	 * returns true, if the homomorphism h of the corresponding branching
	 * process reduced to conditions and places is a well defined isomorphism.
	 * this is a helper method used only for assertions.
	 * 
	 * @param conditions
	 * @param places
	 * @return
	 */
	private boolean conditionToPlaceEqual(
			Collection<Condition<S, C>> conditions,
			Collection<Place<S, C>> places) {
		places = new HashSet<Place<S, C>>(places);
		for (Condition<S, C> c : conditions) {
			if (!places.remove(c.getPlace()))
				return false;
		}
		return places.isEmpty();
	}

	/**
	 * Creates a dummy event. Used as the root of a branchingprocess.
	 * 
	 * @param m_Successors
	 */
	public Event(PetriNetJulian<S, C> net) {
		this.m_Transition = null;
		this.m_LocalConfiguration = new Configuration<S, C>(
				new HashSet<Event<S, C>>());
		this.m_Mark = net.getInitialMarking();
		Set<Condition<S, C>> conditionMarkSet = new HashSet<Condition<S, C>>();
		this.m_ConditionMark = new ConditionMarking<S, C>(conditionMarkSet);
		this.m_Predecessors = new HashSet<Condition<S, C>>();
		this.m_Successors = new HashSet<Condition<S, C>>();
		for (Place<S, C> p : m_Mark) {
			Condition<S, C> c = new Condition<S, C>(this, p);
			this.m_Successors.add(c);
			conditionMarkSet.add(c);
		}
		m_HashCode = computeHashCode();
	}

	public ConditionMarking<S, C> getConditionMark() {
		return m_ConditionMark;
	}

	public Set<Condition<S, C>> getSuccessorConditions() {
		return m_Successors;
	}

	public Set<Condition<S, C>> getPredecessorConditions() {
		return m_Predecessors;
	}

	/**
	 * @return marking of the local configuration of this.
	 */
	public Marking<S, C> getMark() {
		return m_Mark;
	}

	/**
	 * if e is a companion of this
	 * <ul>
	 * <li>return true and calls {@link Event#setCompanion(Event)}.</li>
	 * <li>otherwise return false.</li>
	 * </ul>
	 * 
	 * <b>Definition:</b> e is a companion of e' iff
	 * <ul>
	 * <li>e < e' with respect to order</li>
	 * <li>Mark([e]) == Mark([e'])</li>
	 * </ul>
	 * So far this definition corresponds to cut-off events as defined in the
	 * 1996 TACAS Paper.
	 * @param sameTransitionCutOff
	 * If true, additionally we require
	 * <ul>
	 * <li>e and e' belong to the same transition</li>
	 * </ul>
	 * which will produce fewer cut-off events and a bigger prefix hence.
	 * However, we assume the blowup is not so big TODO: check this claim.
	 * (maybe linear? with respect to what?)
	 * 
	 * @return
	 */
	public boolean checkCutOffSetCompanion(Event<S, C> e,
			Comparator<Event<S, C>> order, boolean sameTransitionCutOff) {
		if (sameTransitionCutOff) {
			// additional requirement for cut-off events.
			// TODO: tests to compare prefix sizes.
			if (!this.getTransition().equals(e.getTransition())) {
				return false;
			}
		}
		if (!getMark().equals(e.getMark())) {
			return false;
		}
		if (!(order.compare(e, this) < 0)) {
			return false;
		}
		setCompanion(e);
		return true;
	}

	/**
	 * set this.companion to e, or, if e is a cut-off event itself to the
	 * companion of e.
	 * 
	 * @param e
	 */
	private void setCompanion(Event<S, C> e) {
		assert this.m_Companion == null;
		if (e.getCompanion() == null) {
			this.m_Companion = e;
		} else {
			setCompanion(e.getCompanion());
		}
	}

	/**
	 * true, if the event is a cutoff event. requires, that
	 * {@link #checkCutOffSetCompanion(Event, Comparator)} was called.
	 * <p>
	 * In the implementation of the construction of the unfolding, it is called
	 * after being added to a the Branchinprocess.
	 * </p>
	 * 
	 * @see BranchingProcess#isCutoffEvent(Event, Comparator)
	 * @return
	 */
	public boolean isCutoffEvent() {
		return this.m_Companion != null;
	}

	/**
	 * returns the size of the local configuration, that is the number of
	 * ancestor events.
	 * 
	 * @return
	 */
	public int getAncestors() {
		return m_LocalConfiguration.size();
	}

	public Configuration<S, C> getLocalConfiguration() {
		return m_LocalConfiguration;
	}

	public Event<S, C> getCompanion() {
		return m_Companion;
	}

	public Transition<S, C> getTransition() {
		return m_Transition;
	}

	public String toString() {
		return m_HashCode + ":" + getTransition() + ","
				+ m_LocalConfiguration.size() + "A";
	}

	public int computeHashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((m_Predecessors == null) ? 0 : m_Predecessors.hashCode());
		// TODO remove successors from here later since they're not needed.
		result = prime * result
				+ ((m_Successors == null) ? 0 : m_Successors.hashCode());
		result = prime * result
				+ ((m_Transition == null) ? 0 : m_Transition.hashCode());
		return result;
	}

	@Override
	public int hashCode() {
		return m_HashCode;
	}

}