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

import java.io.Serializable;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;

public class Event<S, C> implements Serializable {
	private static final long serialVersionUID = 7162664880110047121L;
	
	private final int mHashCode;
	
	private final Set<Condition<S, C>> mPredecessors;
	private final Set<Condition<S, C>> mSuccessors;
	private final Configuration<S, C> mLocalConfiguration;
	// private final Event<S, C>[] mLocalConfiguration;
	// private final ArrayList<Event<S, C>> mLocalConfiguration;
	private final Marking<S, C> mMark;
	private final ConditionMarking<S, C> mConditionMark;
	
	private Event<S, C> mCompanion;
	private final Transition<S, C> mTransition;
	
	/**
	 * Creates an Event from its predecessor conditions and the transition from
	 * the net system it is mapped to by the homomorphism. Its successor
	 * conditions are automatically created. The given set not be referenced
	 * directly, but copied.
	 */
	public Event(final Collection<Condition<S, C>> predecessors,
			final Transition<S, C> transition) {
		assert conditionToPlaceEqual(predecessors,
				transition.getPredecessors()) : "An event was created with inappropriate predecessors.\n  "
						+ "transition: "
						+ transition.toString()
						+ "\n  events predecessors: "
						+ predecessors.toString()
						+ "\n  "
						+ "transitions predecessors:"
						+ transition.getPredecessors();
		this.mPredecessors = new HashSet<Condition<S, C>>(predecessors);
		// HashSet<Event<S, C>> localConfiguration = new HashSet<Event<S, C>>();
		this.mLocalConfiguration = new Configuration<S, C>(
				new HashSet<Event<S, C>>());
		this.mTransition = transition;
		final Set<Condition<S, C>> conditionMarkSet = new HashSet<Condition<S, C>>();
		
		final Set<Event<S, C>> predecessorEvents = new HashSet<Event<S, C>>();
		for (final Condition<S, C> c : predecessors) {
			final Event<S, C> e = c.getPredecessorEvent();
			if (predecessorEvents.contains(e)) {
				continue;
			}
			predecessorEvents.add(e);
			// Collections.addAll(localConfiguration, e.mLocalConfiguration);
			mLocalConfiguration.addAll(e.mLocalConfiguration);
			e.mConditionMark.addTo(conditionMarkSet);
		}
		
		mLocalConfiguration.add(this);
		
		this.mSuccessors = new HashSet<Condition<S, C>>();
		for (final Place<S, C> p : transition.getSuccessors()) {
			this.mSuccessors.add(new Condition<S, C>(this, p));
		}
		for (final Event<S, C> a : mLocalConfiguration) {
			conditionMarkSet.removeAll(a.getPredecessorConditions());
		}
		conditionMarkSet.addAll(mSuccessors);
		this.mConditionMark = new ConditionMarking<S, C>(conditionMarkSet);
		this.mMark = mConditionMark.getMarking();
		mHashCode = computeHashCode();
	}
	
	/**
	 * @return The Set of all successor conditions of {@code events}.
	 */
	public static <S, C> Set<Condition<S, C>> getDot(final Set<Event<S, C>> events) {
		final HashSet<Condition<S, C>> result = new HashSet<Condition<S, C>>();
		for (final Event<S, C> e : events) {
			result.addAll(e.getSuccessorConditions());
		}
		return result;
	}
	
	/**
	 * @return The Set of all successor events of all successor conditions of the event.
	 */
	public Set<Event<S, C>> getSuccessorEvents() {
		final HashSet<Event<S, C>> result = new HashSet<Event<S, C>>();
		for (final Condition<S, C> c : this.getSuccessorConditions()) {
			result.addAll(c.getSuccessorEvents());
		}
		return result;
	}
	
	/**
	 * @return The Set of all successor events of all successor conditions of {@code events}.
	 */
	public static <S, C> Set<Event<S, C>> getSuccessorEvents(
			final Set<Event<S, C>> events) {
		final HashSet<Event<S, C>> result = new HashSet<Event<S, C>>();
		for (final Event<S, C> e : events) {
			result.addAll(e.getSuccessorEvents());
		}
		return result;
	}
	
	/**
	 * @return The Set of all predecessor events of all predecessor conditions of {@code events}.
	 */
	public static <S, C> Set<Event<S, C>> getPredecessorEvents(
			final Set<Event<S, C>> events) {
		final HashSet<Event<S, C>> result = new HashSet<Event<S, C>>();
		for (final Event<S, C> e : events) {
			result.addAll(e.getPredecessorEvents());
		}
		return result;
	}
	
	/**
	 * @return The Set of all predecessor events of all predecessor conditions of the event.
	 */
	public Set<Event<S, C>> getPredecessorEvents() {
		final HashSet<Event<S, C>> result = new HashSet<Event<S, C>>();
		for (final Condition<S, C> c : this.getPredecessorConditions()) {
			result.add(c.getPredecessorEvent());
		}
		return result;
	}
	
	/**
	 * returns true, if the homomorphism h of the corresponding branching
	 * process reduced to conditions and places is a well defined isomorphism.
	 * this is a helper method used only for assertions.
	 */
	private boolean conditionToPlaceEqual(
			final Collection<Condition<S, C>> conditions,
			Collection<Place<S, C>> places) {
		places = new HashSet<Place<S, C>>(places);
		for (final Condition<S, C> c : conditions) {
			if (!places.remove(c.getPlace())) {
				return false;
			}
		}
		return places.isEmpty();
	}
	
	/**
	 * Creates a dummy event. Used as the root of a branchingprocess.
	 */
	public Event(final PetriNetJulian<S, C> net) {
		this.mTransition = null;
		this.mLocalConfiguration = new Configuration<S, C>(
				new HashSet<Event<S, C>>());
		this.mMark = net.getInitialMarking();
		final Set<Condition<S, C>> conditionMarkSet = new HashSet<Condition<S, C>>();
		this.mConditionMark = new ConditionMarking<S, C>(conditionMarkSet);
		this.mPredecessors = new HashSet<Condition<S, C>>();
		this.mSuccessors = new HashSet<Condition<S, C>>();
		for (final Place<S, C> p : mMark) {
			final Condition<S, C> c = new Condition<S, C>(this, p);
			this.mSuccessors.add(c);
			conditionMarkSet.add(c);
		}
		mHashCode = computeHashCode();
	}
	
	public ConditionMarking<S, C> getConditionMark() {
		return mConditionMark;
	}
	
	public Set<Condition<S, C>> getSuccessorConditions() {
		return mSuccessors;
	}
	
	public Set<Condition<S, C>> getPredecessorConditions() {
		return mPredecessors;
	}
	
	/**
	 * @return marking of the local configuration of this.
	 */
	public Marking<S, C> getMark() {
		return mMark;
	}
	
	/**
	 * if e is a companion of this
	 * <ul>
	 * <li>return true and calls {@link Event#setCompanion(Event)}.</li>
	 * <li>otherwise return false.</li>
	 * </ul>
	 * <b>Definition:</b> e is a companion of e' iff
	 * <ul>
	 * <li>e < e' with respect to order</li>
	 * <li>Mark([e]) == Mark([e'])</li>
	 * </ul>
	 * So far this definition corresponds to cut-off events as defined in the
	 * 1996 TACAS Paper.
	 * 
	 * @param sameTransitionCutOff
	 *            If true, additionally we require
	 *            <ul>
	 *            <li>e and e' belong to the same transition</li>
	 *            </ul>
	 *            which will produce fewer cut-off events and a bigger prefix hence.
	 *            However, we assume the blowup is not so big TODO: check this claim.
	 *            (maybe linear? with respect to what?)
	 */
	public boolean checkCutOffSetCompanion(final Event<S, C> e,
			final Comparator<Event<S, C>> order, final boolean sameTransitionCutOff) {
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
	 */
	private void setCompanion(final Event<S, C> e) {
		assert this.mCompanion == null;
		if (e.getCompanion() == null) {
			this.mCompanion = e;
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
	 */
	public boolean isCutoffEvent() {
		return this.mCompanion != null;
	}
	
	/**
	 * returns the size of the local configuration, that is the number of
	 * ancestor events.
	 */
	public int getAncestors() {
		return mLocalConfiguration.size();
	}
	
	public Configuration<S, C> getLocalConfiguration() {
		return mLocalConfiguration;
	}
	
	public Event<S, C> getCompanion() {
		return mCompanion;
	}
	
	public Transition<S, C> getTransition() {
		return mTransition;
	}
	
	@Override
	public String toString() {
		return mHashCode + ":" + getTransition() + ","
				+ mLocalConfiguration.size() + "A";
	}
	
	public int computeHashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((mPredecessors == null) ? 0 : mPredecessors.hashCode());
		// TODO remove successors from here later since they're not needed.
		result = prime * result
				+ ((mSuccessors == null) ? 0 : mSuccessors.hashCode());
		result = prime * result
				+ ((mTransition == null) ? 0 : mTransition.hashCode());
		return result;
	}
	
	@Override
	public int hashCode() {
		return mHashCode;
	}
	
}
