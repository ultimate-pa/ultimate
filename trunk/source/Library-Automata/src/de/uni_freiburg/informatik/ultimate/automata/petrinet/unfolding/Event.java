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

import java.io.Serializable;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;

/**
 * Event of a {@link BranchingProcess}.
 * Each event corresponds to a {@link ITransition} of a {@link IPetriNet}.
 *
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            symbol type
 * @param <PLACE>
 *            place content type
 */
public final class Event<LETTER, PLACE> implements Serializable {
	private static final long serialVersionUID = 7162664880110047121L;

	private final int mHashCode;

	private final Set<Condition<LETTER, PLACE>> mPredecessors;
	private final Set<Condition<LETTER, PLACE>> mSuccessors;
	private final Configuration<LETTER, PLACE> mLocalConfiguration;
	// private final Event<LETTER, PLACE>[] mLocalConfiguration;
	// private final ArrayList<Event<LETTER, PLACE>> mLocalConfiguration;
	private final Marking<LETTER, PLACE> mMark;
	private final ConditionMarking<LETTER, PLACE> mConditionMark;

	private Event<LETTER, PLACE> mCompanion;
	private final ITransition<LETTER, PLACE> mTransition;

	/**
	 * Creates an Event from its predecessor conditions and the transition from the net system it is mapped to by the
	 * homomorphism. Its successor conditions are automatically created. The given set not be referenced directly, but
	 * copied.
	 *
	 * @param predecessors
	 *            predecessor conditions
	 * @param transition
	 *            homomorphism transition
	 */
	public Event(final Collection<Condition<LETTER, PLACE>> predecessors, final ITransition<LETTER, PLACE> transition,
			final BoundedPetriNet<LETTER, PLACE> net) {
		assert conditionToPlaceEqual(predecessors,
				net.getPredecessors(transition)) : "An event was created with inappropriate predecessors.\n  "
						+ "transition: " + transition.toString() + "\n  events predecessors: " + predecessors.toString()
						+ "\n  " + "transitions predecessors:" + net.getPredecessors(transition);
		mPredecessors = new HashSet<>(predecessors);
		// HashSet<Event<LETTER, PLACE>> localConfiguration = new HashSet<Event<LETTER, PLACE>>();
		mLocalConfiguration = new Configuration<>(new HashSet<Event<LETTER, PLACE>>());
		mTransition = transition;
		final Set<Condition<LETTER, PLACE>> conditionMarkSet = new HashSet<>();

		final Set<Event<LETTER, PLACE>> predecessorEvents = new HashSet<>();
		for (final Condition<LETTER, PLACE> c : predecessors) {
			final Event<LETTER, PLACE> e = c.getPredecessorEvent();
			if (predecessorEvents.contains(e)) {
				continue;
			}
			predecessorEvents.add(e);
			// Collections.addAll(localConfiguration, e.mLocalConfiguration);
			mLocalConfiguration.addAll(e.mLocalConfiguration);
			e.mConditionMark.addTo(conditionMarkSet);
		}

		mLocalConfiguration.add(this);

		mSuccessors = new HashSet<>();
		for (final PLACE p : net.getSuccessors(transition)) {
			mSuccessors.add(new Condition<>(this, p));
		}
		for (final Event<LETTER, PLACE> a : mLocalConfiguration) {
			conditionMarkSet.removeAll(a.getPredecessorConditions());
		}
		conditionMarkSet.addAll(mSuccessors);
		mConditionMark = new ConditionMarking<>(conditionMarkSet);
		mMark = mConditionMark.getMarking();
		mHashCode = computeHashCode();
	}

	/**
	 * Creates a dummy event. Used as the root of a {@link BranchingProcess}.
	 *
	 * @param net
	 *            Petri net
	 */
	public Event(final BoundedPetriNet<LETTER, PLACE> net) {
		mTransition = null;
		mLocalConfiguration = new Configuration<>(new HashSet<Event<LETTER, PLACE>>());
		mMark = new Marking(net.getInitialPlaces());
		final Set<Condition<LETTER, PLACE>> conditionMarkSet = new HashSet<>();
		mConditionMark = new ConditionMarking<>(conditionMarkSet);
		mPredecessors = new HashSet<>();
		mSuccessors = new HashSet<>();
		for (final PLACE p : mMark) {
			final Condition<LETTER, PLACE> c = new Condition<>(this, p);
			mSuccessors.add(c);
			conditionMarkSet.add(c);
		}
		mHashCode = computeHashCode();
	}

	/**
	 * @return The Set of all successor events of all successor conditions of the event.
	 */
	public Set<Event<LETTER, PLACE>> getSuccessorEvents() {
		final HashSet<Event<LETTER, PLACE>> result = new HashSet<>();
		for (final Condition<LETTER, PLACE> c : getSuccessorConditions()) {
			result.addAll(c.getSuccessorEvents());
		}
		return result;
	}

	/**
	 * @param events
	 *            A set of events.
	 * @param <LETTER>
	 *            symbol type
	 * @param <PLACE>
	 *            place content type
	 * @return The Set of all successor events of all successor conditions of {@code events}.
	 */
	public static <LETTER, PLACE> Set<Event<LETTER, PLACE>> getSuccessorEvents(final Set<Event<LETTER, PLACE>> events) {
		final HashSet<Event<LETTER, PLACE>> result = new HashSet<>();
		for (final Event<LETTER, PLACE> e : events) {
			result.addAll(e.getSuccessorEvents());
		}
		return result;
	}

	/**
	 * @param events
	 *            A set of events.
	 * @param <LETTER>
	 *            symbol type
	 * @param <PLACE>
	 *            place content type
	 * @return The Set of all predecessor events of all predecessor conditions of {@code events}.
	 */
	public static <LETTER, PLACE> Set<Event<LETTER, PLACE>> getPredecessorEvents(final Set<Event<LETTER, PLACE>> events) {
		final HashSet<Event<LETTER, PLACE>> result = new HashSet<>();
		for (final Event<LETTER, PLACE> e : events) {
			result.addAll(e.getPredecessorEvents());
		}
		return result;
	}

	/**
	 * @return The Set of all predecessor events of all predecessor conditions of the event.
	 */
	public Set<Event<LETTER, PLACE>> getPredecessorEvents() {
		final HashSet<Event<LETTER, PLACE>> result = new HashSet<>();
		for (final Condition<LETTER, PLACE> c : getPredecessorConditions()) {
			result.add(c.getPredecessorEvent());
		}
		return result;
	}

	/**
	 * returns true, if the homomorphism h of the corresponding branching process reduced to conditions and places is a
	 * well defined isomorphism. this is a helper method used only for assertions.
	 */
	private boolean conditionToPlaceEqual(final Collection<Condition<LETTER, PLACE>> conditions,
			final Collection<PLACE> placesIn) {
		final Collection<PLACE> places = new HashSet<>(placesIn);
		for (final Condition<LETTER, PLACE> c : conditions) {
			if (!places.remove(c.getPlace())) {
				return false;
			}
		}
		return places.isEmpty();
	}

	public ConditionMarking<LETTER, PLACE> getConditionMark() {
		return mConditionMark;
	}

	public Set<Condition<LETTER, PLACE>> getSuccessorConditions() {
		return mSuccessors;
	}

	public Set<Condition<LETTER, PLACE>> getPredecessorConditions() {
		return mPredecessors;
	}

	/**
	 * @return marking of the local configuration of this.
	 */
	public Marking<LETTER, PLACE> getMark() {
		return mMark;
	}

	/**
	 * @param event
	 *            event
	 * @param order
	 *            order
	 * @param sameTransitionCutOff
	 *            If true, additionally we require
	 *            <ul>
	 *            <li>e and e' belong to the same transition</li>
	 *            </ul>
	 *            which will produce fewer cut-off events and a bigger prefix hence. However, we assume the blowup is
	 *            not so big TODO: check this claim. (maybe linear? with respect to what?)
	 * @return If the event is a companion of this
	 *         <ul>
	 *         <li>return true and calls {@link Event#setCompanion(Event)}.</li>
	 *         <li>otherwise return false.</li>
	 *         </ul>
	 *         <b>Definition:</b> e is a companion of e' iff
	 *         <ul>
	 *         <li>e < e' with respect to order</li>
	 *         <li>Mark([e]) == Mark([e'])</li>
	 *         </ul>
	 *         So far this definition corresponds to cut-off events as defined in the 1996 TACAS Paper.
	 */
	public boolean checkCutOffSetCompanion(final Event<LETTER, PLACE> event, final Comparator<Event<LETTER, PLACE>> order,
			final boolean sameTransitionCutOff) {
		if (sameTransitionCutOff) {
			// additional requirement for cut-off events.
			// TODO: tests to compare prefix sizes.
			if (!getTransition().equals(event.getTransition())) {
				return false;
			}
		}
		if (!getMark().equals(event.getMark())) {
			return false;
		}
		if (order.compare(event, this) >= 0) {
			return false;
		}
		setCompanion(event);
		return true;
	}

	/**
	 * set this.companion to e, or, if e is a cut-off event itself to the companion of e.
	 */
	private void setCompanion(final Event<LETTER, PLACE> event) {
		assert mCompanion == null;
		if (event.getCompanion() == null) {
			mCompanion = event;
		} else {
			setCompanion(event.getCompanion());
		}
	}

	/**
	 * @return {@code true} iff the event is a cutoff event. requires, that
	 *         {@link #checkCutOffSetCompanion(Event, Comparator)} was called.
	 *         <p>
	 *         In the implementation of the construction of the unfolding, it is called after being added to a the
	 *         Branchinprocess.
	 * @see BranchingProcess#isCutoffEvent(Event, Comparator)
	 */
	public boolean isCutoffEvent() {
		return mCompanion != null;
	}

	/**
	 * @return The size of the local configuration, that is the number of ancestor events.
	 */
	public int getAncestors() {
		return mLocalConfiguration.size();
	}

	public Configuration<LETTER, PLACE> getLocalConfiguration() {
		return mLocalConfiguration;
	}

	public Event<LETTER, PLACE> getCompanion() {
		return mCompanion;
	}

	public ITransition<LETTER, PLACE> getTransition() {
		return mTransition;
	}

	@Override
	public String toString() {
		return mHashCode + ":" + getTransition() + "," + mLocalConfiguration.size() + "A";
	}

	private int computeHashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mPredecessors == null) ? 0 : mPredecessors.hashCode());
		// TODO remove successors from here later since they're not needed.
		result = prime * result + ((mSuccessors == null) ? 0 : mSuccessors.hashCode());
		result = prime * result + ((mTransition == null) ? 0 : mTransition.hashCode());
		return result;
	}

	@Override
	public int hashCode() {
		return mHashCode;
	}
}
