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
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Place;

/**
 * A condition.
 * 
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <S>
 *            symbol type
 * @param <C>
 *            place content type
 **/
public class Condition<S, C> implements Serializable {
	private static final long serialVersionUID = -497620137647502376L;

	private static int sSerialNumberCounter;

	private final Event<S, C> mPredecessor;
	private final Collection<Event<S, C>> mSuccessors;
	private final Place<C> mPlace;

	private final int mSerialNumber;

	/**
	 * Constructor.
	 * 
	 * @param predecessor
	 *            predecessor event
	 * @param place
	 *            place
	 */
	public Condition(final Event<S, C> predecessor, final Place<C> place) {
		mSerialNumber = sSerialNumberCounter;
		sSerialNumberCounter++;

		mPredecessor = predecessor;
		mSuccessors = new HashSet<>();
		mPlace = place;
	}

	/**
	 * Adds successors of an event.
	 * 
	 * @param event
	 *            event
	 */
	public void addSuccesssor(final Event<S, C> event) {
		mSuccessors.add(event);
	}

	public Collection<Event<S, C>> getSuccessorEvents() {
		return mSuccessors;
	}

	public Event<S, C> getPredecessorEvent() {
		return mPredecessor;
	}

	public Place<C> getPlace() {
		return mPlace;
	}

	@Override
	public String toString() {
		return "c" + mSerialNumber + ":CorrespPlace: " + mPlace.toString();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		return prime + mSerialNumber;
	}
}
