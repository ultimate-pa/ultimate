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

import java.util.ArrayList;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;

/**
 * represents an incomplete Event.
 * A <i>Candidate</i> consists of
 * <ul>
 * <li>the transition which belongs to the event</li>
 * <li>a subset of conditions of the set of predecessors of the event.</li>
 * <li>the set of predecessor-places of the transition minus the places that
 * correspond with the conditions in the given condition-set.</li>
 * </ul>
 **/
public class Candidate<S, C> {
	public final Transition<S, C> mT;
	public final ArrayList<Condition<S, C>> mChosen;
	public final ArrayList<Place<S, C>> mPlaces;
	
	public Candidate(
			final Map.Entry<Transition<S, C>, Map<Place<S, C>, Condition<S, C>>> candidate) {
		this.mT = candidate.getKey();
		this.mChosen = new ArrayList<Condition<S, C>>(candidate.getValue()
				.values());
		this.mPlaces = new ArrayList<Place<S, C>>(candidate.getValue().keySet());
	}

	public Candidate(final Transition<S, C> t2) {
		this.mT = t2;
		this.mChosen = new ArrayList<Condition<S, C>>(mT.getPredecessors().size());
		this.mPlaces = new ArrayList<Place<S, C>>(mT.getPredecessors());
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mChosen == null) ? 0 : mChosen.hashCode());
		result = prime * result + ((mPlaces == null) ? 0 : mPlaces.hashCode());
		result = prime * result + ((mT == null) ? 0 : mT.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final Candidate<?, ?> other = (Candidate<?, ?>) obj;
		if (mChosen == null) {
			if (other.mChosen != null) {
				return false;
			}
		} else if (!mChosen.equals(other.mChosen)) {
			return false;
		}
		if (mPlaces == null) {
			if (other.mPlaces != null) {
				return false;
			}
		} else if (!mPlaces.equals(other.mPlaces)) {
			return false;
		}
		if (mT == null) {
			if (other.mT != null) {
				return false;
			}
		} else if (!mT.equals(other.mT)) {
			return false;
		}
		return true;
	}	
}
