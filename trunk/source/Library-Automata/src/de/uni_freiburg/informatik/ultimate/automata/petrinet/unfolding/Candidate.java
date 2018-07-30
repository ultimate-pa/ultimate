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

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.ISuccessorTransitionProvider;

/**
 * Represents an incomplete Event. A <i>Candidate</i> consists of
 * <ul>
 * <li>the transition which belongs to the event</li>
 * <li>a subset of conditions of the set of predecessors of the event.</li>
 * <li>the set of predecessor-places of the transition minus the places that correspond with the conditions in the given
 * condition-set.</li>
 * </ul>
 *
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            symbol type
 * @param <PLACE>
 *            place content type
 **/
public class Candidate<LETTER, PLACE> {

	private final ISuccessorTransitionProvider<LETTER, PLACE> mSuccTransProvider;
	/**
	 * Chosen conditions.
	 */
	private final ArrayList<Condition<LETTER, PLACE>> mChosen;
	/**
	 * Places.
	 */
	private final ArrayList<PLACE> mPlaces;

//	/**
//	 * Constructor from another candidate.
//	 *
//	 * @param candidate
//	 *            candidate
//	 */
//	public Candidate(final Map.Entry<Transition<LETTER, PLACE>, Map<PLACE, Condition<LETTER, PLACE>>> candidate) {
//		mT = candidate.getKey();
//		mChosen = new ArrayList<>(candidate.getValue().values());
//		mPlaces = new ArrayList<>(candidate.getValue().keySet());
//	}

	/**
	 * Constructor with transition.
	 *
	 * @param transition
	 *            transition
	 */
	public Candidate(final ISuccessorTransitionProvider<LETTER, PLACE> succTransProvider) {
		mSuccTransProvider = succTransProvider;
		mChosen = new ArrayList<>(succTransProvider.getPredecessorPlaces().size());
		mPlaces = new ArrayList<>(succTransProvider.getPredecessorPlaces());
	}




	public ISuccessorTransitionProvider<LETTER, PLACE> getTransition() {
		return mSuccTransProvider;
	}




	public ArrayList<Condition<LETTER, PLACE>> getChosen() {
		return mChosen;
	}




	public ArrayList<PLACE> getPlaces() {
		return mPlaces;
	}




	@Override
	public int hashCode() {
		final int prime = 31;
		int result = prime + ((mChosen == null) ? 0 : mChosen.hashCode());
		result = prime * result + ((mPlaces == null) ? 0 : mPlaces.hashCode());
		result = prime * result + ((mSuccTransProvider == null) ? 0 : mSuccTransProvider.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || getClass() != obj.getClass()) {
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
		if (mSuccTransProvider == null) {
			if (other.mSuccTransProvider != null) {
				return false;
			}
		} else if (!mSuccTransProvider.equals(other.mSuccTransProvider)) {
			return false;
		}
		return true;
	}
}
