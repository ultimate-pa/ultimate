/*
 * Copyright (C) 2012-2015 Julian Jarecki (jareckij@informatik.uni-freiburg.de)
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
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;


/**
 * Represents a Suffix of a Configuration. A Configuration is a Set of Events
 * which is causally closed and conflict-free. A Set E is called Suffix if there
 * is a Configuration C, such that
 * <ul>
 * <li>C united with E is a Configuration</li>
 * <li>The intersection of C and E is empty</li>
 * </ul>
 *
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            symbol type
 * @param <PLACE>
 *            place content type
 */
public class Configuration<LETTER, PLACE> implements Iterable<Event<LETTER, PLACE>> {
	private final ArrayList<Event<LETTER, PLACE>> mEvents;
	private final ArrayList<List<Event<LETTER, PLACE>>> mFoataNormalForm;
	private boolean mSorted = false;
	private boolean mFoataComputed = false;
	private int lastSortedMinimum = 0;
	private final int mConfigurationDepth;
	private final static boolean USE_DEPTH_TO_COMPUTE_FNF = true;


	public Configuration(final Set<Event<LETTER, PLACE>> events, final int configurationDepth) {
		mEvents = new ArrayList<>(events);
		mFoataNormalForm = new ArrayList<>(configurationDepth + 1);
		mConfigurationDepth= configurationDepth;
	}

	private List<Event<LETTER, PLACE>> getMinPhi(final int depth, Comparator<Event<LETTER, PLACE>> comparator) {
		if (lastSortedMinimum < depth) {
			mFoataNormalForm.get(depth).sort(comparator);
			lastSortedMinimum = depth;
		}
		return mFoataNormalForm.get(depth);
	}

	@Override
	public Iterator<Event<LETTER, PLACE>> iterator() {
		return mEvents.iterator();
	}

	public int size() {
		return mEvents.size();
	}

	/**
	 * Compares configurations initially based on size. In case of equal size,
	 * lexically compares the ordered sequences of events with respect to the the
	 * total order on their transitions.
	 */

	public int compareTo(final Configuration<LETTER, PLACE> other, Comparator<Event<LETTER, PLACE>> comparator) {
		if (size() != other.size()) {
			return size() - other.size();
		}
		computePhi(comparator);
		other.computePhi(comparator);
		return comparePhi(mEvents, other.mEvents, comparator);
	}

	public int compareMin(final Configuration<LETTER, PLACE> other, final int depth,
			Comparator<Event<LETTER, PLACE>> comparator) {
		int result = mFoataNormalForm.get(depth).size() - other.mFoataNormalForm.get(depth).size();
		if (result != 0) {
			return result;
		}
		final List<Event<LETTER, PLACE>> phi1 = getMinPhi(depth, comparator);
		final List<Event<LETTER, PLACE>> phi2 = other.getMinPhi(depth, comparator);
		return comparePhi(phi1, phi2, comparator);
	}

	private int comparePhi(final List<Event<LETTER, PLACE>> phi1, final List<Event<LETTER, PLACE>> phi2,
			Comparator<Event<LETTER, PLACE>> comparator) {
		for (int i = 0; i < phi1.size(); i++) {
			final int result = comparator.compare(phi1.get(i), phi2.get(i));
			if (result != 0) {
				return result;
			}
		}
		return 0;
	}

	private void computePhi(Comparator<Event<LETTER, PLACE>> comparator) {
		if (!mSorted) {
			Collections.sort(mEvents, comparator);
			mSorted = true;
		}
	}
	
	public ArrayList<Event<LETTER, PLACE>> getSortedConfiguration(Comparator<Event<LETTER, PLACE>> comparator) {
		final ArrayList<Event<LETTER, PLACE>>  result = new ArrayList<>(mEvents);
		Collections.sort(result, comparator);
		return result;
	}

	public void computeFoataNormalFormUsingDepth() {
			for (int i = 0; i < mConfigurationDepth + 1; i++) {
				mFoataNormalForm.add(new ArrayList<>());
			}
			for (final Event<LETTER, PLACE> e : mEvents) {
				mFoataNormalForm.get(e.getDepth()).add(e);
			}
		
	}
	public void computeFoataNormalFormIntuitively() {
		final Set<Event<LETTER,PLACE>> remainingEvents = new HashSet<>(mEvents);
		Set<Event<LETTER, PLACE>> minimum = mEvents.stream().filter(event -> event.getAncestors() == 1).collect(Collectors.toCollection(HashSet::new));
		mFoataNormalForm.add(new ArrayList<>(minimum));
		while(!minimum.isEmpty()) {
			remainingEvents.removeAll(minimum);
			minimum = Event.getSuccessorEvents(minimum).stream().filter(e -> remainingEvents.contains(e) &&
					!(e.getPredecessorEvents().stream().anyMatch(e2 -> remainingEvents.contains(e2)))).collect(Collectors.toCollection(HashSet::new));
			mFoataNormalForm.add(new ArrayList<>(minimum));
		}
		mFoataNormalForm.add(new ArrayList<>(remainingEvents));
	}

	public void computeFoataNormalForm() {
		if (!mFoataComputed) {
			if(USE_DEPTH_TO_COMPUTE_FNF) {
				computeFoataNormalFormUsingDepth();
			} else {
				computeFoataNormalFormIntuitively();
			}
			mFoataComputed = true;
		}
		
	}
	
	public int getDepth() {
		return mConfigurationDepth;
	}
	
	public List<Event<LETTER, PLACE>> getEvents(){
		return mEvents;
	}
	public boolean contains(Event<LETTER, PLACE> e) {
		return mEvents.contains(e);
	}
}
