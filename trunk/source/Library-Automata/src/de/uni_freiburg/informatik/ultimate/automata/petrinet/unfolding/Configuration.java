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

import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;

// TODO: rewrite this class, possibly split it up to resolve this horrible ambiguity
/**
 * Represents a Suffix of a Configuration. A Configuration is a Set of Events which is causally closed and
 * conflict-free. A Set E is called Suffix if there is a Configuration C, such that
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
public class Configuration<LETTER, PLACE> implements Comparable<Configuration<LETTER, PLACE>>, Iterable<Event<LETTER, PLACE>> {
	private final Set<Event<LETTER, PLACE>> mEvents;
	private Set<Event<LETTER, PLACE>> mMin;
	private ArrayList<Transition<LETTER, PLACE>> mPhi;
	private List<Event<LETTER, PLACE>> mSortedConfiguration;
	private final int mRemovedMin;
	private int mDepth;
//	private SortedMap<Integer, T<Event<LETTER, PLACE>>> mSortedEvents;
	/**
	 * Constructs a Configuration (Not a Suffix). The set given as parameter has to be causally closed and
	 * conflict-free.
	 *
	 * @param events
	 *            set of events
	 */
	public Configuration(final Set<Event<LETTER, PLACE>> events) {
		this(events, 0);
	}

	/**
	 * Constructor with a minimum set of events.
	 *
	 * @param events
	 *            set of events
	 * @param min
	 *            minimum set of events
	 */
	private Configuration(final Set<Event<LETTER, PLACE>> events, final int removedMin) {
		mEvents = events;
		mRemovedMin = removedMin;
	}

	private List<Transition<LETTER, PLACE>> getPhi() {
		if (mPhi == null) {
			mPhi = new ArrayList<>(mEvents.size());
			for (final Event<LETTER, PLACE> e : mEvents) {
				mPhi.add((Transition<LETTER, PLACE>) e.getTransition());
			}
			Collections.sort(mPhi);
		}
		return mPhi;
	}

	/**
	 * Returns the causally minimal Events in this Configuration.
	 * An Event e is causally minimal in a Configuration,
	 * iff all Events preceding e are not in the configuration.
	 *
	 * @return causally minimal Events in this Configuration
	 */
	public Configuration<LETTER, PLACE> getMin() {
		if (mMin == null) {
			mMin = computeMin();
		}
		return new Configuration<>(mMin);
	}
	public Configuration<LETTER, PLACE> getMin(final int depth){
		final Set<Event<LETTER, PLACE>> result = mEvents.stream()
				.filter(event -> event.getDepth() == depth)
				.collect(Collectors.toCollection(HashSet::new));
		if (result.isEmpty()) {
			throw new AssertionError("minimum must not be empty");
		}
		return new Configuration<>(result);
	}
	public void setDepth(final int depth) {
		mDepth = depth;
	}
	public int getDepth() {
		return mDepth;
	}
	
	public List<Event<LETTER, PLACE>> getSortedConfiguration(final Comparator<Event<LETTER, PLACE>> comparator) {
		if (mSortedConfiguration == null) {
			mSortedConfiguration = mEvents.stream().sorted(comparator).collect(Collectors.toList());
		}
		return mSortedConfiguration; 
	}

	private Set<Event<LETTER, PLACE>> computeMin() {
		final Set<Event<LETTER, PLACE>> result = mEvents.stream()
				.filter(event -> event.getDepth() == mRemovedMin + 1)
				.collect(Collectors.toCollection(HashSet::new));
		if (result.isEmpty()) {
			throw new AssertionError("minimum must not be empty");
		}
		return result;
	}
	
	@Override
	public Iterator<Event<LETTER, PLACE>> iterator() {
		return mEvents.iterator();
	}

	public int size() {
		return mEvents.size();
	}

	public boolean add(final Event<LETTER, PLACE> arg0) {
		return mEvents.add(arg0);
	}

	/**
	 * improved implementation of removeMin.
	 * @return A new Configuration that contains the set difference between the original configuration and its minimum
	 *         regarding the casual relation.
	 *         <p>
	 *         requires, that getMin() has been called.
	 */
	public Configuration<LETTER, PLACE> removeMin() {
		assert mMin != null : "getMin() must have been called before removeMin()";
		assert !mMin.isEmpty() : "The minimum of a configuration must not be empty.";
		final HashSet<Event<LETTER, PLACE>> events = new HashSet<>(mEvents);
		events.removeAll(mMin);
		return new Configuration<>(events, mRemovedMin +1);
	}

	/**
	 * Compares configurations initially based on size. In case of equal size, lexically compares the ordered sequences
	 * of events with respect to the the total order on their transitions.
	 */
	@Override
	public int compareTo(final Configuration<LETTER, PLACE> other) {
		if (size() != other.size()) {
			return size() - other.size();
		}
		final List<Transition<LETTER, PLACE>> phi1 = getPhi();
		final List<Transition<LETTER, PLACE>> phi2 = other.getPhi();
		for (int i = 0; i < phi1.size(); i++) {
			final Transition<LETTER, PLACE> t1 = phi1.get(i);
			final Transition<LETTER, PLACE> t2 = phi2.get(i);
			final int result = t1.getTotalOrderId() - t2.getTotalOrderId();
			if (result != 0) {
				return result;
			}
		}
		return 0;
	}
}
