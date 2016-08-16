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
import java.util.Map;
import java.util.PriorityQueue;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;

public class PossibleExtensions<S, C> implements IPossibleExtensions<S, C> {

	private final PriorityQueue<Event<S, C>> mPe;
	private final BranchingProcess<S, C> mBranchingProcess;

	public PossibleExtensions(final BranchingProcess<S, C> branchingProcess,
			final Comparator<Event<S, C>> order) {
		this.mBranchingProcess = branchingProcess;

		// anonymous implementation of the Order corresponding to McMillans
		// Algorithm

		// TODO find an appropriate initial Capacity
		this.mPe = new PriorityQueue<Event<S, C>>(1000, order);
	}

	@Override
	public Event<S, C> remove() {
		return mPe.remove();
	}

	@Override
	public void update(final Event<S, C> e) {
		final Collection<Candidate<S, C>> candidates = computeCandidates(e);
		for (final Candidate<S, C> candidate : candidates) {
			evolveCandidate(candidate);
		}
	}


	/**
	 * Evolves a {@code Candidate} for a new possible Event in all possible ways
	 * and, as a side-effect, adds valid extensions (ones whose predecessors are
	 * a co-set) to he possible extension set.
	 */
	private void evolveCandidate(final Candidate<S, C> cand) {
		if (cand.mPlaces.isEmpty()) {
			mPe.add(new Event<S, C>(cand.mChosen, cand.mT));
			return;
		}
		final Place<S, C> p = cand.mPlaces.remove(cand.mPlaces.size() - 1);
		for (final Condition<S, C> c : mBranchingProcess.place2cond(p)) {
			assert cand.mT.getPredecessors().contains(c.getPlace());
			assert c.getPlace() == p;
			assert !cand.mChosen.contains(c);
			if (mBranchingProcess.isCoset(cand.mChosen, c)) {
				cand.mChosen.add(c);
				evolveCandidate(cand);
				cand.mChosen.remove(cand.mChosen.size() - 1);
			}
		}
		cand.mPlaces.add(p);
	}

	// private void evolveCandidate(Transition<S, C> t,
	// Set<Condition<S, C>> chosen, Collection<Place<S, C>> places) {

	/**
	 * computes all {@code Candidate}s for possible extensions that are
	 * successors of {@code Event} e
	 */
	private Collection<Candidate<S, C>> computeCandidates(final Event<S, C> e) {
		final int initCapacity = 2 
				* e.getSuccessorConditions().size()
				* e.getSuccessorConditions().iterator().next()
						.getPlace().getSuccessors().size();
		final Map<ITransition<S, C>, Candidate<S, C>> candidates = 
				new HashMap<ITransition<S, C>, Candidate<S, C>>(initCapacity);
		for (final Condition<S, C> c0 : e.getSuccessorConditions()) {
			for (final ITransition<S, C> t : c0.getPlace().getSuccessors()) {
				Candidate<S, C> current;
				if (!candidates.containsKey(t)) {
					current = new Candidate<S, C>((Transition<S, C>)t);
					candidates.put(t, current);
				} else {
					current = candidates.get(t);
				}
				current.mChosen.add(c0);
				current.mPlaces.remove(c0.getPlace());
				assert current.mPlaces.size() + current.mChosen.size() == t.getPredecessors().size();
			}
		}
		return candidates.values();
	}


	@Override
	public boolean isEmpy() {
		return mPe.isEmpty();
	}

	@Override
	public int size() {
		return mPe.size();
	}

}
