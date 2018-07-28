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

import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.PriorityQueue;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;

/**
 * Implementation of a possible extension.
 *
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <S>
 *            symbol type
 * @param <C>
 *            place content type
 */
public class PossibleExtensions<S, C> implements IPossibleExtensions<S, C> {

	private final PriorityQueue<Event<S, C>> mPe;
	private final BranchingProcess<S, C> mBranchingProcess;

	public PossibleExtensions(final BranchingProcess<S, C> branchingProcess, final Comparator<Event<S, C>> order) {
		mBranchingProcess = branchingProcess;
		mPe = new PriorityQueue<>(order);
	}

	@Override
	public Event<S, C> remove() {
		return mPe.remove();
	}

	@Override
	public void update(final Event<S, C> event) {
		final Collection<Candidate<S, C>> candidates = computeCandidates(event);
		for (final Candidate<S, C> candidate : candidates) {
			evolveCandidate(candidate);
		}
	}

	/**
	 * Evolves a {@code Candidate} for a new possible Event in all possible ways and, as a side-effect, adds valid
	 * extensions (ones whose predecessors are a co-set) to he possible extension set.
	 */
	@SuppressWarnings("squid:S1698")
	private void evolveCandidate(final Candidate<S, C> cand) {
		if (cand.mPlaces.isEmpty()) {
			mPe.add(new Event<>(cand.mChosen, cand.mT));
			return;
		}
		final C p = cand.mPlaces.remove(cand.mPlaces.size() - 1);
		for (final Condition<S, C> c : mBranchingProcess.place2cond(p)) {
			assert cand.mT.getPredecessors().contains(c.getPlace());
			// equality intended here
			assert c.getPlace().equals(p);
			assert !cand.mChosen.contains(c);
			if (mBranchingProcess.isCoset(cand.mChosen, c)) {
				cand.mChosen.add(c);
				evolveCandidate(cand);
				cand.mChosen.remove(cand.mChosen.size() - 1);
			}
		}
		cand.mPlaces.add(p);
	}

	/**
	 * @return All {@code Candidate}s for possible extensions that are successors of the {@code Event}.
	 */
	private Collection<Candidate<S, C>> computeCandidates(final Event<S, C> event) {
		final Map<ITransition<S, C>, Candidate<S, C>> candidates = new HashMap<>();
		for (final Condition<S, C> cond0 : event.getSuccessorConditions()) {
			for (final ITransition<S, C> t : mBranchingProcess.getNet().getSuccessors(cond0.getPlace())) {
				Candidate<S, C> current;
				if (!candidates.containsKey(t)) {
					current = new Candidate<>((Transition<S, C>) t);
					candidates.put(t, current);
				} else {
					current = candidates.get(t);
				}
				current.mChosen.add(cond0);
				current.mPlaces.remove(cond0.getPlace());
				assert current.mPlaces.size() + current.mChosen.size() == mBranchingProcess.getNet().getPredecessors(t).size();
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
