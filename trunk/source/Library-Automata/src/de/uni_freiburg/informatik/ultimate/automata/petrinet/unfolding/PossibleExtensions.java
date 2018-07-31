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
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.SimpleSuccessorTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;

/**
 * Implementation of a possible extension.
 *
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            symbol type
 * @param <PLACE>
 *            place content type
 */
public class PossibleExtensions<LETTER, PLACE> implements IPossibleExtensions<LETTER, PLACE> {

	private final PriorityQueue<Event<LETTER, PLACE>> mPe;
	private final BranchingProcess<LETTER, PLACE> mBranchingProcess;

	public PossibleExtensions(final BranchingProcess<LETTER, PLACE> branchingProcess, final Comparator<Event<LETTER, PLACE>> order) {
		mBranchingProcess = branchingProcess;
		mPe = new PriorityQueue<>(order);
	}

	@Override
	public Event<LETTER, PLACE> remove() {
		return mPe.remove();
	}

	@Override
	public void update(final Event<LETTER, PLACE> event) {
		final Collection<Candidate<LETTER, PLACE>> candidates = computeCandidates(event);
		for (final Candidate<LETTER, PLACE> candidate : candidates) {
			evolveCandidate(candidate);
		}
	}

	/**
	 * Evolves a {@code Candidate} for a new possible Event in all possible ways and, as a side-effect, adds valid
	 * extensions (ones whose predecessors are a co-set) to he possible extension set.
	 */
	@SuppressWarnings("squid:S1698")
	private void evolveCandidate(final Candidate<LETTER, PLACE> cand) {
		if (cand.getPlaces().isEmpty()) {
			for (final ITransition<LETTER, PLACE> trans : cand.getTransition().getTransitions()) {
				mPe.add(new Event<>(cand.getChosen(), trans, mBranchingProcess));
			}
			return;
		}
		// mod!
		final PLACE p = cand.getPlaces().remove(cand.getPlaces().size() - 1);
		for (final Condition<LETTER, PLACE> c : mBranchingProcess.place2cond(p)) {
			assert cand.getTransition().getPredecessorPlaces().contains(c.getPlace());
			// equality intended here
			assert c.getPlace().equals(p);
			assert !cand.getChosen().contains(c);
			if (mBranchingProcess.isCoset(cand.getChosen(), c)) {
				// mod!
				cand.getChosen().add(c);
				evolveCandidate(cand);
				// mod!
				cand.getChosen().remove(cand.getChosen().size() - 1);
			}
		}
		// mod!
		cand.getPlaces().add(p);
	}

	/**
	 * @return All {@code Candidate}s for possible extensions that are successors of the {@code Event}.
	 */
	private Collection<Candidate<LETTER, PLACE>> computeCandidates(final Event<LETTER, PLACE> event) {
		final Map<ITransition<LETTER, PLACE>, Candidate<LETTER, PLACE>> candidates = new HashMap<>();
		for (final Condition<LETTER, PLACE> cond0 : event.getSuccessorConditions()) {
			for (final ITransition<LETTER, PLACE> t : mBranchingProcess.getNet().getSuccessors(cond0.getPlace())) {
				Candidate<LETTER, PLACE> current;
				if (!candidates.containsKey(t)) {
					final Transition<LETTER, PLACE> trans = (Transition<LETTER, PLACE>) t;
					current = new Candidate<>(new SimpleSuccessorTransitionProvider<>(Collections.singleton(trans),
							mBranchingProcess.getNet()));
					candidates.put(t, current);
				} else {
					current = candidates.get(t);
				}
				current.getChosen().add(cond0);
				current.getPlaces().remove(cond0.getPlace());
				assert current.getPlaces().size() + current.getChosen().size() == mBranchingProcess.getNet().getPredecessors(t).size();
			}
		}
//		Collection<Candidate<LETTER, PLACE>> alternativeResult = computeCandidatesCollectTransitionsFirst(event);
		return candidates.values();
	}
	
	private Collection<Candidate<LETTER, PLACE>> computeCandidatesCollectTransitionsFirst(final Event<LETTER, PLACE> event) {
		Set<ITransition<LETTER, PLACE>> transitions = new HashSet<>();
		for (final Condition<LETTER, PLACE> cond0 : event.getSuccessorConditions()) {
			for (final ITransition<LETTER, PLACE> t : mBranchingProcess.getNet().getSuccessors(cond0.getPlace())) {
				transitions.add(t);
			}
		}
		List<Candidate<LETTER, PLACE>> candidates = new ArrayList<>();
		for (ITransition<LETTER, PLACE> transition : transitions) {
			candidates.add(new Candidate<>(new SimpleSuccessorTransitionProvider<>(Collections.singleton(transition), mBranchingProcess.getNet())));
		}
		return candidates;
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
