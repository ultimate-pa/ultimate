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
import java.util.HashSet;
import java.util.List;
import java.util.PriorityQueue;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.ISuccessorTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.SimpleSuccessorTransitionProvider;

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
	private final boolean mLazySuccessorComputation = !false;

	/**
	 * A candidate is useful if it lead to at least one new possible extension.
	 */
	private int mUsefulCandidates = 0;
	private int mUselessCandidates = 0;

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
			if (candidate.getInstantiated().isEmpty()) {
				throw new AssertionError("at least one place has to be instantiated");
			}
			final int possibleExtensionsBefore = mPe.size();
			evolveCandidate(candidate);
			if (mPe.size() > possibleExtensionsBefore) {
				mUsefulCandidates++;
			} else {
				mUselessCandidates++;
			}
		}
	}

	/**
	 * Evolves a {@code Candidate} for a new possible Event in all possible ways and, as a side-effect, adds valid
	 * extensions (ones whose predecessors are a co-set) to he possible extension set.
	 */
	@SuppressWarnings("squid:S1698")
	private void evolveCandidate(final Candidate<LETTER, PLACE> cand) {
		if (cand.isFullyInstantiated()) {
			for (final ITransition<LETTER, PLACE> trans : cand.getTransition().getTransitions()) {
				final boolean somethingWasAdded = mPe.add(new Event<>(cand.getInstantiated(), trans, mBranchingProcess));
				if (!somethingWasAdded) {
					throw new AssertionError("Event was already in queue.");
				}
			}
			return;
		}
		final PLACE p = cand.getNextUninstantiatedPlace();
		for (final Condition<LETTER, PLACE> c : mBranchingProcess.place2cond(p)) {
			assert cand.getTransition().getPredecessorPlaces().contains(c.getPlace());
			// equality intended here
			assert c.getPlace().equals(p);
			assert !cand.getInstantiated().contains(c);
			if (mBranchingProcess.getCoRelation().isCoset(cand.getInstantiated(), c)) {
				cand.instantiateNext(c);
				evolveCandidate(cand);
				cand.undoOneInstantiation();
			}
		}
	}



	/**
	 * @return All {@code Candidate}s for possible extensions that are successors of the {@code Event}.
	 */
	private Collection<Candidate<LETTER, PLACE>> computeCandidates(final Event<LETTER, PLACE> event) {
		if (mLazySuccessorComputation) {
			final Set<Condition<LETTER, PLACE>> conditions = event.getSuccessorConditions();
			final Set<PLACE> correspondingPlaces = conditions.stream().map(Condition::getPlace).collect(Collectors.toSet());
			final Collection<ISuccessorTransitionProvider<LETTER, PLACE>> successorTransitionProviders = mBranchingProcess
					.getNet().getSuccessorTransitionProviders(correspondingPlaces);
			final List<Candidate<LETTER, PLACE>> candidates = successorTransitionProviders.stream()
					.map(x -> new Candidate<LETTER, PLACE>(x, conditions)).collect(Collectors.toList());
			return candidates;
		} else {
			if (!(mBranchingProcess.getNet() instanceof IPetriNet)) {
				throw new IllegalArgumentException("non-lazy computation only available for fully constructed nets");
			}
			final IPetriNet<LETTER, PLACE> fullPetriNet = (IPetriNet<LETTER, PLACE>) mBranchingProcess.getNet();
			final Set<ITransition<LETTER, PLACE>> transitions = new HashSet<>();
			for (final Condition<LETTER, PLACE> cond : event.getSuccessorConditions()) {
				for (final ITransition<LETTER, PLACE> t : fullPetriNet.getSuccessors(cond.getPlace())) {
					transitions.add(t);
				}
			}
			final List<Candidate<LETTER, PLACE>> candidates = new ArrayList<>();
			for (final ITransition<LETTER, PLACE> transition : transitions) {
				final Candidate<LETTER, PLACE> candidate = new Candidate<>(new SimpleSuccessorTransitionProvider<>(
						Collections.singleton(transition), fullPetriNet), event.getSuccessorConditions());
				candidates.add(candidate);
			}
			return candidates;
		}
	}


	@Override
	public boolean isEmpy() {
		return mPe.isEmpty();
	}

	@Override
	public int size() {
		return mPe.size();
	}

	public int getUsefulCandidates() {
		return mUsefulCandidates;
	}

	public int getUselessCandidates() {
		return mUselessCandidates;
	}


}
