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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.ISuccessorTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.SimpleSuccessorTransitionProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.TreePriorityQueue;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

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

	/**
	 * Use the optimization that is outlined in observation B07 in the following
	 * issue. https://github.com/ultimate-pa/ultimate/issues/448
	 */
	private static final boolean BUMBLEBEE_B07_OPTIMIZATION = true;
	private final Queue<Event<LETTER, PLACE>> mPe;
	private final Map<Marking<LETTER, PLACE>, Event<LETTER, PLACE>> mMarkingEventMap = new HashMap<>();
	private int mMaximalSize = 0;
	private static final boolean USE_PQ = true;
	private final boolean mUseFirstbornCutoffCheck;
	/**
	 * If {@link Event} is known to be cut-off event we can move it immediately
	 * to front because it will not create descendants. This optimization keeps
	 * the queue smaller. TODO 2019-10-16 Matthias: Mehdi found out that this
	 * ArrayDeque is currently unused because the cut-off detection is only done
	 * later. We could to an additional cut-off check earlier but we have doubts
	 * that this will pay off.
	 */
	private final Comparator<Event<LETTER, PLACE>> mOrder;
	private final ArrayDeque<Event<LETTER, PLACE>> mFastpathCutoffEventList;
	private final BranchingProcess<LETTER, PLACE> mBranchingProcess;
	private final boolean mLazySuccessorComputation = true;

	/**
	 * A candidate is useful if it lead to at least one new possible extension.
	 */
	private int mUsefulExtensionCandidates = 0;
	private int mUselessExtensionCandidates = 0;

	public PossibleExtensions(final BranchingProcess<LETTER, PLACE> branchingProcess,
			final EventOrder<LETTER, PLACE> order, final boolean useFirstbornCutoffCheck) {
		mUseFirstbornCutoffCheck = useFirstbornCutoffCheck;
		mBranchingProcess = branchingProcess;
		if (USE_PQ) {
			mPe = new PriorityQueue<>(order);
		} else {
			if (!order.isTotal()) {
				throw new UnsupportedOperationException(TreePriorityQueue.class.getSimpleName()
						+ " can only be used in combination with total orders.");
			}
			mPe = new TreePriorityQueue<>(order);
		}
		mFastpathCutoffEventList = new ArrayDeque<>();
		mOrder = order;
		mMarkingEventMap.put(mBranchingProcess.getDummyRoot().getMark(), mBranchingProcess.getDummyRoot());
	}

	@Override
	public Event<LETTER, PLACE> remove() {
		if (mFastpathCutoffEventList.isEmpty()) {
			return mPe.remove();
		} else {
			return mFastpathCutoffEventList.removeFirst();
		}
	}

	@Override
	public void update(final Event<LETTER, PLACE> event) throws PetriNetNot1SafeException {
		final Collection<Candidate<LETTER, PLACE>> candidates = computeCandidates(event);
		for (final Candidate<LETTER, PLACE> candidate : candidates) {
			if (candidate.getInstantiated().isEmpty()) {
				throw new AssertionError("at least one place has to be instantiated");
			}
			final int possibleExtensionsBefore = size();
			evolveCandidate(candidate);
			if (size() > possibleExtensionsBefore) {
				mUsefulExtensionCandidates++;
			} else {
				mUselessExtensionCandidates++;
			}
		}
	}

	private boolean firstbornCutoffCheck(final Event<LETTER, PLACE> newEvent) {
		final Event<LETTER, PLACE> eventWithSameMarking = mMarkingEventMap.get(newEvent.getMark());
		if (eventWithSameMarking == null) {
			return false;
		}

		if (mOrder.compare(newEvent, eventWithSameMarking) > 0) {
			newEvent.setCompanion(eventWithSameMarking);
			return true;
		} else {
			boolean eventWithSameMarkingWasInTheMainQueu;
			eventWithSameMarkingWasInTheMainQueu = mPe.remove(eventWithSameMarking);
			assert(eventWithSameMarkingWasInTheMainQueu);
			mFastpathCutoffEventList.add(eventWithSameMarking);
			eventWithSameMarking.setCompanion(newEvent);
			return false;
		}
	}
	/**
	 * Evolves a {@code Candidate} for a new possible Event in all possible ways and, as a side-effect, adds valid
	 * extensions (ones whose predecessors are a co-set) to he possible extension set.
	 */
	@SuppressWarnings("squid:S1698")
	private void evolveCandidate(final Candidate<LETTER, PLACE> cand) throws PetriNetNot1SafeException {
		if (cand.isFullyInstantiated()) {
			for (final ITransition<LETTER, PLACE> trans : cand.getTransition().getTransitions()) {
				final Event<LETTER, PLACE> newEvent = new Event<>(cand.getInstantiated(), trans, mBranchingProcess);
				if (mUseFirstbornCutoffCheck) {
					if (firstbornCutoffCheck(newEvent)) {
						mFastpathCutoffEventList.add(newEvent);
					} else {
						mMarkingEventMap.put(newEvent.getMark(), newEvent);
						final boolean somethingWasAdded = mPe.add(newEvent);
						mMaximalSize = Integer.max(mMaximalSize, mPe.size());
						if (!somethingWasAdded) {
							throw new AssertionError("Event was already in queue.");
						}
					}
				} else {
					final boolean somethingWasAdded = mPe.add(newEvent);
					mMaximalSize = Integer.max(mMaximalSize, mPe.size());
					if (!somethingWasAdded) {
						throw new AssertionError("Event was already in queue.");
					}
				}
			}
			return;
		}
		final PLACE nextUninstantiated = cand.getNextUninstantiatedPlace();
		if (BUMBLEBEE_B07_OPTIMIZATION) {
			final List<Condition<LETTER, PLACE>> yetInstantiated = cand.getInstantiated();
			// list that contains one set for each instantiated condition c
			// the set contains all conditions that are in co-relation to c and
			// whose place is 'nextUninstantiated'
			final List<Set<Condition<LETTER, PLACE>>> coRelatedWithInstantiated = new ArrayList<>();
			for (final Condition<LETTER, PLACE> instantiated : yetInstantiated) {
				final Set<Condition<LETTER, PLACE>> coRelatedToInstantiated = mBranchingProcess.getCoRelation()
						.computeCoRelatatedConditions(instantiated, nextUninstantiated);
				// 2019-10-18 Matthias Optimization: Use construction cache
				// because while backtracking same set is computed several times
				coRelatedWithInstantiated.add(coRelatedToInstantiated);
			}
			final Set<Condition<LETTER, PLACE>> inCoRelationWithAllInstantiated = DataStructureUtils
					.intersection(coRelatedWithInstantiated);
			for (final Condition<LETTER, PLACE> c : inCoRelationWithAllInstantiated) {
				assert cand.getTransition().getPredecessorPlaces().contains(c.getPlace());
				// equality intended here
				assert c.getPlace().equals(nextUninstantiated);
				assert !cand.getInstantiated().contains(c);
				if (!c.getPredecessorEvent().isCutoffEvent()) {
					cand.instantiateNext(c);
					evolveCandidate(cand);
					cand.undoOneInstantiation();
				}
			}
		} else {
			for (final Condition<LETTER, PLACE> c : mBranchingProcess.place2cond(nextUninstantiated)) {
				assert cand.getTransition().getPredecessorPlaces().contains(c.getPlace());
				// equality intended here
				assert c.getPlace().equals(nextUninstantiated);
				assert !cand.getInstantiated().contains(c);
				if (!c.getPredecessorEvent().isCutoffEvent()) {
					if (mBranchingProcess.getCoRelation().isCoset(cand.getInstantiated(), c)) {
						cand.instantiateNext(c);
						evolveCandidate(cand);
						cand.undoOneInstantiation();
					}
				}
			}
		}
	}



	/**
	 * @return All {@code Candidate}s for possible extensions that are successors of
	 *         the {@code Event}.
	 */
	private Collection<Candidate<LETTER, PLACE>> computeCandidates(final Event<LETTER, PLACE> event) {
		if (event.getSuccessorConditions().isEmpty()) {
			return Collections.emptySet();
		}
		if (mLazySuccessorComputation) {
			final Set<Condition<LETTER, PLACE>> newConditions = event.getSuccessorConditions();
			final ICoRelation<LETTER, PLACE> coRelation = mBranchingProcess.getCoRelation();
			final Set<Condition<LETTER, PLACE>> coRelatedConditions = coRelation.computeCoRelatatedConditions(newConditions.iterator().next());
			final HashRelation<PLACE, Condition<LETTER, PLACE>> place2coRelatedConditions = new HashRelation<>();
			for (final Condition<LETTER, PLACE> c : coRelatedConditions) {
				place2coRelatedConditions.addPair(c.getPlace(), c);
			}
			final HashRelation<PLACE, PLACE> place2allowedSiblings = new HashRelation<>();
			for (final Condition<LETTER, PLACE> c : newConditions) {
				place2allowedSiblings.addAllPairs(c.getPlace(), place2coRelatedConditions.getDomain());
			}
			final Collection<ISuccessorTransitionProvider<LETTER, PLACE>> successorTransitionProviders = mBranchingProcess
					.getNet().getSuccessorTransitionProviders(place2allowedSiblings);
			final List<Candidate<LETTER, PLACE>> candidates = successorTransitionProviders.stream()
					.map(x -> new Candidate<LETTER, PLACE>(x, newConditions, place2coRelatedConditions)).collect(Collectors.toList());
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
				final Candidate<LETTER, PLACE> candidate = new Candidate<>(
						new SimpleSuccessorTransitionProvider<>(Collections.singleton(transition), fullPetriNet),
						event.getSuccessorConditions(), null);
				candidates.add(candidate);
			}
			return candidates;
		}
	}

	private static <LETTER, PLACE> HashRelation<PLACE, PLACE> computeCoRelatedPlacesRelation(
			final Set<Condition<LETTER, PLACE>> conditions, final ICoRelation<LETTER, PLACE> coRelation) {
		final HashRelation<PLACE, PLACE> result = new HashRelation<>();
		for (final Condition<LETTER, PLACE> condition : conditions) {
			for (final Condition<LETTER, PLACE> coRelated : coRelation.computeCoRelatatedConditions(condition)) {
				result.addPair(condition.getPlace(), coRelated.getPlace());
			}
		}
		return result;
	}


	@Override
	public boolean isEmpy() {
		return mPe.isEmpty() && mFastpathCutoffEventList.isEmpty();
	}

	@Override
	public int size() {
		return mPe.size() + mFastpathCutoffEventList.size();
	}

	@Override
	public int getUsefulExtensionCandidates() {
		return mUsefulExtensionCandidates;
	}

	@Override
	public int getUselessExtensionCandidates() {
		return mUselessExtensionCandidates;
	}

	@Override
	public int getMaximalSize() {
		return mMaximalSize;
	}




}
