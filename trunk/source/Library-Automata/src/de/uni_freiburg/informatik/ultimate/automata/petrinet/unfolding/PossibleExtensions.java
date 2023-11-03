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
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.ISuccessorTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.SimpleSuccessorTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
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
	 * Use the optimization that is outlined in observation B07 in the following issue.
	 * https://github.com/ultimate-pa/ultimate/issues/448
	 */
	private static final boolean USE_FORWARD_CHECKING = false;
	private static final boolean USE_PQ = true;
	private final static boolean LAZY_SUCCESSOR_COMPUTATION = true;

	private final Queue<Event<LETTER, PLACE>> mPe;
	private final Map<Marking<PLACE>, Event<LETTER, PLACE>> mMarkingEventMap = new HashMap<>();
	private int mMaximalSize;
	private final boolean mUseFirstbornCutoffCheck;
	private final boolean mUseB32Optimization;
	private int mNumberOfGeneratedExtensions = 0;
	/**
	 * If {@link Event} is known to be cut-off event we can move it immediately to front because it will not create
	 * descendants. This optimization keeps the queue smaller. TODO 2019-10-16 Matthias: Mehdi found out that this
	 * ArrayDeque is currently unused because the cut-off detection is only done later. We could to an additional
	 * cut-off check earlier but we have doubts that this will pay off.
	 */
	private final Comparator<Event<LETTER, PLACE>> mOrder;
	private final ArrayDeque<Event<LETTER, PLACE>> mFastpathCutoffEventList;
	private final BranchingProcess<LETTER, PLACE> mBranchingProcess;

	/**
	 * A candidate is useful if it lead to at least one new possible extension.
	 */
	private int mUsefulExtensionCandidates;
	private int mUselessExtensionCandidates;

	public PossibleExtensions(final BranchingProcess<LETTER, PLACE> branchingProcess,
			final ConfigurationOrder<LETTER, PLACE> order, final boolean useFirstbornCutoffCheck,
			final boolean useB32Optimization) {
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
		mUseB32Optimization = useB32Optimization;
	}

	@Override
	public Event<LETTER, PLACE> remove() {
		if (mFastpathCutoffEventList.isEmpty()) {
			return mPe.remove();
		}
		return mFastpathCutoffEventList.removeFirst();
	}

	@Override
	public void update(final Event<LETTER, PLACE> event) throws PetriNetNot1SafeException {
		final Collection<Candidate<LETTER, PLACE>> candidates = computeCandidates(event);
		for (final Candidate<LETTER, PLACE> candidate : candidates) {
			if (candidate.getInstantiated().isEmpty()) {
				throw new AssertionError("at least one place has to be instantiated");
			}
			final int possibleExtensionsBefore = size();
			if (USE_FORWARD_CHECKING) {
				evolveCandidateWithForwardChecking(candidate);
			} else {
				evolveCandidate(candidate);
			}
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
		}
		final boolean eventWithSameMarkingWasInTheMainQueu = mPe.remove(eventWithSameMarking);
		assert eventWithSameMarkingWasInTheMainQueu;
		mFastpathCutoffEventList.add(eventWithSameMarking);
		eventWithSameMarking.setCompanion(newEvent);
		return false;
	}

	/**
	 * Evolves a {@code Candidate} for a new possible Event in all possible ways and, as a side-effect, adds valid
	 * extensions (ones whose predecessors are a co-set) to he possible extension set.
	 */

	private void addFullyInstantiatedCandidate(final Candidate<LETTER, PLACE> cand) throws PetriNetNot1SafeException {
		for (final Transition<LETTER, PLACE> trans : cand.getTransition().getTransitions()) {
			mNumberOfGeneratedExtensions++;
			final Event<LETTER, PLACE> newEvent =
					new Event<>(cand.getInstantiated(), trans, mBranchingProcess, mNumberOfGeneratedExtensions);
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
	}

	private void evolveCandidate(final Candidate<LETTER, PLACE> cand) throws PetriNetNot1SafeException {
		if (cand.isFullyInstantiated()) {
			addFullyInstantiatedCandidate(cand);
			return;
		}
		final PLACE nextUninstantiated = cand.getNextUninstantiatedPlace();
		final ICoRelation<LETTER, PLACE> coRelation = mBranchingProcess.getCoRelation();
		final List<Condition<LETTER, PLACE>> yetInstantiated = cand.getInstantiatedButNotInitially();
		final Set<Condition<LETTER, PLACE>> inCoRelationWithAllInstantiated =
				cand.getPossibleInstantiations(nextUninstantiated).stream()
						.filter(x -> coRelation.isCoset(yetInstantiated, x)).collect(Collectors.toSet());
		for (final Condition<LETTER, PLACE> c : inCoRelationWithAllInstantiated) {
			assert cand.getTransition().getPredecessorPlaces().contains(c.getPlace());
			// equality intended here
			assert c.getPlace().equals(nextUninstantiated);
			assert !cand.getInstantiated().contains(c);
			cand.instantiateNext(c);
			evolveCandidate(cand);
			cand.undoOneInstantiation();
		}
	}

	private void evolveCandidateWithForwardChecking(final Candidate<LETTER, PLACE> cand)
			throws PetriNetNot1SafeException {
		if (cand.isFullyInstantiated()) {
			addFullyInstantiatedCandidate(cand);
			return;
		}
		final PLACE nextUninstantiated = cand.getNextUninstantiatedPlace();
		final ICoRelation<LETTER, PLACE> coRelation = mBranchingProcess.getCoRelation();
		final Map<PLACE, Set<Condition<LETTER, PLACE>>> possibleInstantiationsMap = cand.getPossibleInstantiationsMap();
		final Set<Condition<LETTER, PLACE>> possibleInstantiations = cand.getPossibleInstantiations(nextUninstantiated);
		possibleInstantiationsMap.remove(nextUninstantiated);
		for (final Condition<LETTER, PLACE> condition : possibleInstantiations) {
			final Map<PLACE, Set<Condition<LETTER, PLACE>>> newPossibleInstantiations = new HashMap<>();
			boolean uselessCandidate = false;
			for (final PLACE p : possibleInstantiationsMap.keySet()) {
				final Set<Condition<LETTER, PLACE>> possibleInstantiationsforP = possibleInstantiationsMap.get(p)
						.stream().filter(x -> coRelation.isInCoRelation(condition, x)).collect(Collectors.toSet());
				if (possibleInstantiationsforP.isEmpty()) {
					uselessCandidate = true;
					break;
				}
				newPossibleInstantiations.put(p, possibleInstantiationsforP);
			}
			if (!uselessCandidate) {
				final LinkedList<Condition<LETTER, PLACE>> newInstantiated = new LinkedList<>(cand.getInstantiated());
				newInstantiated.add(condition);
				final LinkedList<PLACE> newNotInstantiated = new LinkedList<>(cand.getNotInstantiated());
				newNotInstantiated.removeLast();
				evolveCandidateWithForwardChecking(new Candidate<>(cand.getTransition(), newNotInstantiated,
						newInstantiated, newPossibleInstantiations));
			}
		}
	}

	/**
	 * @return All {@code Candidate}s for possible extensions that are successors of the {@code Event}.
	 */
	private Collection<Candidate<LETTER, PLACE>> computeCandidates(final Event<LETTER, PLACE> event) {
		if (event.getSuccessorConditions().isEmpty()) {
			return Collections.emptySet();
		}
		if (LAZY_SUCCESSOR_COMPUTATION) {
			final Set<Condition<LETTER, PLACE>> newConditions = event.getSuccessorConditions();
			final ICoRelation<LETTER, PLACE> coRelation = mBranchingProcess.getCoRelation();
			final Set<Condition<LETTER, PLACE>> coRelatedConditions;
			final HashRelation<PLACE, Condition<LETTER, PLACE>> place2coRelatedConditions = new HashRelation<>();
			if (mUseB32Optimization) {
				coRelatedConditions = coRelation.computeNonCutoffCoRelatatedConditions(newConditions.iterator().next());
				for (final Condition<LETTER, PLACE> c : coRelatedConditions) {
					place2coRelatedConditions.addPair(c.getPlace(), c);
				}
			} else {
				coRelatedConditions = coRelation.computeCoRelatatedConditions(newConditions.iterator().next());
				for (final Condition<LETTER, PLACE> c : coRelatedConditions) {
					if (!c.getPredecessorEvent().isCutoffEvent()) {
						place2coRelatedConditions.addPair(c.getPlace(), c);
					}
				}
			}
			final Collection<ISuccessorTransitionProvider<LETTER, PLACE>> successorTransitionProviders;

			final Set<PLACE> placesOfNewConditions = new HashSet<>();
			for (final Condition<LETTER, PLACE> c : newConditions) {
				placesOfNewConditions.add(c.getPlace());
			}
			successorTransitionProviders = mBranchingProcess.getNet()
					.getSuccessorTransitionProviders(placesOfNewConditions, place2coRelatedConditions.getDomain());

			final List<Candidate<LETTER, PLACE>> candidates = successorTransitionProviders.stream()
					.map(x -> new Candidate<>(x, newConditions, place2coRelatedConditions))
					.collect(Collectors.toList());
			return candidates;
		}
		if (!(mBranchingProcess.getNet() instanceof IPetriNetTransitionProvider)) {
			throw new AssertionError("non-lazy computation only available for fully constructed nets");
		}
		final IPetriNetTransitionProvider<LETTER, PLACE> fullPetriNet =
				(IPetriNetTransitionProvider<LETTER, PLACE>) mBranchingProcess.getNet();
		final Set<Transition<LETTER, PLACE>> transitions = new HashSet<>();
		for (final Condition<LETTER, PLACE> cond : event.getSuccessorConditions()) {
			for (final Transition<LETTER, PLACE> t : fullPetriNet.getSuccessors(cond.getPlace())) {
				transitions.add(t);
			}
		}
		final List<Candidate<LETTER, PLACE>> candidates = new ArrayList<>();
		for (final Transition<LETTER, PLACE> transition : transitions) {
			final Candidate<LETTER, PLACE> candidate =
					new Candidate<>(new SimpleSuccessorTransitionProvider<>(Collections.singleton(transition)),
							event.getSuccessorConditions(), null);
			candidates.add(candidate);
		}
		return candidates;
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
