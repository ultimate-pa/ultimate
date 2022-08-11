package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.ISuccessorTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

public class BuchiPetrinetBuchiIntersection<LETTER, PLACE> implements IPetriNetSuccessorProvider<LETTER, PLACE> {

	private final IPetriNetSuccessorProvider<LETTER, PLACE> mPetriNet;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> mBuchiAutomata;

	private final IBlackWhiteStateFactory<PLACE> mBuchiPlaceFactory;

	private final NestedMap2<Transition<LETTER, PLACE>, OutgoingInternalTransition<LETTER, PLACE>, Transition<LETTER, PLACE>> mStateOneTransitions =
			new NestedMap2<>();

	private final NestedMap2<Transition<LETTER, PLACE>, OutgoingInternalTransition<LETTER, PLACE>, Transition<LETTER, PLACE>> mStateTwoTransitions =
			new NestedMap2<>();

	/*
	 * original places are keys, labeled q places are values
	 */
	private final Map<PLACE, PLACE> mInputQGetQ1 = new HashMap<>();
	/*
	 * original places are keys, labeled q places are values
	 */
	private final Map<PLACE, PLACE> mInputQGetQ2 = new HashMap<>();

	/*
	 * original places are values, labeled q places are keys
	 */
	private final Map<PLACE, PLACE> mInputQ1GetQ = new HashMap<>();
	/*
	 * original places are keys, labeled q places are Keys
	 */
	private final Map<PLACE, PLACE> mInputQ2GetQ = new HashMap<>();

	// TODO: do this some other way, also we are creating duplicates this is wrong
	private final Map<Transition<LETTER, PLACE>, Transition<LETTER, PLACE>> mTransitions = new HashMap<>();
	/*
	 * Either constantly ADD to these, or constantly keep them up to date, i.e. in line with a marking or multiple
	 * possible markings.. ?
	 *
	 */
	private final Set<PLACE> mCurrentlyRelevantPurePetriPlaces = new HashSet<>();
	private final Set<PLACE> mCurrentlyRelevantLabeledBuchiPlaces = new HashSet<>();
	// probably cant know that only one Qplace is relevant... but would make it easy
	// private PLACE mCurrentlyRelevantLabeledBuchiPlace;

	private final int mNextTransitionId = 0;

	// TODO call this clas slazy, and maybe make new one with ipetrinet..
	public BuchiPetrinetBuchiIntersection(final IPetriNetSuccessorProvider<LETTER, PLACE> petriNet,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> automaton,
			final IBlackWhiteStateFactory<PLACE> factory) {
		mPetriNet = petriNet;
		mBuchiAutomata = automaton;
		mBuchiPlaceFactory = factory;
	}

	/*
	 * mPetriNet and mBuchiAutomata must have same alphabet.
	 */
	@Override
	public Set<LETTER> getAlphabet() {
		return mPetriNet.getAlphabet();
	}

	@Override
	public int size() {
		int flowRealtionSize = 0;
		for (final Transition<LETTER, PLACE> transition : mTransitions.values()) {
			flowRealtionSize += transition.getPredecessors().toArray().length;
			flowRealtionSize += transition.getSuccessors().toArray().length;
		}
		return flowRealtionSize;
	}

	@Override
	public String sizeInformation() {
		return "" + size() + "relations in flow relation.";
	}

	@Override
	public IElement transformToUltimateModel(final AutomataLibraryServices services)
			throws AutomataOperationCanceledException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<PLACE> getInitialPlaces() {
		final Set<PLACE> initialPlaces = new HashSet<>();
		initialPlaces.addAll(mPetriNet.getInitialPlaces());
		mCurrentlyRelevantPurePetriPlaces.addAll(mPetriNet.getInitialPlaces());
		// exception for more than one initial state
		final PLACE qInitialPlace = createOrGetLabelOneQPlace(mBuchiAutomata.getInitialStates().iterator().next());
		initialPlaces.add(qInitialPlace);
		return initialPlaces;
	}

	@Override
	public ImmutableSet<PLACE> getSuccessors(final Transition<LETTER, PLACE> transition) {
		final Transition<LETTER, PLACE> casted = mTransitions.get(transition);
		if (casted == null) {
			throw new IllegalArgumentException("unknown transition " + transition);
		}
		return casted.getSuccessors();
	}

	@Override
	public ImmutableSet<PLACE> getPredecessors(final Transition<LETTER, PLACE> transition) {
		final Transition<LETTER, PLACE> casted = mTransitions.get(transition);
		if (casted == null) {
			throw new IllegalArgumentException("unknown transition " + transition);
		}
		return casted.getPredecessors();
	}

	/*
	 * Schaue ob die places in den input automaten existieren, nicht hier
	 */
	@Override
	public Set<Transition<LETTER, PLACE>> getSuccessors(final PLACE place) {
		if (mCurrentlyRelevantLabeledBuchiPlaces.contains(place)) {
			return getBuchiPlaceSuccessors(place);
		} else if (mCurrentlyRelevantPurePetriPlaces.contains(place)) {
			return getPetriPlaceSuccessors(place);
		} else {
			throw new IllegalArgumentException("Place doesn't exist: " + place);
		}
	}

	private final Set<Transition<LETTER, PLACE>> getBuchiPlaceSuccessors(final PLACE place) {
		if (mInputQ1GetQ.containsKey(place)) {
			return getBuchiStateOnePlaceSuccessors(place);
		} else if (mInputQ2GetQ.containsKey(place)) {
			return getBuchiStateTwoPlaceSuccessors(place);
		} else {
			throw new IllegalArgumentException("place in limbo :" + place);
		}
	}

	// methoden vereinigen
	private final Set<Transition<LETTER, PLACE>> getBuchiStateOnePlaceSuccessors(final PLACE place) {
		final Set<Transition<LETTER, PLACE>> successorTransitions = new HashSet<>();
		for (final OutgoingInternalTransition<LETTER, PLACE> transition : mBuchiAutomata
				.internalSuccessors(mInputQ1GetQ.get(place))) {
			final Set<PLACE> relevantPetriPlaces = new HashSet<>();
			relevantPetriPlaces.addAll(mCurrentlyRelevantPurePetriPlaces);
			for (final PLACE pPlace : relevantPetriPlaces) {
				for (final Transition<LETTER, PLACE> pTransition : mPetriNet.getSuccessors(pPlace)) {
					if (transition.getLetter() == pTransition.getSymbol()) {
						successorTransitions
								.add(createOrGetLabelOneTransition(pTransition, transition, mInputQ1GetQ.get(place)));
					}
				}
			}
		}
		return successorTransitions;
	}

	private final Set<Transition<LETTER, PLACE>> getBuchiStateTwoPlaceSuccessors(final PLACE place) {
		final Set<Transition<LETTER, PLACE>> successorTransitions = new HashSet<>();
		for (final OutgoingInternalTransition<LETTER, PLACE> transition : mBuchiAutomata
				.internalSuccessors(mInputQ2GetQ.get(place))) {
			final Set<PLACE> relevantPetriPlaces = new HashSet<>();
			relevantPetriPlaces.addAll(mCurrentlyRelevantPurePetriPlaces);
			for (final PLACE pPlace : relevantPetriPlaces) {
				for (final Transition<LETTER, PLACE> pTransition : mPetriNet.getSuccessors(pPlace)) {
					if (transition.getLetter() == pTransition.getSymbol()) {
						successorTransitions
								.add(createOrGetLabelTwoTransition(pTransition, transition, mInputQ2GetQ.get(place)));
					}
				}
			}
		}
		return successorTransitions;
	}

	private final Set<Transition<LETTER, PLACE>> getPetriPlaceSuccessors(final PLACE place) {
		final Set<Transition<LETTER, PLACE>> successorTransitions = new HashSet<>();
		for (final Transition<LETTER, PLACE> transition : mPetriNet.getSuccessors(place)) {
			final Set<PLACE> relevantLabeledQplaces = new HashSet<>();
			relevantLabeledQplaces.addAll(mCurrentlyRelevantLabeledBuchiPlaces);
			for (final PLACE qPlace : relevantLabeledQplaces) {
				PLACE originalQPlace;
				// TODO bidirection map
				if (mInputQ1GetQ.containsKey(qPlace)) {
					originalQPlace = mInputQ1GetQ.get(qPlace);
				} else if (mInputQ2GetQ.containsKey(qPlace)) {
					originalQPlace = mInputQ2GetQ.get(qPlace);
				} else {
					throw new IllegalArgumentException("place doesnt exist during getsuccessors");
				}
				for (final OutgoingInternalTransition<LETTER, PLACE> qTransition : mBuchiAutomata
						.internalSuccessors(originalQPlace)) {
					if (transition.getSymbol() == qTransition.getLetter()) {
						successorTransitions
								.add(createOrGetLabelOneTransition(transition, qTransition, originalQPlace));
						successorTransitions
								.add(createOrGetLabelTwoTransition(transition, qTransition, originalQPlace));
					}
				}
			}
		}
		return successorTransitions;
	}

	@Override
	public Set<Transition<LETTER, PLACE>> getPredecessors(final PLACE place) {
		final Set<Transition<LETTER, PLACE>> predecessorTransitions = new HashSet<>();
		for (final Transition<LETTER, PLACE> transition : mTransitions.values()) {
			if (transition.getSuccessors().contains(place)) {
				predecessorTransitions.add(transition);
			}
		}
		return predecessorTransitions;
	}

	@Override
	public Collection<ISuccessorTransitionProvider<LETTER, PLACE>>
			getSuccessorTransitionProviders(final HashRelation<PLACE, PLACE> place2allowedSiblings) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<ISuccessorTransitionProvider<LETTER, PLACE>>
			getSuccessorTransitionProviders(final Set<PLACE> mustPlaces, final Set<PLACE> mayPlaces) {
		// TODO Auto-generated method stub
		return null;
	}

	// We have no accepting markings in a BuchiPetriNet
	@Override
	public boolean isAccepting(final Marking<LETTER, PLACE> marking) {
		return false;
	}

	@Override
	public boolean isAccepting(final PLACE place) {
		return mInputQ2GetQ.containsKey(place) && mBuchiAutomata.isFinal(mInputQ2GetQ.get(place));
	}

	private PLACE createOrGetLabelOneQPlace(final PLACE place) {
		if (mInputQGetQ1.containsKey(place)) {
			return mInputQGetQ1.get(place);
		}
		final PLACE qOnePlace = mBuchiPlaceFactory.getWhiteContent(place);
		mInputQGetQ1.put(place, qOnePlace);
		mInputQ1GetQ.put(qOnePlace, place);
		mCurrentlyRelevantLabeledBuchiPlaces.add(qOnePlace);
		return qOnePlace;
	}

	private PLACE createOrGetLabelTwoQPlace(final PLACE place) {
		if (mInputQGetQ2.containsKey(place)) {
			return mInputQGetQ2.get(place);
		}
		final PLACE q2Place = mBuchiPlaceFactory.getBlackContent(place);
		mInputQGetQ2.put(place, q2Place);
		mInputQ2GetQ.put(q2Place, place);
		mCurrentlyRelevantLabeledBuchiPlaces.add(q2Place);
		return q2Place;
	}

	private Transition<LETTER, PLACE> createOrGetLabelOneTransition(final Transition<LETTER, PLACE> oldPetrTransition,
			final OutgoingInternalTransition<LETTER, PLACE> buchiAutomataTransition, final PLACE buchiPredecessor) {

		if (mStateOneTransitions.containsKey(oldPetrTransition)) {
			if (mStateOneTransitions.get(oldPetrTransition).containsKey(buchiAutomataTransition)) {
				return mStateOneTransitions.get(oldPetrTransition).get(buchiAutomataTransition);
			}
		}

		final Set<PLACE> allPredecessors = new HashSet<>();

		allPredecessors.addAll(mPetriNet.getPredecessors(oldPetrTransition));
		mCurrentlyRelevantPurePetriPlaces.addAll(mPetriNet.getPredecessors(oldPetrTransition));
		allPredecessors.add(createOrGetLabelOneQPlace(buchiPredecessor));

		final Set<PLACE> allSuccessors = getStateOneTransitionSuccessors(oldPetrTransition, buchiAutomataTransition);

		final Transition<LETTER, PLACE> newTransition = new Transition<>(oldPetrTransition.getSymbol(),
				ImmutableSet.of(allPredecessors), ImmutableSet.of(allSuccessors), mNextTransitionId);
		// mNextTransitionId++;

		mTransitions.put(newTransition, newTransition);
		mStateOneTransitions.put(oldPetrTransition, buchiAutomataTransition, newTransition);
		return newTransition;
	}

	private Transition<LETTER, PLACE> createOrGetLabelTwoTransition(final Transition<LETTER, PLACE> oldPetrTransition,
			final OutgoingInternalTransition<LETTER, PLACE> buchiAutomataTransition, final PLACE buchiPredecessor) {

		if (mStateOneTransitions.containsKey(oldPetrTransition)) {
			if (mStateOneTransitions.get(oldPetrTransition).containsKey(buchiAutomataTransition)) {
				return mStateOneTransitions.get(oldPetrTransition).get(buchiAutomataTransition);
			}
		}
		final Set<PLACE> allPredecessors = new HashSet<>();

		allPredecessors.addAll(mPetriNet.getPredecessors(oldPetrTransition));
		mCurrentlyRelevantPurePetriPlaces.addAll(mPetriNet.getPredecessors(oldPetrTransition));
		allPredecessors.add(createOrGetLabelTwoQPlace(buchiPredecessor));

		final Set<PLACE> allSuccessors =
				getStateTwoTransitionSuccessors(oldPetrTransition, buchiAutomataTransition, buchiPredecessor);

		final Transition<LETTER, PLACE> newTransition = new Transition<>(oldPetrTransition.getSymbol(),
				ImmutableSet.of(allPredecessors), ImmutableSet.of(allSuccessors), mNextTransitionId);
		// mNextTransitionId++;

		mTransitions.put(newTransition, newTransition);
		mStateTwoTransitions.put(oldPetrTransition, buchiAutomataTransition, newTransition);
		return newTransition;
	}

	Set<PLACE> getStateOneTransitionSuccessors(final Transition<LETTER, PLACE> oldPetrTransition,
			final OutgoingInternalTransition<LETTER, PLACE> buchiAutomataTransition) {
		final Set<PLACE> allSuccessors = new HashSet<>();

		boolean acceptingPetriSuccessor = false;
		for (final PLACE place : mPetriNet.getSuccessors(oldPetrTransition)) {
			if (mPetriNet.isAccepting(place)) {
				acceptingPetriSuccessor = true;
			}
		}

		if (acceptingPetriSuccessor) {
			allSuccessors.add(createOrGetLabelTwoQPlace(buchiAutomataTransition.getSucc()));
		} else {
			allSuccessors.add(createOrGetLabelOneQPlace(buchiAutomataTransition.getSucc()));
		}

		allSuccessors.addAll(mPetriNet.getSuccessors(oldPetrTransition));
		mCurrentlyRelevantPurePetriPlaces.addAll(mPetriNet.getSuccessors(oldPetrTransition));
		return allSuccessors;
	}

	Set<PLACE> getStateTwoTransitionSuccessors(final Transition<LETTER, PLACE> oldPetrTransition,
			final OutgoingInternalTransition<LETTER, PLACE> buchiAutomataTransition, final PLACE buchiPredecessor) {
		final Set<PLACE> allSuccessors = new HashSet<>();

		boolean acceptingBuchiPredecessor = false;
		if (mBuchiAutomata.isFinal(buchiPredecessor)) {
			acceptingBuchiPredecessor = true;
		}

		if (acceptingBuchiPredecessor) {
			allSuccessors.add(createOrGetLabelOneQPlace(buchiAutomataTransition.getSucc()));
		} else {
			allSuccessors.add(createOrGetLabelTwoQPlace(buchiAutomataTransition.getSucc()));
		}

		allSuccessors.addAll(mPetriNet.getSuccessors(oldPetrTransition));
		mCurrentlyRelevantPurePetriPlaces.addAll(mPetriNet.getSuccessors(oldPetrTransition));
		return allSuccessors;
	}
}
