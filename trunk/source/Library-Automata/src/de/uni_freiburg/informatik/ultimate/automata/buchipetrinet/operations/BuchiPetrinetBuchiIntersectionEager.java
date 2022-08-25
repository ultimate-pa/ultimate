package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class BuchiPetrinetBuchiIntersectionEager<LETTER, PLACE>
		extends GeneralOperation<LETTER, PLACE, IPetriNet2FiniteAutomatonStateFactory<PLACE>> {

	private final IPetriNet<LETTER, PLACE> mPetriNet;
	private final INestedWordAutomaton<LETTER, PLACE> mBuchiAutomata;

	private final IBlackWhiteStateFactory<PLACE> mLabeledBuchiPlaceFactory;

	private final Map<PLACE, PLACE> mInputQGetQ1 = new HashMap<>();
	private final Map<PLACE, PLACE> mInputQGetQ2 = new HashMap<>();
	private final Map<PLACE, PLACE> mInputQ2GetQ = new HashMap<>();

	private final BoundedPetriNet<LETTER, PLACE> mIntersectionNet;

	public BuchiPetrinetBuchiIntersectionEager(final IPetriNet<LETTER, PLACE> petriNet,
			final INestedWordAutomaton<LETTER, PLACE> buchiAutomata, final IBlackWhiteStateFactory<PLACE> factory,
			final AutomataLibraryServices services) {
		super(services);
		mPetriNet = petriNet;
		mBuchiAutomata = buchiAutomata;
		if (buchiAutomata.getInitialStates().size() != 1) {
			throw new IllegalArgumentException("Buchi with multiple initial states not supported.");
		}
		mLabeledBuchiPlaceFactory = factory;
		mIntersectionNet = new BoundedPetriNet<>(services, petriNet.getAlphabet(), false);
		constructIntersectionNet();
	}

	private final void constructIntersectionNet() {
		addPlacesToIntersectionNet();
		addTransitionsToIntersectionNet();
	}

	private final void addPlacesToIntersectionNet() {
		addOriginalPetriPlaces();
		addOriginalBuchiPlaces();
	}

	private final void addOriginalPetriPlaces() {
		for (final PLACE place : mPetriNet.getPlaces()) {
			mIntersectionNet.addPlace(place, mPetriNet.getInitialPlaces().contains(place), false);
		}
	}

	private final void addOriginalBuchiPlaces() {
		for (final PLACE place : mBuchiAutomata.getStates()) {
			final PLACE stateOnePlace = mLabeledBuchiPlaceFactory.getWhiteContent(place);
			final PLACE stateTwoPlace = mLabeledBuchiPlaceFactory.getBlackContent(place);
			mIntersectionNet.addPlace(stateOnePlace, mBuchiAutomata.isInitial(place), false);
			mIntersectionNet.addPlace(stateTwoPlace, false, mBuchiAutomata.isFinal(place));
			mInputQGetQ1.put(place, stateOnePlace);
			mInputQGetQ2.put(place, stateTwoPlace);
			mInputQ2GetQ.put(stateTwoPlace, place);
		}
	}

	private final void addTransitionsToIntersectionNet() {
		for (final Transition<LETTER, PLACE> petriTransition : mPetriNet.getTransitions()) {
			for (final PLACE buchiPlace : mBuchiAutomata.getStates()) {
				for (final OutgoingInternalTransition<LETTER, PLACE> buchiTransition : mBuchiAutomata
						.internalSuccessors(buchiPlace, petriTransition.getSymbol())) {
					addStateOneAndTwoTransition(petriTransition, buchiTransition, buchiPlace);
				}
			}
		}
	}

	private final void addStateOneAndTwoTransition(final Transition<LETTER, PLACE> petriTransition,
			final OutgoingInternalTransition<LETTER, PLACE> buchiTransition, final PLACE buchiPredecessor) {
		Set<PLACE> predecessorSet = getTransitionPredecessors(petriTransition, buchiPredecessor, true);
		Set<PLACE> successorSet = getTransitionSuccessors(petriTransition, buchiTransition, predecessorSet, true);
		mIntersectionNet.addTransition(petriTransition.getSymbol(), ImmutableSet.of(predecessorSet),
				ImmutableSet.of(successorSet));
		predecessorSet = getTransitionPredecessors(petriTransition, buchiPredecessor, false);
		successorSet = getTransitionSuccessors(petriTransition, buchiTransition, predecessorSet, false);
		mIntersectionNet.addTransition(petriTransition.getSymbol(), ImmutableSet.of(predecessorSet),
				ImmutableSet.of(successorSet));
	}

	private final Set<PLACE> getTransitionPredecessors(final Transition<LETTER, PLACE> petriTransition,
			final PLACE buchiPredecessor, final boolean mBuildingStateOneTransition) {
		final Set<PLACE> predecessorSet = new HashSet<>(petriTransition.getPredecessors());

		if (mBuildingStateOneTransition) {
			predecessorSet.add(mInputQGetQ1.get(buchiPredecessor));
		} else {
			predecessorSet.add(mInputQGetQ2.get(buchiPredecessor));
		}

		return predecessorSet;
	}

	private final Set<PLACE> getTransitionSuccessors(final Transition<LETTER, PLACE> petriTransition,
			final OutgoingInternalTransition<LETTER, PLACE> buchiTransition, final Set<PLACE> predecessorSet,
			final boolean mBuildingStateOneTransition) {
		final Set<PLACE> successorSet = new HashSet<>(petriTransition.getSuccessors());
		if (mBuildingStateOneTransition) {
			successorSet.add(getQSuccesorForStateOneTransition(petriTransition, buchiTransition));
		} else {
			successorSet.add(getQSuccesorForStateTwoTransition(predecessorSet, buchiTransition));
		}

		return successorSet;
	}

	private PLACE getQSuccesorForStateOneTransition(final Transition<LETTER, PLACE> petriTransition,
			final OutgoingInternalTransition<LETTER, PLACE> buchiTransition) {
		for (final PLACE place : petriTransition.getSuccessors()) {
			if (mPetriNet.getAcceptingPlaces().contains(place)) {
				return mInputQGetQ2.get(buchiTransition.getSucc());
			}
		}
		return mInputQGetQ1.get(buchiTransition.getSucc());
	}

	private PLACE getQSuccesorForStateTwoTransition(final Set<PLACE> predecessorSet,
			final OutgoingInternalTransition<LETTER, PLACE> buchiTransition) {
		for (final PLACE place : predecessorSet) {
			if (mInputQ2GetQ.containsKey(place) && mBuchiAutomata.getFinalStates().contains(mInputQ2GetQ.get(place))) {
				return mInputQGetQ1.get(buchiTransition.getSucc());
			}
		}
		return mInputQGetQ2.get(buchiTransition.getSucc());
	}

	@Override
	public IPetriNet<LETTER, PLACE> getResult() {
		return mIntersectionNet;
	}
}
