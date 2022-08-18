package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.ISuccessorTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

// Generaloperatin
public class BuchiPetrinetBuchiIntersectionEager<LETTER, PLACE> implements IPetriNetSuccessorProvider<LETTER, PLACE> {

	// TODO : make class safe, check for double initial place in buchi for example, .. excepetion
	// und für 0
	private final IPetriNet<LETTER, PLACE> mPetriNet;
	private final INestedWordAutomaton<LETTER, PLACE> mBuchiAutomata;

	private final IBlackWhiteStateFactory<PLACE> mLabeledBuchiPlaceFactory;

	private final Map<PLACE, PLACE> mInputQGetQ1 = new HashMap<>();
	private final Map<PLACE, PLACE> mInputQGetQ2 = new HashMap<>();
	private final Map<PLACE, PLACE> mInputQ2GetQ = new HashMap<>();

	/*
	 * Helper variable to avoid duplicate code during Transition creation in addTransitionsToIntersectionNet().
	 */
	private boolean mBuildingStateOneTransition = true;

	private BoundedPetriNet<LETTER, PLACE> mIntersectionNet;

	public BuchiPetrinetBuchiIntersectionEager(IPetriNet<LETTER, PLACE> petriNet,
			INestedWordAutomaton<LETTER, PLACE> buchiAutomata, IBlackWhiteStateFactory<PLACE> factory,
			final AutomataLibraryServices services) {
		mPetriNet = petriNet;
		mBuchiAutomata = buchiAutomata;
		mLabeledBuchiPlaceFactory = factory;
		mIntersectionNet = new BoundedPetriNet<>(services, petriNet.getAlphabet(), false);
		constructIntersectionNet();
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mPetriNet.getAlphabet();
	}

	@Override
	public int size() {
		int flowRealtionSize = 0;
		for (final Transition<LETTER, PLACE> transition : mIntersectionNet.getTransitions()) {
			flowRealtionSize += transition.getPredecessors().toArray().length;
			flowRealtionSize += transition.getSuccessors().toArray().length;
		}
		return flowRealtionSize;
	}

	@Override
	public String sizeInformation() {
		return "There are" + size() + "elements in flow relation, with " + mIntersectionNet.getPlaces().toArray().length
				+ " places and " + mIntersectionNet.getTransitions().toArray().length + " transitions.";
	}

	@Override
	public IElement transformToUltimateModel(AutomataLibraryServices services)
			throws AutomataOperationCanceledException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<PLACE> getInitialPlaces() {
		return mIntersectionNet.getInitialPlaces();
	}

	@Override
	public Set<Transition<LETTER, PLACE>> getSuccessors(PLACE place) {
		return mIntersectionNet.getSuccessors(place);
	}

	@Override
	public Set<Transition<LETTER, PLACE>> getPredecessors(PLACE place) {
		return mIntersectionNet.getPredecessors(place);
	}

	@Override
	public Collection<ISuccessorTransitionProvider<LETTER, PLACE>>
			getSuccessorTransitionProviders(Set<PLACE> mustPlaces, Set<PLACE> mayPlaces) {
		return mIntersectionNet.getSuccessorTransitionProviders(mustPlaces, mayPlaces);
	}

	/*
	 * Markings of Buchipetrinets can't be accepting as the acceptance condition is defined with the firing of
	 * transitions instead.
	 */
	@Override
	public boolean isAccepting(Marking<LETTER, PLACE> marking) {
		return false;
	}

	@Override
	public boolean isAccepting(PLACE place) {
		return mIntersectionNet.isAccepting(place);
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
		for (PLACE place : mPetriNet.getPlaces()) {
			mIntersectionNet.addPlace(place, mPetriNet.getInitialPlaces().contains(place), false);
		}
	}

	private final void addOriginalBuchiPlaces() {
		for (PLACE place : mBuchiAutomata.getStates()) {
			PLACE stateOnePlace = mLabeledBuchiPlaceFactory.getWhiteContent(place);
			PLACE stateTwoPlace = mLabeledBuchiPlaceFactory.getBlackContent(place);
			mIntersectionNet.addPlace(stateOnePlace, mBuchiAutomata.isInitial(place), false);
			mIntersectionNet.addPlace(stateTwoPlace, false, mBuchiAutomata.isFinal(place));
			mInputQGetQ1.put(place, stateOnePlace);
			mInputQGetQ2.put(place, stateTwoPlace);
			mInputQ2GetQ.put(stateTwoPlace, place);
		}
	}

	private final void addTransitionsToIntersectionNet() {
		for (Transition<LETTER, PLACE> petriTransition : mPetriNet.getTransitions()) {
			for (PLACE buchiPlace : mBuchiAutomata.getStates()) {
				for (OutgoingInternalTransition<LETTER, PLACE> buchiTransition : mBuchiAutomata
						.internalSuccessors(buchiPlace, petriTransition.getSymbol())) {
					addStateOneAndTwoTransition(petriTransition, buchiTransition, buchiPlace);
				}
			}
		}
	}

	private final void addStateOneAndTwoTransition(Transition<LETTER, PLACE> petriTransition,
			OutgoingInternalTransition<LETTER, PLACE> buchiTransition, PLACE buchiPredecessor) {
		mBuildingStateOneTransition = true;
		Set<PLACE> predecessorSet = getTransitionPredecessors(petriTransition, buchiPredecessor);
		Set<PLACE> successorSet = getTransitionSuccessors(petriTransition, buchiTransition, predecessorSet);
		mIntersectionNet.addTransition(petriTransition.getSymbol(), ImmutableSet.of(predecessorSet),
				ImmutableSet.of(successorSet));
		mBuildingStateOneTransition = false;
		predecessorSet = getTransitionPredecessors(petriTransition, buchiPredecessor);
		successorSet = getTransitionSuccessors(petriTransition, buchiTransition, predecessorSet);
		mIntersectionNet.addTransition(petriTransition.getSymbol(), ImmutableSet.of(predecessorSet),
				ImmutableSet.of(successorSet));
	}

	// booplean argument
	private final Set<PLACE> getTransitionPredecessors(Transition<LETTER, PLACE> petriTransition,
			PLACE buchiPredecessor) {
		Set<PLACE> predecessorSet = new HashSet<>(petriTransition.getPredecessors());

		if (mBuildingStateOneTransition) {
			predecessorSet.add(mInputQGetQ1.get(buchiPredecessor));
		} else {
			predecessorSet.add(mInputQGetQ2.get(buchiPredecessor));
		}

		return predecessorSet;
	}

	private final Set<PLACE> getTransitionSuccessors(Transition<LETTER, PLACE> petriTransition,
			OutgoingInternalTransition<LETTER, PLACE> buchiTransition, Set<PLACE> predecessorSet) {
		Set<PLACE> successorSet = new HashSet<>(petriTransition.getSuccessors());
		if (mBuildingStateOneTransition) {
			successorSet.add(getQSuccesorForStateOneTransition(petriTransition, buchiTransition));
		} else {
			successorSet.add(getQSuccesorForStateTwoTransition(predecessorSet, buchiTransition));
		}

		return successorSet;
	}

	private PLACE getQSuccesorForStateOneTransition(Transition<LETTER, PLACE> petriTransition,
			OutgoingInternalTransition<LETTER, PLACE> buchiTransition) {
		for (PLACE place : petriTransition.getSuccessors()) {
			if (mPetriNet.getAcceptingPlaces().contains(place)) {
				return mInputQGetQ2.get(buchiTransition.getSucc());
			}
		}
		return mInputQGetQ1.get(buchiTransition.getSucc());
	}

	private PLACE getQSuccesorForStateTwoTransition(Set<PLACE> predecessorSet,
			OutgoingInternalTransition<LETTER, PLACE> buchiTransition) {
		for (PLACE place : predecessorSet) {
			if (mInputQ2GetQ.containsKey(place) && mBuchiAutomata.getFinalStates().contains(mInputQ2GetQ.get(place))) {
				return mInputQGetQ1.get(buchiTransition.getSucc());
			}
		}
		return mInputQGetQ2.get(buchiTransition.getSucc());
	}
}
