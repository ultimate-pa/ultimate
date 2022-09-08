package de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class RabinBuchiDifference<LETTER, PLACE>
		extends GeneralOperation<LETTER, PLACE, IPetriNet2FiniteAutomatonStateFactory<PLACE>> {

	private final IPetriNet<LETTER, PLACE> mPetriNet;
	private final INestedWordAutomaton<LETTER, PLACE> mBuchiAutomata;

	private final Set<PLACE> mFinitePlaces;

	private final BoundedPetriNet<LETTER, PLACE> mDifferenceNet;

	public RabinBuchiDifference(final IPetriNet<LETTER, PLACE> petriNet,
			final INestedWordAutomaton<LETTER, PLACE> buchiAutomata, final AutomataLibraryServices services) {
		super(services);
		mPetriNet = petriNet;
		mBuchiAutomata = buchiAutomata;
		mFinitePlaces = (Set<PLACE>) mBuchiAutomata.getFinalStates();
		if (buchiAutomata.getInitialStates().size() != 1) {
			throw new IllegalArgumentException("Buchi with multiple initial states not supported.");
		}
		mDifferenceNet = new BoundedPetriNet<>(services, petriNet.getAlphabet(), false);
		constructIntersectionNet();
	}

	@Override
	public IPetriNet<LETTER, PLACE> getResult() {
		return mDifferenceNet;
	}

	public Set<PLACE> getFinitePlaces() {
		return mFinitePlaces;
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
			mDifferenceNet.addPlace(place, mPetriNet.getInitialPlaces().contains(place), false);
		}
	}

	private final void addOriginalBuchiPlaces() {
		for (final PLACE place : mBuchiAutomata.getStates()) {
			mDifferenceNet.addPlace(place, mBuchiAutomata.isInitial(place), false);
		}
	}

	private final void addTransitionsToIntersectionNet() {
		final Set<Transition<LETTER, PLACE>> pairedTransitions = new HashSet<>();
		for (final Transition<LETTER, PLACE> petriTransition : mPetriNet.getTransitions()) {
			for (final PLACE buchiPlace : mBuchiAutomata.getStates()) {
				for (final OutgoingInternalTransition<LETTER, PLACE> buchiTransition : mBuchiAutomata
						.internalSuccessors(buchiPlace, petriTransition.getSymbol())) {
					addNewTransition(petriTransition, buchiTransition, buchiPlace);
					pairedTransitions.add(petriTransition);
				}
			}
		}
		for (final Transition<LETTER, PLACE> petriTransition : mPetriNet.getTransitions()) {
			if (!pairedTransitions.contains(petriTransition)) {
				mDifferenceNet.addTransition(petriTransition.getSymbol(), petriTransition.getPredecessors(),
						petriTransition.getSuccessors());
			}
		}
	}

	private final void addNewTransition(final Transition<LETTER, PLACE> petriTransition,
			final OutgoingInternalTransition<LETTER, PLACE> buchiTransition, final PLACE buchiPredecessor) {
		final Set<PLACE> predecessorSet = getTransitionPredecessors(petriTransition, buchiPredecessor);
		final Set<PLACE> successorSet = getTransitionSuccessors(petriTransition, buchiTransition);
		mDifferenceNet.addTransition(petriTransition.getSymbol(), ImmutableSet.of(predecessorSet),
				ImmutableSet.of(successorSet));
	}

	private final Set<PLACE> getTransitionPredecessors(final Transition<LETTER, PLACE> petriTransition,
			final PLACE buchiPredecessor) {
		final Set<PLACE> predecessorSet = new HashSet<>(petriTransition.getPredecessors());

		predecessorSet.add(buchiPredecessor);

		return predecessorSet;
	}

	private final Set<PLACE> getTransitionSuccessors(final Transition<LETTER, PLACE> petriTransition,
			final OutgoingInternalTransition<LETTER, PLACE> buchiTransition) {
		final Set<PLACE> successorSet = new HashSet<>(petriTransition.getSuccessors());
		successorSet.add(buchiTransition.getSucc());

		return successorSet;
	}
}
