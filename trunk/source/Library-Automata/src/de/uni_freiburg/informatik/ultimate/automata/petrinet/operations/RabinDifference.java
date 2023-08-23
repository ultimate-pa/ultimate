package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Eager difference of Rabin-Petri-net minuend and Buchi automata subtrahend. Buchi automata must be complete and
 * deterministic.
 *
 */
public class RabinDifference<LETTER, PLACE>
		extends GeneralOperation<LETTER, PLACE, IPetriNet2FiniteAutomatonStateFactory<PLACE>> {

	private final IRabinPetriNet<LETTER, PLACE> mPetriNet;
	private final INestedWordAutomaton<LETTER, PLACE> mBuchiAutomata;
	private final BoundedRabinPetriNet<LETTER, PLACE> mDifferenceNet;

	public RabinDifference(final AutomataLibraryServices services, final IRabinPetriNet<LETTER, PLACE> petriNet,
			final INestedWordAutomaton<LETTER, PLACE> buchiAutomata) throws AutomataLibraryException {
		super(services);
		mPetriNet = petriNet;
		mBuchiAutomata = buchiAutomata;
		if (buchiAutomata.getInitialStates().size() != 1) {
			throw new IllegalArgumentException("Buchi with multiple initial states not supported.");
		}
		mDifferenceNet = new BoundedRabinPetriNet<>(services, petriNet.getAlphabet(), false);
		for (final PLACE place : mBuchiAutomata.getFinalStates()) {
			mDifferenceNet.addFinitePlace(place);
		}
		constructIntersectionNet();
	}

	@Override
	public IRabinPetriNet<LETTER, PLACE> getResult() {
		return mDifferenceNet;
	}

	private final void constructIntersectionNet() throws AutomataLibraryException {
		addPlacesToIntersectionNet();
		addTransitionsToIntersectionNet();
	}

	private final void addPlacesToIntersectionNet() {
		addOriginalPetriPlaces();
		addOriginalBuchiPlaces();
	}

	private final void addOriginalPetriPlaces() {
		for (final PLACE place : mPetriNet.getPlaces()) {
			mDifferenceNet.addPlace(place, mPetriNet.getInitialPlaces().contains(place), mPetriNet.isAccepting(place));
		}
	}

	private final void addOriginalBuchiPlaces() {
		for (final PLACE place : mBuchiAutomata.getStates()) {
			mDifferenceNet.addPlace(place, mBuchiAutomata.isInitial(place), false);
			if (mBuchiAutomata.isFinal(place)) {
				mDifferenceNet.addFinitePlace(place);
			}
		}
	}

	private final void addTransitionsToIntersectionNet() throws AutomataLibraryException {
		final Set<Transition<LETTER, PLACE>> pairedTransitions = new HashSet<>();
		for (final Transition<LETTER, PLACE> petriTransition : mPetriNet.getTransitions()) {
			for (final PLACE buchiPlace : mBuchiAutomata.getStates()) {

				final Iterable<OutgoingInternalTransition<LETTER, PLACE>> successorCandidate =
						mBuchiAutomata.internalSuccessors(buchiPlace, petriTransition.getSymbol());

				final Iterator<OutgoingInternalTransition<LETTER, PLACE>> successorCandidateIterator =
						successorCandidate.iterator();
				OutgoingInternalTransition<LETTER, PLACE> buchiTransition;
				if (successorCandidateIterator.hasNext()) {
					buchiTransition = successorCandidateIterator.next();
					if (successorCandidateIterator.hasNext()) {
						throw new AutomataLibraryException(getClass(),
								"Nondeterministic buchi automaton can not be used in deterministic difference.\n"
										+ "There are multiple transitions for one state-letter pair.");
					}
				} else {
					throw new AutomataLibraryException(getClass(),
							"Not full buchi automaton can not be used in deterministic difference.\n"
									+ "There is no transition for one state-letter pair.");
				}

				addNewTransition(petriTransition, buchiTransition, buchiPlace);
				pairedTransitions.add(petriTransition);

			}
		}
		// This method causes the automaton to "sleep" for cases it has no transitions for a letter,
		// but we require it to be complete and deterministic
		/*
		 * for (final Transition<LETTER, PLACE> petriTransition : mPetriNet.getTransitions()) { if
		 * (!pairedTransitions.contains(petriTransition)) { mDifferenceNet.addTransition(petriTransition.getSymbol(),
		 * petriTransition.getPredecessors(), petriTransition.getSuccessors()); } }
		 */
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

	@Override
	public boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<PLACE> stateFactory)
			throws AutomataLibraryException {
		return true; // TODO: implement a valid check
	}
}
