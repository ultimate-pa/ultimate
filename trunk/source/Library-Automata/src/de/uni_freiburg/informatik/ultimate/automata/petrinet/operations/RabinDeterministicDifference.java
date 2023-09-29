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
 * Eager difference of Rabin-Petri-net minuend and Buchi automaton subtrahend. Buchi automata must be complete and
 * deterministic.
 *
 * @param <LETTER>
 *            type of letters
 * @param <PLACE>
 *            type of places
 */
public class RabinDeterministicDifference<LETTER, PLACE>
		extends GeneralOperation<LETTER, PLACE, IPetriNet2FiniteAutomatonStateFactory<PLACE>> {

	private final IRabinPetriNet<LETTER, PLACE> mPetriNet;
	private final INestedWordAutomaton<LETTER, PLACE> mBuchiAutomaton;
	private final BoundedRabinPetriNet<LETTER, PLACE> mDifferenceNet;

	/**
	 * eagerly builds a Rabin-Petri-Net that accepts L = @param{petriNet} - @param{buchiAutomaton}
	 *
	 * @param services
	 *            services
	 * @param petriNet
	 *            the Rabin-Petri-Net minuend
	 * @param buchiAutomaton
	 *            the automaton subtrahend
	 * @throws AutomataLibraryException
	 *             a exception to be thrown when the automaton is not complete or deterministic
	 */
	public RabinDeterministicDifference(final AutomataLibraryServices services,
			final IRabinPetriNet<LETTER, PLACE> petriNet, final INestedWordAutomaton<LETTER, PLACE> buchiAutomaton)
			throws AutomataLibraryException {
		super(services);
		mPetriNet = petriNet;
		mBuchiAutomaton = buchiAutomaton;
		if (buchiAutomaton.getInitialStates().size() != 1) {
			throw new IllegalArgumentException("Buchi with multiple initial states not supported.");
		}
		mDifferenceNet = new BoundedRabinPetriNet<>(services, petriNet.getAlphabet(), false);

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
			if (mPetriNet.isFinite(place)) {
				mDifferenceNet.addFinitePlace(place);
				mDifferenceNet.addPlace(place, mPetriNet.getInitialPlaces().contains(place), false);
			} else {
				mDifferenceNet.addPlace(place, mPetriNet.getInitialPlaces().contains(place),
						mPetriNet.isAccepting(place));

			}
		}
	}

	private final void addOriginalBuchiPlaces() {
		for (final PLACE place : mBuchiAutomaton.getStates()) {
			mDifferenceNet.addPlace(place, mBuchiAutomaton.isInitial(place), false);
			if (mBuchiAutomaton.isFinal(place)) {
				mDifferenceNet.addFinitePlace(place);
			}
		}
	}

	private final void addTransitionsToIntersectionNet() throws AutomataLibraryException {
		for (final Transition<LETTER, PLACE> petriTransition : mPetriNet.getTransitions()) {
			for (final PLACE buchiPlace : mBuchiAutomaton.getStates()) {

				final Iterable<OutgoingInternalTransition<LETTER, PLACE>> successorCandidate =
						mBuchiAutomaton.internalSuccessors(buchiPlace, petriTransition.getSymbol());

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
							"Incomplete buchi automaton can not be used in deterministic difference.\n"
									+ "There is no transition for one state-letter pair.");
				}

				addNewTransition(petriTransition, buchiTransition, buchiPlace);

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

	@Override
	public boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<PLACE> stateFactory)
			throws AutomataLibraryException {
		return true; // TODO: implement a valid check
	}
}
