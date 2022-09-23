package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiDifferenceFKV;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsIncludedBuchi;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.PetriNetUtils;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Eager difference of Rabin-petri net minuend and buchi automata subtrahend.
 *
 */
public class DifferenceRabin<LETTER, PLACE>
		extends GeneralOperation<LETTER, PLACE, IPetriNet2FiniteAutomatonStateFactory<PLACE>> {

	private final IRabinPetriNet<LETTER, PLACE> mPetriNet;
	private final INestedWordAutomaton<LETTER, PLACE> mBuchiAutomata;
	private final BoundedRabinPetriNet<LETTER, PLACE> mDifferenceNet;

	public DifferenceRabin(final IRabinPetriNet<LETTER, PLACE> petriNet,
			final INestedWordAutomaton<LETTER, PLACE> buchiAutomata, final AutomataLibraryServices services) {
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
	public IPetriNet<LETTER, PLACE> getResult() {
		return mDifferenceNet;
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
			if (mBuchiAutomata.isFinal(place)) {
				mDifferenceNet.addFinitePlace(place);
				continue;
			}
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

	@SuppressWarnings("unchecked")
	@Override
	public boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<PLACE> stateFactory)
			throws AutomataLibraryException {
		final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> operandAsNwa =
				(new BuchiPetriNet2FiniteAutomaton<>(mServices, stateFactory,
						(IBlackWhiteStateFactory<PLACE>) stateFactory, mPetriNet)).getResult();
		final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> resultAsNwa =
				(new BuchiPetriNet2FiniteAutomaton<>(mServices, stateFactory,
						(IBlackWhiteStateFactory<PLACE>) stateFactory, mDifferenceNet)).getResult();

		final NestedWordAutomatonReachableStates<LETTER, PLACE> automatonDifference =
				(NestedWordAutomatonReachableStates<LETTER, PLACE>) (new BuchiDifferenceFKV(mServices,
						(IDeterminizeStateFactory<PLACE>) stateFactory, operandAsNwa, mBuchiAutomata)).getResult();
		final IsIncludedBuchi<LETTER, PLACE> isSubset = new IsIncludedBuchi<>(mServices,
				(INwaInclusionStateFactory<PLACE>) stateFactory, resultAsNwa, automatonDifference);
		if (!isSubset.getResult()) {
			final NestedLassoWord<LETTER> ctx = isSubset.getCounterexample().getNestedLassoWord();
			final ILogger logger = mServices.getLoggingService().getLogger(PetriNetUtils.class);
			logger.error("Intersection recognizes incorrect word : " + ctx);

		}
		final IsIncludedBuchi<LETTER, PLACE> isSuperset = new IsIncludedBuchi<>(mServices,
				(INwaInclusionStateFactory<PLACE>) stateFactory, automatonDifference, resultAsNwa);
		if (!isSuperset.getResult()) {
			final NestedLassoWord<LETTER> ctx = isSuperset.getCounterexample().getNestedLassoWord();
			final ILogger logger = mServices.getLoggingService().getLogger(PetriNetUtils.class);
			logger.error("Intersection not recognizing word of correct intersection : " + ctx);
		}
		return isSubset.getResult() && isSuperset.getResult();
	}
}
