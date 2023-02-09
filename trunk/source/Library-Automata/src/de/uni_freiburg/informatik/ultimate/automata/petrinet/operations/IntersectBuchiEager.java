package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIntersect;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsIncludedBuchi;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.PetriNetUtils;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiIntersectStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Creates intersection of Buchi Petri net and buchi automata (eagerly).
 *
 * @param <LETTER>
 * @param <PLACE>
 */
public class IntersectBuchiEager<LETTER, PLACE>
		extends GeneralOperation<LETTER, PLACE, IPetriNet2FiniteAutomatonStateFactory<PLACE>> {

	private final IPetriNet<LETTER, PLACE> mPetriNet;
	private final INestedWordAutomaton<LETTER, PLACE> mBuchiAutomata;

	private final IBlackWhiteStateFactory<PLACE> mLabeledBuchiPlaceFactory;

	private final Map<PLACE, PLACE> mInputQGetQ1 = new HashMap<>();
	private final Map<PLACE, PLACE> mInputQGetQ2 = new HashMap<>();
	private final Map<PLACE, PLACE> mInputQ2GetQ = new HashMap<>();

	private final BoundedPetriNet<LETTER, PLACE> mIntersectionNet;

	private final Set<LETTER> mLooperSymbols = new HashSet<>();

	private final Set<PLACE> mStateTwoEnablerSet = new HashSet<>();

	private PLACE mCurrentNewPlace;

	private final Set<Transition<LETTER, PLACE>> toBeDoneStateOneOnlyTransitions = new HashSet<>();

	private final Set<Transition<LETTER, PLACE>> toBeDoneTransitions = new HashSet<>();

	private final HashMap<PLACE, PLACE> looperAcptPlaceToEnablePlace = new HashMap<>();

	public IntersectBuchiEager(final AutomataLibraryServices services, final IBlackWhiteStateFactory<PLACE> factory,
			final IPetriNet<LETTER, PLACE> petriNet, final INestedWordAutomaton<LETTER, PLACE> buchiAutomata) {
		super(services);
		mPetriNet = petriNet;
		mBuchiAutomata = buchiAutomata;
		mLogger.info(startMessage());
		if (buchiAutomata.getInitialStates().size() != 1) {
			throw new IllegalArgumentException("Buchi with multiple initial states not supported.");
		}
		mLabeledBuchiPlaceFactory = factory;
		mCurrentNewPlace = mPetriNet.getAcceptingPlaces().iterator().next();
		mIntersectionNet = new BoundedPetriNet<>(services, petriNet.getAlphabet(), false);
		constructIntersectionNet();
		mLogger.info(exitMessage());
	}

	private final void constructIntersectionNet() {
		addPlacesToIntersectionNet();
		calculateLoopers();
		addLooperPlacesAndTransitions();
		addNonLooperTransitionsToIntersectionNet();
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

	private final void calculateLoopers() {
		for (final LETTER transitionSymbol : mBuchiAutomata.getAlphabet()) {
			boolean isLooper = true;
			for (final PLACE buchiPlace : mBuchiAutomata.getStates()) {
				for (final OutgoingInternalTransition<LETTER, PLACE> buchiTransition : mBuchiAutomata
						.internalSuccessors(buchiPlace, transitionSymbol)) {
					if (!(buchiTransition.getSucc() == buchiPlace)) {
						isLooper = false;
						break;
					}
				}

				if (!isLooper) {
					break;
				}
			}
			if (isLooper) {
				mLooperSymbols.add(transitionSymbol);
			}
		}
		// mLogger.info("From " + mBuchiAutomata.getAlphabet().size() + " symbols, " + mLooperSymbols.size()
		// + " are looper symbols.");
	}

	private final void addLooperPlacesAndTransitions() {
		for (final Transition<LETTER, PLACE> petriTransition : mPetriNet.getTransitions()) {
			if (mLooperSymbols.contains(petriTransition.getSymbol())) {
				addLooperOptimizedTransitions(petriTransition);
			}
		}
	}

	private final void addNonLooperTransitionsToIntersectionNet() {
		for (final Transition<LETTER, PLACE> petriTransition : mPetriNet.getTransitions()) {
			if (!mLooperSymbols.contains(petriTransition.getSymbol())) {
				// normal construction
				addTransitionsNormally(petriTransition);
			} else if (toBeDoneTransitions.contains(petriTransition)) {
				// is looper but no optimization possible
				addTransitionsNormally(petriTransition);
			} else if (toBeDoneStateOneOnlyTransitions.contains(petriTransition)) {
				// is looper and only state two transitions could be optimized
				addStateOneTransitionsNormally(petriTransition);
			}
		}
	}

	private final void addTransitionsNormally(final Transition<LETTER, PLACE> petriTransition) {
		for (final PLACE buchiPlace : mBuchiAutomata.getStates()) {
			for (final OutgoingInternalTransition<LETTER, PLACE> buchiTransition : mBuchiAutomata
					.internalSuccessors(buchiPlace, petriTransition.getSymbol())) {
				addStateOneAndTwoTransition(petriTransition, buchiTransition, buchiPlace);
			}
		}
	}

	private final void addLooperOptimizedTransitions(final Transition<LETTER, PLACE> petriTransition) {
		boolean leadsIntoAcceptingPetri = false;
		boolean loopsInAcceptingBuchi = false;

		if (petriTransition.getSuccessors().stream().anyMatch(mPetriNet.getAcceptingPlaces()::contains)) {
			leadsIntoAcceptingPetri = true;
		}

		for (final PLACE state : mBuchiAutomata.getStates()) {
			if (mBuchiAutomata.internalSuccessors(state, petriTransition.getSymbol()).iterator().hasNext()) {
				loopsInAcceptingBuchi = true;
				break;
			}
		}

		if (!leadsIntoAcceptingPetri && !loopsInAcceptingBuchi) {
			// full looper optimization possible
			addPurePetriTransition(petriTransition);
		} else if (leadsIntoAcceptingPetri) {
			// theoretically we cannot optimize here ? since we dont know which Q-state has a token right now.
			toBeDoneTransitions.add(petriTransition);
		} else if (loopsInAcceptingBuchi) {
			// can only optimize state two transition
			toBeDoneStateOneOnlyTransitions.add(petriTransition);
			buildLooperOptimizationStateTwo(petriTransition);
		}
	}

	private final void addPurePetriTransition(final Transition<LETTER, PLACE> petriTransition) {
		mIntersectionNet.addTransition(petriTransition.getSymbol(), petriTransition.getPredecessors(),
				petriTransition.getSuccessors());
	}

	private final void buildLooperOptimizationStateTwo(final Transition<LETTER, PLACE> petriTransition) {
		addPurePetriTransition(petriTransition);

		for (final PLACE buchiPlace : mBuchiAutomata.getFinalStates()) {
			for (final OutgoingInternalTransition<LETTER, PLACE> buchiTransition : mBuchiAutomata
					.internalSuccessors(buchiPlace, petriTransition.getSymbol())) {
				// second for loop for the case that buchi automata is not complete or nondeterministic
				final PLACE newPlace = getNewPlace();
				mStateTwoEnablerSet.add(newPlace);
				mIntersectionNet.addPlace(newPlace, false, false);
				looperAcptPlaceToEnablePlace.put(buchiPlace, newPlace);

				final Set<PLACE> predecessorSet = new HashSet<>(petriTransition.getPredecessors());
				predecessorSet.add(newPlace);
				final Set<PLACE> successorSet = petriTransition.getSuccessors();
				mIntersectionNet.addTransition(petriTransition.getSymbol(), ImmutableSet.of(predecessorSet),
						ImmutableSet.of(successorSet));
				break;
			}
		}

	}

	private final PLACE getNewPlace() {
		// TODO: Replace this if there exists a better way to create a new place.
		mCurrentNewPlace = mLabeledBuchiPlaceFactory.getBlackContent(mCurrentNewPlace);
		return (mCurrentNewPlace);
	}

	private final void addStateOneTransitionsNormally(final Transition<LETTER, PLACE> petriTransition) {
		for (final PLACE buchiPlace : mBuchiAutomata.getStates()) {
			for (final OutgoingInternalTransition<LETTER, PLACE> buchiTransition : mBuchiAutomata
					.internalSuccessors(buchiPlace, petriTransition.getSymbol())) {
				addStateOneTransition(petriTransition, buchiTransition, buchiPlace);
			}
		}
	}

	private final void addStateOneTransition(final Transition<LETTER, PLACE> petriTransition,
			final OutgoingInternalTransition<LETTER, PLACE> buchiTransition, final PLACE buchiPredecessor) {
		final Set<PLACE> predecessorSet = getTransitionPredecessors(petriTransition, buchiPredecessor, true);
		final Set<PLACE> successorSet = getTransitionSuccessors(petriTransition, buchiTransition, predecessorSet, true);
		mIntersectionNet.addTransition(petriTransition.getSymbol(), ImmutableSet.of(predecessorSet),
				ImmutableSet.of(successorSet));
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
			for (final PLACE place : looperAcptPlaceToEnablePlace.keySet()) {
				if (predecessorSet.contains(place)) {
					predecessorSet.add(looperAcptPlaceToEnablePlace.get(place));
				}
			}
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
			for (final PLACE place : looperAcptPlaceToEnablePlace.keySet()) {
				if (successorSet.contains(place)) {
					successorSet.add(looperAcptPlaceToEnablePlace.get(place));
				}
			}
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
	public String startMessage() {
		return "Starting Intersection";
	}

	@Override
	public String exitMessage() {
		return "Exiting Intersection";
	}

	@Override
	public IPetriNet<LETTER, PLACE> getResult() {
		return mIntersectionNet;
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
						(IBlackWhiteStateFactory<PLACE>) stateFactory, mIntersectionNet)).getResult();

		final NestedWordAutomatonReachableStates<LETTER, PLACE> automatonIntersection = new BuchiIntersect<>(mServices,
				(IBuchiIntersectStateFactory<PLACE>) stateFactory, operandAsNwa, mBuchiAutomata).getResult();

		final IsIncludedBuchi<LETTER, PLACE> isSubset = new IsIncludedBuchi<>(mServices,
				(INwaInclusionStateFactory<PLACE>) stateFactory, resultAsNwa, automatonIntersection);
		if (!isSubset.getResult()) {
			final NestedLassoWord<LETTER> ctx = isSubset.getCounterexample().getNestedLassoWord();
			final ILogger logger = mServices.getLoggingService().getLogger(PetriNetUtils.class);
			logger.error("Intersection recognizes incorrect word : " + ctx);

		}
		final IsIncludedBuchi<LETTER, PLACE> isSuperset = new IsIncludedBuchi<>(mServices,
				(INwaInclusionStateFactory<PLACE>) stateFactory, automatonIntersection, resultAsNwa);
		if (!isSuperset.getResult()) {
			final NestedLassoWord<LETTER> ctx = isSuperset.getCounterexample().getNestedLassoWord();
			final ILogger logger = mServices.getLoggingService().getLogger(PetriNetUtils.class);
			logger.error("Intersection not recognizing word of correct intersection : " + ctx);
		}
		return isSubset.getResult() && isSuperset.getResult();
	}
}
