package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.rabin.IRabinAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * This Rabin automaton uses a Rabin-Petri-Net and lazily converts it to a semantically equivalent automaton
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 *            type of letters
 * @param <STATE>
 *            type of states/places
 * @param <FACTORY>
 *            a {@link IPetriNet2FiniteAutomatonStateFactory} and {@link IBlackWhiteStateFactory} that operates on
 *            states/places
 */
public class RabinPetriNet2RabinAutomaton<LETTER, STATE, FACTORY extends IPetriNet2FiniteAutomatonStateFactory<STATE> & IBlackWhiteStateFactory<STATE>>
		implements IRabinAutomaton<LETTER, STATE> {

	private final IRabinPetriNet<LETTER, STATE> mOperand;
	private final FACTORY mContentFactory;

	private Set<STATE> mInitialStates;
	private final HashMap<STATE, Pair<Marking<STATE>, AcceptanceCondition>> mAutomatonMap = new HashMap<>();

	/**
	 * This constructor take a IRabinPetriNet and a FACTORY, and prepares a semantically equivalent Rabin-automaton
	 *
	 * @param rpn
	 *            The Rabin-Petri-Net that should be transformed to a Rabin automaton
	 * @param factory
	 *            A {@link IPetriNet2FiniteAutomatonStateFactory} and {@link IBlackWhiteStateFactory} that operates on
	 *            type STATE
	 */
	public RabinPetriNet2RabinAutomaton(final IRabinPetriNet<LETTER, STATE> rpn, final FACTORY factory) {
		mOperand = rpn;
		mContentFactory = factory;
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mOperand.getAlphabet();
	}

	/**
	 * The size information is an upper bound for reachable states.
	 */
	@Override
	public int size() {
		final int operandSize = mOperand.getPlaces().size();
		// bitshift will fail for larger numbers
		if (operandSize > (Integer.SIZE - 2)) {
			return -1;
		}
		if (operandSize == 0) {
			return 0;
		}
		// (2^operandSize) *3
		return AcceptanceCondition.values().length << (operandSize - 1);
	}

	/**
	 * The size information is an upper bound for reachable states.
	 */
	@Override
	public String sizeInformation() {
		final int size = size();
		if (size == -1) {
			return "Automaton has more than " + Integer.MAX_VALUE + " states!" + "Currently " + mAutomatonMap.size()
					+ " have been lazily computed.";
		}
		return "Automaton has " + size + " states.\n" + "Currently " + mAutomatonMap.size()
				+ " have been lazily computed.";
	}

	@Override
	public Set<STATE> getInitialStates() {
		if (mInitialStates == null) {
			mInitialStates = Set.of(getMarking2State(new Marking<>(ImmutableSet.of(mOperand.getInitialPlaces())),
					AcceptanceCondition.NONFINITE));
		}
		return mInitialStates;
	}

	@Override
	public boolean isAccepting(final STATE state) {
		return mAutomatonMap.get(state).getSecond() == AcceptanceCondition.ACCEPTING;
	}

	@Override
	public boolean isFinite(final STATE state) {
		return mAutomatonMap.get(state).getSecond() == AcceptanceCondition.FINITE;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state) {
		final Pair<Marking<STATE>, AcceptanceCondition> originalStateInformation = mAutomatonMap.get(state);
		try {
			return getStateOutgoingTransitions(originalStateInformation.getFirst(),
					activeTransitionsWithoutSymbol(originalStateInformation.getFirst()));
		} catch (final PetriNetNot1SafeException e) {
			// TODO Make a proper catch-block
			e.printStackTrace();
			return null;
		}

	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state, final LETTER letter) {
		final Pair<Marking<STATE>, AcceptanceCondition> originalStateInformation = mAutomatonMap.get(state);
		try {
			return getStateOutgoingTransitions(originalStateInformation.getFirst(),
					activeTransitionsWithSymbol(originalStateInformation.getFirst(), letter));
		} catch (final PetriNetNot1SafeException e) {
			// TODO Make a proper catch-block
			e.printStackTrace();
			return null;
		}
	}

	private STATE getMarking2State(final Marking<STATE> marking, final AcceptanceCondition acceptanceCondition) {
		STATE result = mContentFactory.getContentOnPetriNet2FiniteAutomaton(marking);
		switch (acceptanceCondition) {
		case ACCEPTING:
			result = mContentFactory.getBlackContent(result);
			break;
		case FINITE:
			result = mContentFactory.getWhiteContent(result);
			break;
		default:
			break;
		}
		mAutomatonMap.computeIfAbsent(result, x -> new Pair<>(marking, acceptanceCondition));
		return result;
	}

	private enum AcceptanceCondition {
		FINITE, NONFINITE, ACCEPTING;
	}

	private static AcceptanceCondition returnBest(final AcceptanceCondition x, final AcceptanceCondition y) {
		if (x.ordinal() < y.ordinal()) {
			return y;
		}
		return x;
	}

	/**
	 * method for returning successor markings and the best AcceptanceCondition which was encountered for all
	 * transitions reaching a specific marking, based on code from Daniel Küchlers RabinAccepts
	 */
	private Iterable<OutgoingInternalTransition<LETTER, STATE>> getStateOutgoingTransitions(
			final Marking<STATE> currentMarking, final HashSet<Transition<LETTER, STATE>> enabledTransitionSet)
			throws PetriNetNot1SafeException {

		final HashMap<OutgoingInternalTransition<LETTER, STATE>, AcceptanceCondition> resultWithAcceptanceCondition =
				new HashMap<>();

		for (final Transition<LETTER, STATE> transition : enabledTransitionSet) {
			AcceptanceCondition ac;
			if (!(transition.getSuccessors().stream().anyMatch(mOperand::isFinite))) {
				if (transition.getSuccessors().stream().anyMatch(mOperand::isAccepting)) {
					ac = AcceptanceCondition.ACCEPTING;
				} else {
					ac = AcceptanceCondition.NONFINITE;
				}
			} else {
				ac = AcceptanceCondition.FINITE;
			}
			final OutgoingInternalTransition<LETTER, STATE> outgoingTransition = new OutgoingInternalTransition<>(
					transition.getSymbol(), getMarking2State(currentMarking.fireTransition(transition), ac));
			if (resultWithAcceptanceCondition.containsKey(outgoingTransition)) {
				ac = returnBest(resultWithAcceptanceCondition.get(outgoingTransition), ac);
			}
			resultWithAcceptanceCondition.put(outgoingTransition, ac);
		}
		return resultWithAcceptanceCondition.keySet();
	}

	/**
	 * Copied from Daniel Küchlers Accepts
	 */
	private HashSet<Transition<LETTER, STATE>> activeTransitionsWithSymbol(final Marking<STATE> marking,
			final LETTER symbol) {
		final HashSet<Transition<LETTER, STATE>> activeTransitionsWithSymbol = new HashSet<>();
		for (final STATE place : marking) {
			mOperand.getSuccessors(place).stream().filter(transition -> transition.getSymbol().equals(symbol))
					.filter((transition -> marking.isTransitionEnabled(transition))).collect(Collectors.toSet())
					.forEach(activeTransitionsWithSymbol::add);
		}
		return activeTransitionsWithSymbol;
	}

	private HashSet<Transition<LETTER, STATE>> activeTransitionsWithoutSymbol(final Marking<STATE> marking) {
		final HashSet<Transition<LETTER, STATE>> activeTransitionsWithSymbol = new HashSet<>();
		for (final STATE place : marking) {
			mOperand.getSuccessors(place).stream().filter((transition -> marking.isTransitionEnabled(transition)))
					.collect(Collectors.toSet()).forEach(activeTransitionsWithSymbol::add);
		}
		return activeTransitionsWithSymbol;
	}
}
