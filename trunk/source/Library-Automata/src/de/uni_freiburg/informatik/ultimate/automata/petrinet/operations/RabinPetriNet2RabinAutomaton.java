package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.rabin.IRabinAutomaton;

public class RabinPetriNet2RabinAutomaton<LETTER, STATE> implements IRabinAutomaton<LETTER, STATE> {

	IRabinPetriNet<LETTER, STATE> mOperand;

	public RabinPetriNet2RabinAutomaton(final IRabinPetriNet<LETTER, STATE> rpn) {
		mOperand = rpn;
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mOperand.getAlphabet();
	}

	@Override
	public int size() {

		final int result = 2 << mOperand.getPlaces().size();
		if (result == 0 && (mOperand.getPlaces().size() != 0)) {
			return -1;
		}
		return result;
	}

	@Override
	public String sizeInformation() {
		final int size = size();
		if (size == -1) {
			return "Automaton has more than " + Integer.MAX_VALUE + " states!";
		}
		return "Automaton has " + size + " states.";
	}

	@Override
	public Set<STATE> getInitialStates() {
		return null;
	}

	@Override
	public boolean isAccepting(final STATE state) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isFinite(final STATE state) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state, final LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

}
