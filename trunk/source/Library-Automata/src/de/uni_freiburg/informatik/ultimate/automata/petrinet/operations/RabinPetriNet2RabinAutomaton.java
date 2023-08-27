package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.rabin.IRabinAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class RabinPetriNet2RabinAutomaton<LETTER, STATE, FACTORY extends IPetriNet2FiniteAutomatonStateFactory<STATE> & IBlackWhiteStateFactory<STATE>>
		implements IRabinAutomaton<LETTER, STATE> {

	IRabinPetriNet<LETTER, STATE> mOperand;

	private final FACTORY mContentFactory;

	public RabinPetriNet2RabinAutomaton(final IRabinPetriNet<LETTER, STATE> rpn, final FACTORY factory) {
		mOperand = rpn;
		mContentFactory = factory;
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mOperand.getAlphabet();
	}

	@Override
	public int size() {
		final int operandSize = mOperand.getPlaces().size();
		if (operandSize > 29) {
			return -1;
		}
		if (operandSize == 0) {
			return 0;
		}
		return 3 << (operandSize - 1);
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
		return Set.of(mContentFactory
				.getContentOnPetriNet2FiniteAutomaton(new Marking<>(ImmutableSet.of(mOperand.getInitialPlaces()))));
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
