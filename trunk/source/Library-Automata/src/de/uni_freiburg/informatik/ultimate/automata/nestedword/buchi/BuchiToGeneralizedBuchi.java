package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.IGeneralizedNwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

public class BuchiToGeneralizedBuchi<LETTER, STATE> implements IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> {

	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;
	
	public BuchiToGeneralizedBuchi(INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand) {
		mOperand = operand;
	}
	
	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(STATE state, LETTER letter) {
		return mOperand.internalSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(STATE state, LETTER letter) {
		return mOperand.callSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(STATE state, STATE hier, LETTER letter) {
		return mOperand.returnSuccessors(state, hier, letter);
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mOperand.getAlphabet();
	}

	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mOperand.getStateFactory();
	}

	@Override
	public int size() {
		return mOperand.size();
	}

	@Override
	public String sizeInformation() {
		return mOperand.sizeInformation();
	}

	@Override
	public VpAlphabet<LETTER> getVpAlphabet() {
		return mOperand.getVpAlphabet();
	}

	@Override
	public STATE getEmptyStackState() {
		return mOperand.getEmptyStackState();
	}

	@Override
	public Iterable<STATE> getInitialStates() {
		return mOperand.getInitialStates();
	}

	@Override
	public boolean isInitial(STATE state) {
		return mOperand.isInitial(state);
	}

	@Override
	public int getAcceptanceSize() {
		return 1;
	}

	@Override
	public boolean isFinal(STATE state, int index) {
		if(index > 0 || index < 0) return false;
		return mOperand.isFinal(state);
	}

	@Override
	public Set<Integer> getAcceptanceLabels(STATE state) {
		Set<Integer> labels = new HashSet<>();
		if(mOperand.isFinal(state)) {
			labels.add(0);
		}
		return labels;
	}

}
