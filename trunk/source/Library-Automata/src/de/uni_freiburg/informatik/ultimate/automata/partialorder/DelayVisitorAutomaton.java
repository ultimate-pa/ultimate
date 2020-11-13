package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.ArrayDeque;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;

public class DelayVisitorAutomaton<L, S> implements IPartialOrderVisitor<L, S> {
	
	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;
	private final NestedWordAutomaton<L, S> mReductionAutomaton;

	public DelayVisitorAutomaton(final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final AutomataLibraryServices services, final IEmptyStackStateFactory<S> stateFactory) {
		mOperand = operand;
		mReductionAutomaton = new NestedWordAutomaton<>(services, mOperand.getVpAlphabet(), stateFactory);
	}
	@Override
	public void discoverState() {
		// do nothing
		
	}
	@Override
	public boolean discoverTransition(S source, L letter, S target) {
		// add succState to the automaton
		if (!mReductionAutomaton.contains(target)) {
			mReductionAutomaton.addState(false, mOperand.isFinal(target), target);
		}
		// add transition from currentState to succState to the automaton
		mReductionAutomaton.addInternalTransition(source, letter, target);
		return mOperand.isFinal(target);
	}

	@Override
	public void backtrackState(Object state) {
		// do nothing
	}
	
	public NestedRun<L, S> constructRun(ArrayDeque<S> stateStack) {
		return null;
	}
	
	public NestedWordAutomaton<L, S> getReductionAutomaton(){
		return mReductionAutomaton;
	}
	
	@Override
	public void addStartState(S state) {
		mReductionAutomaton.addState(true, mOperand.isFinal(state), state);
		
	}

}
