package de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;


/**
 * Visitor Class for the Dynamic Partial Order Reduction.
 *
 * @author 
 *
 * @param <L>
 *            letter
 * @param <S>
 *            state
 */
public class DynamicPORVisitor<L, S, V extends IDfsVisitor<L, S>> extends WrapperVisitor<L, S, V> {
	// The current stack of states
	private final Deque<S> mStateStack = new ArrayDeque<>();

	// A possible successor of the last state on the stack, which may become the next element on the stack.
	private S mPendingState;
	
	public DynamicPORVisitor(final V underlying) { // V - underlying visitor to which calls are proxied
		super(underlying);
	}
	
	@Override
	public boolean addStartState(final S state) {
		assert mStateStack.isEmpty() : "start state must be first";
		mStateStack.addLast(state);
		visitState(state);
		return mUnderlying.addStartState(state);
	}


	public boolean getReductionAutomaton() {
		return true;
	}
	
	@Override
	public void backtrackState(final S state, final boolean isComplete) {
		
	}
	
	private void visitState(final S state) {
		// actions for a state
		//System.out.println("visit state");
	}
	
	@Override
	public boolean discoverTransition(final S source, final L letter, final S target) {
		mPendingState = target;
		
		// return true if letter should be pruned
		return false || mUnderlying.discoverTransition(source, letter, target);
	}
}