package de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.DepthFirstTraversal;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;


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
	// List to remember chosen path
	// Contains States, Letter representing the Backtrackset and Letter chosen from State S
	private ArrayList<Triple<S,L,L>> mStateTrace = new ArrayList<>();

	//private final Deque<Pair<S, OutgoingInternalTransition<L, S>>> mWorklist = new ArrayDeque<>();
	private final INwaOutgoingLetterAndTransitionProvider<L, S> mAutomaton;
	private final IDfsOrder<L,S> mOrder;

	// A possible successor of the last state on the stack, which may become the next element on the stack.
	private S mPendingState;
	
	public DynamicPORVisitor(final V underlying, final INwaOutgoingLetterAndTransitionProvider<L, S> operand, final IDfsOrder<L, S> order) { // V - underlying visitor to which calls are proxied
		super(underlying);
		mAutomaton = operand;
		mOrder = order;
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
		if (isComplete) {
			int index = mStateTrace.size()-1;
			if (index > 0) {
				if (mStateTrace.get(mStateTrace.size()-1).getFirst().equals(state)) {
				mStateTrace.remove(mStateTrace.size() - 1);
				}
			}
		}
	}
	
	private void visitState(final S state) {
		// add the greatest letter from membrane to backtrack(state)
		
		// actions for a state
		//System.out.println("visit state");
	}
	
	@Override
	public boolean discoverTransition(final S source, final L letter, final S target) {
		// keep track of word and state
		mPendingState = target;
		int index = mStateTrace.size()-1;
		if (index < 0) {
			mStateTrace.add(new Triple<S,L,L>(source, letter, letter));
			return false || mUnderlying.discoverTransition(source, letter, target);
		}
		
		if (!mStateTrace.get(index).getFirst().equals(source)) {
			mStateTrace.add(new Triple<S,L,L>(source, letter, letter));
		} else {
			// get old backtrackset and set state, letter
			L backtrackState = mStateTrace.get(index).getSecond();
			mStateTrace.set(index, new Triple<S,L,L>(source, backtrackState, letter));
		}
		// backtracksetLetter is the greatest letter from backtrackset
		// any letter greater can therefore not be in backtrackset
		if (mOrder.getOrder(source).compare(letter, mStateTrace.get(mStateTrace.size()-1).getSecond()) > 0) {
			return true;
		}
		// Set the disable backtrackingpoints
		disableBacktracking(letter);
		// Set the necessary backtrackingpoints
		setBacktrackingPoints(letter);
		
		System.out.println(mStateTrace);
		// return true if letter is not in backtrackset(source)
		return false || mUnderlying.discoverTransition(source, letter, target);
	}
	
	private boolean disableBacktracking(final L letter) {
		int index = mStateTrace.size();
		for (L a: mAutomaton.getAlphabet()) {
			if (disables(letter, a)) {
				L backtrackLetter = mStateTrace.get(index).getSecond();
				S backtrackState = mStateTrace.get(index).getFirst();
				// check if a enabled in backtrackState
				boolean enabled = false;
				for (OutgoingInternalTransition<L, S> t : mAutomaton.internalSuccessors(backtrackState, a)) {
					enabled = true;
				}
				if (enabled) {
					if (mOrder.getOrder(backtrackState).compare(backtrackLetter, a) < 0) {
						// backtrackLetter < a
						// Set mStateTrace.get(index).Second to a
					} else {
						// do nothing
					}
				} else {
					// a is not enabled
					// add necessary enabling set for a
				}
			}
		}
		return true;
	}
	
	
	private boolean setBacktrackingPoints(final L letter) {
		ArrayList<L> mWord = currentWord();
		if (mWord.size() <= 1) {
			return true;
		}
		for (int i = 0; i < mWord.size() - 1; i++) {
			S backtrackState = mStateTrace.get(i).getFirst();
			L backtrackSetLetter = mStateTrace.get(i).getSecond();
			L transitionLetter = mStateTrace.get(i).getThird();

			if (!isIndependent(transitionLetter, letter)) {
				// check if letter is enabled in State i
				boolean enabled = false;
				for (OutgoingInternalTransition<L, S> a : mAutomaton.internalSuccessors(backtrackState, letter)) {
					enabled = true;
				 }
				 // if enabled and dependent add letter to backtrack
				 if (enabled) {
					 if (mOrder.getOrder(mPendingState).compare(letter, backtrackSetLetter) < 0) {
						 // letter < backtrackset(i)
						// letter is already backtracked if backtrackset(i) > letter by compatibility
					 } else {
						 Triple<S,L,L> triple = new Triple<S,L,L>(backtrackState, letter, transitionLetter);
						 mStateTrace.set(i, triple);
					 }
				 } else {
					 // compute necessary enabling set
					 // set the backtrackletter from mStateTrace(i) to the max of enabling set
				 }
			}
		}
		return false;
	}
	
	// placeholder for Independence
	private boolean isIndependent(L a, L b) {
		return false;
	}
	
	private boolean disables(L a, L b) {
		return false;
	}
	
	private ArrayList<L> currentWord() {
		ArrayList<L> result = new ArrayList<>();
		for (Triple<S,L,L> triple : mStateTrace) {
			result.add(triple.getThird());
		}
		return result;
	}
}