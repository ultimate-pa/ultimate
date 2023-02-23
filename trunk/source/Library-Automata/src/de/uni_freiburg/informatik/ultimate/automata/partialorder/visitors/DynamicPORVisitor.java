package de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.DepthFirstTraversal;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;


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
	// The current stack of letters (word to current state)
	private final ArrayList<L> mWord = new ArrayList<>();
	// Hashmap to remember backtrackingpoints
	private ArrayList<L> mBacktrackSet = new ArrayList<>();
	//private final Deque<Pair<S, OutgoingInternalTransition<L, S>>> mWorklist = new ArrayDeque<>();

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
		if (isComplete) {
			//mWord.remove(mWord.size() - 1);  // remove last letter
			//mBacktrackSet.remove(mBacktrackSet.size() - 1);
		}
	}
	
	private void visitState(final S state) {
		// actions for a state
		//System.out.println("visit state");
	}
	
	@Override
	public boolean discoverTransition(final S source, final L letter, final S target) {
		// keep track of word and state
		mPendingState = target;
		mWord.add(letter);
		mBacktrackSet.add(letter); // is the smallest letter -> add to backtrack
		
		// Set the necessary backtrackingpoints
		SetBacktrackingPoints(letter);
		
		// return true if letter is not in backtrackset(source)
		return false || mUnderlying.discoverTransition(source, letter, target);
	}
	
	private boolean SetBacktrackingPoints(final L letter) {
		if (mWord.size() == 1) {
			return true;
		}
		System.out.println(mBacktrackSet.toString());
		for (int i = 0; i < mWord.size(); i++) {
			if (!isIndependent(mWord.get(i), letter)) {
				// if letter < mBacktrackset(i) and letter enabled
				mBacktrackSet.set(i, letter);
			}
		}
		
		System.out.println("backtrack word " + mWord.toString());
		// backtrack state has to be computed from word
		//final Set<L> backtrack = mBacktrackSet.get(state);
		// add letter to backtrack
		//backtrack.add(letter);
		//mBacktrackSet.replace(state, backtrack);
		return false;
	}
	
	// placeholder for Independence
	private boolean isIndependent(L a, L b) {
		return false;
	}
}