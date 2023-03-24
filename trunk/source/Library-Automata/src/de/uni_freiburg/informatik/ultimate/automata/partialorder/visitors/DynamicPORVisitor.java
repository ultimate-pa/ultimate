package de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDisabling;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IEnabling;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IMembranes;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;

/**
 * Visitor Class for the Dynamic Partial Order Reduction.
 *
 * @author tiloh
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
	private final ArrayList<BacktrackTriple> mStateTrace = new ArrayList<>();

	// private final Deque<Pair<S, OutgoingInternalTransition<L, S>>> mWorklist = new ArrayDeque<>();
	private final INwaOutgoingLetterAndTransitionProvider<L, S> mAutomaton;
	private final IDfsOrder<L, S> mOrder;
	private final IIndependenceRelation<?, L> independenceRelation;
	private final IDisabling<L> disablingRelation;
	private final IMembranes<L, S> membraneSets;
	private final IEnabling<L, S> enablingFunction;

	// A possible successor of the last state on the stack, which may become the next element on the stack.
	private S mPendingState;

	public DynamicPORVisitor(final V underlying, final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final IDfsOrder<L, S> order, final IIndependenceRelation<?, L> independence, final IDisabling<L> disabling,
			final IMembranes<L, S> membrane, final IEnabling<L, S> enabling) { // V - underlying visitor to which calls
																				// are proxied
		super(underlying);
		mAutomaton = operand;
		mOrder = order;
		independenceRelation = independence;
		disablingRelation = disabling;
		membraneSets = membrane;
		enablingFunction = enabling;
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
		assert isComplete : "Incomplete backtracks should only happen for loops, which are unsupported";
		if (isComplete) {
			final int index = mStateTrace.size() - 1;
			if (index > 0) {
				if (mStateTrace.get(mStateTrace.size() - 1).mState.equals(state)) {
					mStateTrace.remove(mStateTrace.size() - 1);
				}
			}
		}
		mUnderlying.backtrackState(state, isComplete);
	}

	private void visitState(final S state) {
	}

	@Override
	public boolean discoverTransition(final S source, final L letter, final S target) {
		// keep track of word and state
		mPendingState = target;
		final int index = mStateTrace.size() - 1;
		if (index < 0) {
			final L initBacktrack = findInitialBacktrackset(source, letter);
			mStateTrace.add(new BacktrackTriple(source, initBacktrack, letter));
			// Set the disable backtrackingpoints for the first letter in inital state
			disableBacktracking(letter);
			return mUnderlying.discoverTransition(source, letter, target);
		}

		if (!mStateTrace.get(index).mState.equals(source)) {
			// find the inital backtrackset
			final L initBacktrack = findInitialBacktrackset(source, letter);
			mStateTrace.add(new BacktrackTriple(source, initBacktrack, letter));
		} else {
			// get old backtrackset keep the backtrackletter and the state and change the transitionletter
			final L backtrackLetter = mStateTrace.get(index).mBacktrackLetter;
			mStateTrace.set(index, new BacktrackTriple(source, backtrackLetter, letter));
		}
		// backtracksetLetter is the greatest letter from backtrackset
		// if letter > backtrackletter the transition can be pruned
		if (!smaller(source, letter, mStateTrace.get(mStateTrace.size() - 1).mBacktrackLetter)) {
			// do not proxy call to underlying visitor, just return
			return true;
		}
		// Set the disable backtrackingpoints for the first 
		disableBacktracking(letter);
		// Set the necessary backtrackingpoints
		setBacktrackingPoints(letter);

		System.out.println(mStateTrace);
		return mUnderlying.discoverTransition(source, letter, target);
	}

	private boolean disableBacktracking(final L letter) {
		System.out.println("disableBacktracking" + letter);
		final int index = mStateTrace.size() - 1;
		for (final L a : mAutomaton.getAlphabet()) {
			if (disables(letter, a)) {
				System.out.println(letter + "disables" + a);
				final L backtrackLetter = mStateTrace.get(index).mBacktrackLetter;
				final S backtrackState = mStateTrace.get(index).mState;
				// check if a enabled in backtrackState
				boolean enabled = false;
				for (final OutgoingInternalTransition<L, S> t : mAutomaton.internalSuccessors(backtrackState, a)) {
					enabled = true;
				}
				if (enabled) {
					if (smaller(backtrackState, backtrackLetter, a)) {
						// backtrackLetter < a
						// Set backtrack letter to a since a has to be added and
						// is the new max of backtrack set
						mStateTrace.set(index, new BacktrackTriple(backtrackState, a, letter));
					} else {
						// do nothing
					}
				} else {
					// add every enabled letter to backtrack set by setting
					// backtrackletter to the max of enabled letters
					L maxLetter = letter;
					for (final OutgoingInternalTransition<L, S> trans : mAutomaton.internalSuccessors(backtrackState)) {
						if (!smaller(backtrackState, trans.getLetter(), maxLetter)) {
							maxLetter = trans.getLetter();
						}
					}
					System.out.println("set backtracking in state "+ backtrackState + "to " +maxLetter);
					mStateTrace.set(index, new BacktrackTriple(backtrackState, maxLetter, letter));

				}
			}
		}
		return true;
	}

	private boolean setBacktrackingPoints(final L letter) {
		final ArrayList<L> mWord = currentWord();
		if (mWord.size() <= 1) {
			return true;
		}
		for (int i = 0; i < mWord.size() - 1; i++) {
			final S backtrackState = mStateTrace.get(i).mState;
			final L backtrackSetLetter = mStateTrace.get(i).mBacktrackLetter;
			final L transitionLetter = mStateTrace.get(i).mTransitionLetter;

			if (!isIndependent(transitionLetter, letter)) {
				System.out.println(transitionLetter + " dependent with " + letter);
				// check if letter is enabled in State i
				boolean enabled = false;
				for (final OutgoingInternalTransition<L, S> a : mAutomaton.internalSuccessors(backtrackState, letter)) {
					enabled = true;
				}
				// if enabled and dependent add letter to backtrack
				if (enabled) {
					if (mOrder.getOrder(mPendingState).compare(letter, backtrackSetLetter) < 0) {
						// letter < backtrackset(i)
						// letter is already backtracked if backtrackset(i) > letter by compatibility
					} else {
						final BacktrackTriple triple = new BacktrackTriple(backtrackState, letter, transitionLetter);
						mStateTrace.set(i, triple);
					}
				} else {
					System.out.println(letter + " not enabled");
					// a is not enabled
					// add necessary enabling set for a (c is the maximum of the enabling set)
					// since a is not enabled by definition the enabling set can not be empty
					final L c = getEnabling(backtrackState, letter);
					System.out.println("enablingletter "+ c);
					if (c != null) {
						mStateTrace.set(i, new BacktrackTriple(backtrackState, c, transitionLetter));
					}
				}
			}
		}
		return false;
	}

	private L findInitialBacktrackset(final S state, final L letter) {
		// first time visiting a state we have to add the membraneset to the backtrackset
		L backtrackLetter = getMembrane(state);
		if (backtrackLetter == null) {
			// if the membraneset is empty the backtrackset contains only the smallest enabled letter
			// which is the transitionletter "letter"
			backtrackLetter = letter;
		}
		return backtrackLetter;
	}

	// Independence check
	private boolean isIndependent(final L a, final L b) {
		final Dependence dep = independenceRelation.isIndependent(null, a, b);
		return dep == Dependence.INDEPENDENT;
	}

	private boolean disables(final L a, final L b) {
		if (disablingRelation == null) {
			return false;
		}
		return disablingRelation.disables(a, b);
	}

	private L getEnabling(final S state, final L letter) {
		if (enablingFunction == null) {
			return null;
		}
		final Set<L> enablingSet = enablingFunction.getEnablingSet(state, letter);
		return getMax(state, enablingSet);
	}

	/**
	 *
	 * @param state
	 * @return a letter that is the maximum of all letters in membraneset of state returns null if the membraneset is
	 *         empty
	 */
	private L getMembrane(final S state) {
		if (membraneSets == null) {
			return null;
		}
		final Set<L> membraneSet = membraneSets.getMembraneSet(state);
		return getMax(state, membraneSet);
	}

	/**
	 * function to compute the maximum of a set of letters. Parametric in the state because the preference order might
	 * depend on the state.
	 *
	 * @param state
	 * @param m
	 * @return
	 */
	private L getMax(final S state, final Set<L> m) {
		if (m.isEmpty()) {
			return null;
		}
		L maxLetter = null;
		for (final L letter : m) {
			// if maxLetter not yet set or letter greater than maxLetter refresh maxLetter
			if (maxLetter == null || !smaller(state, letter, maxLetter)) {
				maxLetter = letter;
			}
		}
		return maxLetter;
	}

	private boolean smaller(final S state, final L a, final L b) {
		return (mOrder.getOrder(state).compare(a, b) <= 0);
	}

	private ArrayList<L> currentWord() {
		final ArrayList<L> result = new ArrayList<>();
		for (final BacktrackTriple triple : mStateTrace) {
			result.add(triple.mTransitionLetter);
		}
		return result;
	}

	/**
	 * Class to remember information about backtrackstatus. Triple of - State which is backtracked - max letter that
	 * needs to be backtracked - transitionletter chosen the last time after exploring this state
	 *
	 * @author tiloh
	 *
	 */
	public class BacktrackTriple {
		private final S mState;
		private final L mBacktrackLetter;
		private final L mTransitionLetter;

		public BacktrackTriple(final S state, final L backtrackLetter, final L transitionLetter) {
			mState = state;
			mBacktrackLetter = backtrackLetter;
			mTransitionLetter = transitionLetter;
		}
	}
}