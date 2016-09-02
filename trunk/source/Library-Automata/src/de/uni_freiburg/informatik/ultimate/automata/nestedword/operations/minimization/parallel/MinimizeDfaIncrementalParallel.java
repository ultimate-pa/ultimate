/*
 * Copyright (C) 2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Layla Franke
 * Copyright (C) 2009-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.parallel;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map.Entry;
import java.util.Set;
import java.util.concurrent.LinkedBlockingQueue;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.AbstractMinimizeIncremental;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.util.Interrupt;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * This class implements the incremental DFA minimization algorithm by Almeida,
 * Moreira, and Reis ('Incremental DFA minimisation').
 * 
 * <p>The basic idea is to check equivalence of each pair of states exactly once
 * (with an order on the states even only once per two states, so
 * <code>q, q'</code> we either check as <code>(q, q')</code> or
 * <code>(q', q)</code>).
 * 
 * <p>Initially each state is not equivalent to all states that have a different
 * final status (<code>q !~ q' <=> (q in F <=> q' not in F)</code>). Also it is
 * clear that each state is equivalent to itself.
 * 
 * <p>If for a pair of states it is not clear whether they are equivalent, then the
 * they are equivalent if and only if all successor states (wrt. a symbol) are
 * equivalent, so we shift the task for one level. Loops are avoided by storing
 * the visited pairs.
 * 
 * <p>If the result was finally found for a pair of states, typically some more
 * pairs of states were investigated. If the answer was positive, all pairs of
 * states that were tested are equivalent. If the answer was negative, some
 * pairs of states were not equivalent. All those pairs are stored and the
 * information is then propagated to avoid checking these states later.
 * 
 * @author Layla Franke
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER> letter type
 * @param <STATE> state type
 */
public class MinimizeDfaIncrementalParallel<LETTER, STATE>
		extends AbstractMinimizeIncremental<LETTER, STATE>
		implements IMinimize, IOperation<LETTER, STATE> {
	/**
	 * The number of states in the input automaton (often used).
	 */
	private int mSize;
	/**
	 * The hash capacity for the number of pairs of states (often used).
	 */
	private int mHashCapNoTuples;
	/**
	 * Map state -> integer index.
	 */
	private HashMap<STATE, Integer> mState2int;
	/**
	 * Map integer index -> state.
	 */
	private ArrayList<STATE> mInt2state;
	/**
	 * Background array for the Union-Find data structure.
	 */
	private int[] mUnionFind;
	/**
	 * Potentially equivalent pairs of states.
	 */
	private SetList mEquiv;
	/**
	 * History of calls to the transition function.
	 */
	private SetList mPath;
	/**
	 * Set of pairs of states which are not equivalent.
	 */
	private Set<Tuple> mNeq;
	/**
	 * Stack for explicit version of recursive procedure.
	 */
	private ArrayDeque<StackElem> mStack;
	/**
	 * Blocking task queue for the parallel programm.
	 */

	/**
	 * True if Incremental algorithm shall help Hopcroft algorithm, false
	 * otherwise.
	 */
	public static final boolean HELP_HOPCROFT = true;

	/**
	 * Double holding the cpu time in seconds.
	 */
	private double mRunTime;

	// ---- Variables and methods needed for parallel execution. ---- //
	private LinkedBlockingQueue<Runnable> mTaskQueue;
	/**
	 * Hopcroft algorithm instance for parallel computation.
	 */
	private MinimizeDfaHopcroftParallel<LETTER, STATE> mHopcroftAlgorithm;
	/**
	 * Boolean variable for determining to run the algorithm with or without
	 * producing tasks for parallel execution.
	 */
	private static boolean sParallel = false;
	/**
	 * This variable will be true as soon as the union-find data structure is
	 * initialized.
	 */
	private boolean mInitialized = false;

	// ----------------------- options for tweaking ----------------------- //

	/**
	 * Option: Separate states with different transitions.
	 * 
	 * <p>That is, if there is a letter {@code l} where one of the states has an
	 * outgoing transitions with {@code l} and one has not (hence this
	 * transition would go to an implicit sink state.
	 * 
	 * <p>NOTE: This is only reasonable if the input automaton is not total.
	 * Furthermore, the method becomes incomplete (i.e., may not find the
	 * minimum) if dead ends have not been removed beforehand.
	 */
	private static final boolean OPTION_NEQ_TRANS = false;

	// --------------------------- class methods --------------------------- //

	/**
	 * GUI Constructor.
	 * 
	 * @param services Ultimate services
	 * @param stateFactory state factory
	 * @param operand
	 *            input automaton (DFA)
	 * @throws AutomataLibraryException
	 *             thrown when execution is cancelled
	 */
	public MinimizeDfaIncrementalParallel(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand)
			throws AutomataLibraryException {
		this(services, stateFactory, operand, new Interrupt());
	}

	/**
	 * Constructor.
	 * 
	 * @param services Ultimate services
	 * @param stateFactory state factory
	 * @param operand
	 *            input automaton (DFA)
	 * @param interrupt
	 *            interrupt
	 * @throws AutomataLibraryException
	 *             thrown when execution is cancelled
	 */
	public MinimizeDfaIncrementalParallel(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final Interrupt interrupt) throws AutomataLibraryException {
		super(services, stateFactory, "MinimizeAMR", operand, interrupt);
		
		/*
		 * Christian: 2016-08-02:
		 *   initialize() is also executed by executeAlgorithm().
		 */
		initialize();
		assert (mInt2state == null && mState2int == null);
		if (!sParallel) {
			executeAlgorithm();
		}
		assert (mInt2state != null && mState2int != null);
	}

	/**
	 * Constructor for given mappings.
	 * 
	 * @param services Ultimate services
	 * @param stateFactory state factory
	 * @param operand
	 *            input automaton (DFA)
	 * @param interrupt
	 *            interrupt
	 * @throws AutomataLibraryException
	 *             thrown by DFA check
	 */
	public MinimizeDfaIncrementalParallel(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final Interrupt interrupt, final ArrayList<STATE> int2state,
			final HashMap<STATE, Integer> state2int)
			throws AutomataLibraryException {
		super(services, stateFactory, "MinimizeAMR", operand, interrupt);
		mInt2state = int2state;
		mState2int = state2int;

		/*
		 * Christian: 2016-08-02:
		 *   initialize() is also executed by executeAlgorithm().
		 */
		initialize();
		assert (mInt2state != null && mState2int != null);
		if (!sParallel) {
			executeAlgorithm();
		}
	}

	/**
	 * Getter of runtime for testing.
	 */
	public double getRunTime() {
		return mRunTime;
	}

	/**
	 * Method for setting the flag before constructor is called.
	 * 
	 * @param parallel
	 *            True if MinimizeDfaParallel is called originally, false
	 *            otherwise.
	 */
	public static void setParallelFlag(final boolean parallel) {
		sParallel = parallel;
	}

	/**
	 * Getter for set of distinguishable tuples of states.
	 * 
	 * @return Set of tuples.
	 */
	public Set<Tuple> getNeq() {
		return mNeq;
	}

	/**
	 * Get state of this algorithm instance.
	 * 
	 * @return True if union-find data structure is initialized, false
	 *         otherwise.
	 */
	public boolean getInitialized() {
		return mInitialized;
	}

	/**
	 * This method is only executed if the algorithm is run non-parallel.
	 */
	private void executeAlgorithm() throws AutomataLibraryException {

		initialize();
		// Do time measurement
		// ThreadMXBean bean = ManagementFactory.getThreadMXBean();
		// mrunTime = bean.getThreadCpuTime(Thread.currentThread().getId())
		// / Math.pow(10, 9);
		// s_logger.info("Incremental CPU Time: " + mrunTime + "sec");
		mLogger.info(exitMessage());
	}

	private void initialize() throws AutomataLibraryException {

		assert super.isDfa() : "The input automaton is no DFA.";

		mSize = mOperand.size();
		assert (mSize >= 0) : "The automaton size must be nonnegative.";

		// trivial special cases
		if (mSize <= 1) {
			mUnionFind = null;
			mNeq = null;
			mEquiv = null;
			mPath = null;
			mStack = null;
			mHashCapNoTuples = 0;

			directResultConstruction(mOperand);
		} else {
			mUnionFind = new int[mSize];

			/*
			 * The maximum number of pairs of states without considering the
			 * order is (n^2 - n)/2.
			 * 
			 * This can easily be more than the maximum integer number. In that
			 * case the constant is set to this bound.
			 */
			int possibleOverflow = (mSize * (mSize - 1)) / 2;
			if (possibleOverflow > 0) {
				possibleOverflow = computeHashCap(possibleOverflow);
				if (possibleOverflow > 0) {
					mHashCapNoTuples = possibleOverflow;
				} else {
					mHashCapNoTuples = Integer.MAX_VALUE;
				}
			} else {
				mHashCapNoTuples = Integer.MAX_VALUE;
			}

			mNeq = Collections.synchronizedSet(new HashSet<Tuple>(
					mHashCapNoTuples));
			mEquiv = new SetList();
			mPath = new SetList();
			mStack = new ArrayDeque<StackElem>();

			if (mInt2state == null && mState2int == null) {
				mLogger.info("preprocessing");
				preprocess();
			}
			if (!sParallel) {
				// initialize data structures
				minimize();
			}
		}
	}

	protected void minimizeParallel(final LinkedBlockingQueue<Runnable> taskQueue,
			final MinimizeDfaHopcroftParallel<LETTER, STATE> hopcroft)
			throws AutomataLibraryException {
		mLogger.info("Inc: started");
		mTaskQueue = taskQueue;
		mHopcroftAlgorithm = hopcroft;
		findEquiv();
	}

	/**
	 * This method invokes the minimization process.
	 * 
	 * @throws AutomataOperationCanceledException
	 *             thrown when execution is cancelled
	 */
	private void minimize()
			throws AutomataLibraryException {

		// try minimization as long as possible
		findEquiv();

		constructResult();
	}

	/**
	 * This method makes the preprocessing step to map states to integers and
	 * vice versa.
	 */
	private void preprocess() {
		mState2int = new HashMap<STATE, Integer>(mSize);
		mInt2state = new ArrayList<STATE>(mSize);
		int i = -1;
		for (final STATE state : mOperand.getStates()) {
			mInt2state.add(state);

			assert (mState2int.get(state) == null) : "The state is already in the map.";
			mState2int.put(state, ++i);
		}

		assert ((mState2int.size() == mInt2state.size()) && (mState2int
				.size() == mSize)) : "The mappings do not have the same size as the input "
				+ "automaton";
	}

	/**
	 * This method is the main method of the minimization. As long as it runs,
	 * it finds for each pair of states whether they are equivalent or not.
	 * 
	 * <p>It terminates automatically, but can also be halted at any time.
	 * 
	 * <p>pseudocode name: MIN-INCR
	 */
	private void findEquiv() {
		// initialization
		initializeUnionFind();
		intializeTupleSet();

		// refinement loop
		for (int p = 0; p < mSize; ++p) {
			for (int q = p + 1; q < mSize; ++q) {
				// termination signal found
				if ((mInterrupt != null) && (mInterrupt.getStatus())) {
					return;
				}

				final Tuple tuple = new Tuple(p, q);

				// tuple was already found to be not equivalent
				if (mNeq.contains(tuple)) {
					continue;
				}

				// states have the same representative
				if (find(p) == find(q)) {
					continue;
				}

				// clean global sets
				mEquiv.clean();
				mPath.clean();

				// find out whether the states are equivalent or not
				final Iterator<Tuple> it;
				// the states are equivalent
				if (isPairEquiv(tuple)) {
					it = mEquiv.iterator();
					while (it.hasNext()) {
						union(it.next());
					}
					if (sParallel && HELP_HOPCROFT) {
						assert (mHopcroftAlgorithm != null);
						try {
							mTaskQueue.put(new HelpHopcroft(this,
									mHopcroftAlgorithm, tuple.mFirst,
									tuple.mSecond));
						} catch (final InterruptedException e) {
							e.printStackTrace();
						}
					}
				} else {
					// the states are not equivalent
					it = mPath.iterator();
					while (it.hasNext()) {
						mNeq.add(it.next());
					}
				}
			}
		}
	}

	/**
	 * This method initializes the set of pairs of states which are definitely
	 * not equivalent.
	 * 
	 * <p>The certain candidates are pairs where exactly one state is final.
	 * 
	 * <p>There is a global option for separating states with different outgoing
	 * transitions.
	 * 
	 * @return set of pairs of states not equivalent to each other
	 */
	private void intializeTupleSet() {
		// insert all pairs of states where one is final and one is not
		// TODO this is naive, think about a faster implementation
		for (int i = 0; i < mSize; ++i) {
			final STATE state1 = mInt2state.get(i);
			final boolean isFirstFinal = mOperand.isFinal(state1);

			for (int j = i + 1; j < mSize; ++j) {
				final STATE state2 = mInt2state.get(j);
				if (mOperand.isFinal(state2) ^ isFirstFinal) {
					mNeq.add(new Tuple(i, j));
				} else if (OPTION_NEQ_TRANS) {
					/*
					 * optional separation of states with different outgoing
					 * transitions
					 */
					final HashSet<LETTER> letters = new HashSet<LETTER>();
					for (final OutgoingInternalTransition<LETTER, STATE> out : mOperand
							.internalSuccessors(state1)) {
						letters.add(out.getLetter());
					}
					boolean broken = false;
					for (final OutgoingInternalTransition<LETTER, STATE> out : mOperand
							.internalSuccessors(state2)) {
						if (!letters.remove(out.getLetter())) {
							mNeq.add(new Tuple(i, j));
							broken = true;
							break;
						}
					}
					if (!(broken || letters.isEmpty())) {
						mNeq.add(new Tuple(i, j));
					}
				}
			}
		}
	}

	/**
	 * This method originally recursively calls itself to find out whether two
	 * states are equivalent. It uses the global set lists to store the paths it
	 * searched through.
	 * 
	 * <p>The recursion was transformed to an explicit form using a stack.
	 * 
	 * <p>pseudocode name: EQUIV-P
	 * 
	 * @param origTuple
	 *            tuple to check equivalence of
	 * @return true iff the pair of states is equivalent
	 */
	private boolean isPairEquiv(final Tuple origTuple) {
		assert (mStack.isEmpty()) : "The stack must be empty.";
		mStack.add(new StackElem(origTuple));

		// NOTE: This line was moved here for faster termination.
		mEquiv.add(origTuple);

		assert (!mStack.isEmpty()) : "The stack must not be empty.";
		do {
			final StackElem elem = mStack.peekLast();
			final Tuple eTuple = elem.mTuple;

			// already expanded: end of (explicit) recursion
			if (elem.mExpanded) {
				// take element from stack
				mStack.pollLast();

				// all successors and hence also this pair of states equivalent
				mPath.remove(eTuple);
				continue;
			} else {
				// not yet expanded: continue (explicit) recursion
				elem.mExpanded = true;

				// tuple was already found to be not equivalent
				if (mNeq.contains(eTuple)) {
					mStack.clear();
					return false;
				}

				/*
				 * tuple was already visited on the path, so the states are
				 * equivalent
				 */
				if (mPath.contains(eTuple)) {
					continue;
				}

				mPath.add(eTuple);

				if (!putSuccOnStack(eTuple)) {
					// one transition is only possible from one state
					mStack.clear();
					return false;
				}
			}
		} while (!mStack.isEmpty());

		// no witness was found why the states should not be equivalent
		// mequiv.add(origTuple); // NOTE: This line was moved upwards.
		return true;
	}

	/**
	 * This method handles the case of {@link #isPairEquiv(Tuple)} when
	 * the pair of states has not yet been expanded.
	 * 
	 * <p>It pushes the pairs of successor states on the stack.
	 * 
	 * <p>If the states have not been separated wrt. different outgoing transitions
	 * at the beginning, this is checked here and then possibly a reason for
	 * non-equivalence is found.
	 * 
	 * @param tuple
	 *            pair of states
	 * @return true iff no reason for non-equivalence was found
	 */
	private boolean putSuccOnStack(final Tuple tuple) {
		final STATE firstState = mInt2state.get(tuple.mFirst);
		final STATE secondState = mInt2state.get(tuple.mSecond);

		/*
		 * NOTE: This could be problematic with nondeterministic automata.
		 */
		for (final OutgoingInternalTransition<LETTER, STATE> out : mOperand
				.internalSuccessors(firstState)) {
			final LETTER letter = out.getLetter();
			assert (mOperand.internalSuccessors(secondState, letter) != null);

			int succQ;
			if (OPTION_NEQ_TRANS) {
				assert (mOperand.internalSuccessors(secondState, letter)
						.iterator().hasNext()) : "States with different outgoing transitions "
						+ "should have been marked as not equivalent.";

				succQ = find(mState2int.get(mOperand
						.internalSuccessors(secondState, letter).iterator()
						.next().getSucc()));
			} else {
				final Iterator<OutgoingInternalTransition<LETTER, STATE>> out2 = mOperand
						.internalSuccessors(secondState, letter).iterator();
				if (out2.hasNext()) {
					succQ = find(mState2int.get(out2.next().getSucc()));
				} else {
					return false;
				}
			}

			int succP = find(mState2int.get(out.getSucc()));
			if (succP != succQ) {
				if (succP > succQ) {
					final int tmp = succP;
					succP = succQ;
					succQ = tmp;
				}
				final Tuple successorTuple = new Tuple(succP, succQ);

				if (!mEquiv.contains(successorTuple)) {
					mEquiv.add(successorTuple);

					// break recursion: add to stack
					mStack.add(new StackElem(successorTuple));
				}
			}
		}

		if (!OPTION_NEQ_TRANS) {
			for (final OutgoingInternalTransition<LETTER, STATE> out : mOperand
					.internalSuccessors(secondState)) {
				if (!mOperand.internalSuccessors(firstState, out.getLetter())
						.iterator().hasNext()) {
					return false;
				}
			}
		}

		return true;
	}

	/**
	 * This method constructs the resulting automaton from the set of equivalent
	 * states.
	 */
	private void constructResult() {
		// mapping from states to their representative
		final HashMap<Integer, ? extends Collection<STATE>> state2equivStates = computeMapState2Equiv();

		// mapping from old state to new state
		final HashMap<Integer, STATE> oldState2newState = new HashMap<Integer, STATE>(
				computeHashCap(state2equivStates.size()));

		// add states
		assert (mOperand.getInitialStates().iterator().hasNext()) : "There is no initial state in the automaton.";
		final int initRepresentative = find(mState2int.get(mOperand
				.getInitialStates().iterator().next()));
		startResultConstruction();
		for (final Entry<Integer, ? extends Collection<STATE>> entry : state2equivStates
				.entrySet()) {
			final int representative = entry.getKey();
			final Collection<STATE> equivStates = entry.getValue();
			final boolean isInitial = (representative == initRepresentative);
			assert (equivStates.iterator().hasNext()) : "There is no equivalent state in the collection.";
			final boolean isFinal = mOperand.isFinal(equivStates.iterator().next());
			final STATE newSTate = addState(isInitial, isFinal, equivStates);
			oldState2newState.put(representative, newSTate);
		}

		/*
		 * add transitions
		 * 
		 * NOTE: This exploits the fact that the input is deterministic.
		 */
		for (final Integer oldStateInt : state2equivStates.keySet()) {
			for (final OutgoingInternalTransition<LETTER, STATE> out : mOperand
					.internalSuccessors(mInt2state.get(oldStateInt))) {
				addInternalTransition(
						oldState2newState.get(oldStateInt), out.getLetter(),
						oldState2newState.get(find(mState2int.get(out
								.getSucc()))));
			}
		}
		finishResultConstruction(null, false);
	}

	/**
	 * This method computes a mapping from old states to new representatives.
	 * 
	 * @return map old state -> new state
	 */
	private HashMap<Integer, ? extends Collection<STATE>> computeMapState2Equiv() {
		final HashMap<Integer, LinkedList<STATE>> state2equivStates = new HashMap<Integer, LinkedList<STATE>>(
				computeHashCap(mSize));
		for (int i = mSize - 1; i >= 0; --i) {
			final int representative = find(i);
			LinkedList<STATE> equivStates = state2equivStates
					.get(representative);
			if (equivStates == null) {
				equivStates = new LinkedList<STATE>();
				state2equivStates.put(representative, equivStates);
			}
			equivStates.add(mInt2state.get(i));
		}
		return state2equivStates;
	}

	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		if (sParallel) {
			constructResult();
		}
		return super.getResult();
	}

	// --------------------- Union-Find data structure --------------------- //

	/**
	 * This method initializes the Union-Find data structure.
	 * 
	 * <p>That is, each state points to itself.
	 * 
	 * <p>pseudocode name: MAKE in for-loop
	 */
	private void initializeUnionFind() {
		synchronized (mUnionFind) {
			for (int i = mUnionFind.length - 1; i >= 0; --i) {
				mUnionFind[i] = i;
				mInitialized = true;
			}
		}
	}

	/**
	 * This method implements the find operation of the Union-Find data
	 * structure.
	 * 
	 * <p>That is, the representative chain is searched and afterwards all
	 * intermediate representatives in this chain are updated accordingly for
	 * faster future find operations.
	 * 
	 * <p>pseudocode name: FIND
	 * 
	 * @param oldRepresentative
	 *            state
	 * @return representative of the given state
	 */
	public int find(int oldRepresentative) {
		final LinkedList<Integer> path = new LinkedList<Integer>();

		while (true) {
			int newRepresentative;
			synchronized (mUnionFind) {
				newRepresentative = mUnionFind[oldRepresentative];
			}

			// found the representative
			if (oldRepresentative == newRepresentative) {
				// update representative on the path
				synchronized (mUnionFind) {
					for (final int i : path) {
						mUnionFind[i] = newRepresentative;
					}
				}

				return newRepresentative;
			} else {
				path.add(oldRepresentative);
				oldRepresentative = newRepresentative;
			}
		}
	}

	/**
	 * This method implements the union operation of the Union-Find data
	 * structure.
	 * 
	 * <p>That is, the representative of the second state is set to the
	 * representative of the first state.
	 * 
	 * <p>NOTE: The find operation is used in order to safe one update later on.
	 * This way the direct representatives are certainly the true
	 * representatives.
	 * 
	 * <p>pseudocode name: UNION
	 * 
	 * @param tuple
	 *            pair of states that shall be united
	 */
	public void union(final Tuple tuple) {
		synchronized (mUnionFind) {
			mUnionFind[tuple.mSecond] = find(tuple.mFirst);
		}
	}

	// ------------------- auxiliary classes and methods ------------------- //

	/**
	 * This is a data structure containing a map and a list for fast operations
	 * on the data (tuples, i.e., pairs of states).
	 * 
	 * <p>The map holds pairs(tuple, list node), i.e., it maps a pair of states to
	 * the list node containing it. For iteration the list is used.
	 * 
	 * <p>Insertion and removal both work in {@code O(1)}. The problem here is that
	 * hash maps must be initialized and this takes time {@code O(size)}. Since
	 * {@code size} is in {@code O(n^2)} throughout the execution and the sets
	 * are repeatedly recreated, this comes with a big cost.
	 * 
	 * <p>To avoid this, the map is instead cleaned for all entries, which might
	 * hopefully be much less than all possible entries.
	 */
	private final class SetList {
		/**
		 * Map from state to list node.
		 */
		private HashMap<Tuple, ListNode> mMap;
		/**
		 * Doubly-linked list of states.
		 */
		private DoublyLinkedList mList;
		/**
		 * Flag that determines whether the map and list have been initialized.
		 */
		private boolean mIsInitialized;

		/**
		 * Constructor.
		 */
		public SetList() {
			mIsInitialized = false;
		}

		/**
		 * This method adds a pair of states.
		 * 
		 * <p>NOTE: The original pseudocode allows elements to be present
		 * beforehand and removes them first. That is avoided by this
		 * implementation.
		 * 
		 * <p>pseudocode name: SET-INSERT
		 * 
		 * @param tuple
		 *            pair of states
		 */
		void add(final Tuple tuple) {
			assert (!mMap.containsKey(tuple)) : "Elements should not be contained twice.";

			// insert new pair of states
			mMap.put(tuple, mList.add(tuple));
		}

		/**
		 * This method removes a pair of states.
		 * 
		 * <p>NOTE: The original pseudocode allows elements to not be present
		 * beforehand. That is avoided by this implementation.
		 * 
		 * <p>pseudocode name: SET-REMOVE
		 * 
		 * @param tuple
		 *            pair of states
		 */
		void remove(final Tuple tuple) {
			assert (mMap.containsKey(tuple)) : "Only elements contained should be removed.";

			// remove pair of states
			mList.remove(mMap.remove(tuple));
		}

		/**
		 * This method checks containment of a pair of states.
		 * 
		 * <p>pseudocode name: SET-SEARCH
		 * 
		 * @param tuple
		 *            pair of states
		 * @return true iff pair of states is contained
		 */
		boolean contains(final Tuple tuple) {
			return mMap.containsKey(tuple);
		}

		/**
		 * This method returns an iterator of all contained elements.
		 * 
		 * <p>pseudocode name: SET-ELEMENTS
		 * 
		 * @return iterator
		 */
		Iterator<Tuple> iterator() {
			return mList.iterator(mMap.size());
		}

		/**
		 * To avoid re-allocation of the whole memory (and default
		 * initialization), the map is instead cleaned for all entries in the
		 * list.
		 * 
		 * <p>pseudocode name: SET-MAKE
		 */
		void clean() {
			if (mIsInitialized) {
				final Iterator<Tuple> it = mList.iterator(mMap.size());
				while (it.hasNext()) {
					final Tuple t = it.next();
					assert (mMap.containsKey(t)) : "The element was not in the map: "
							+ t.toString();
					mMap.remove(t);
				}
				assert (mMap.size() == 0) : "There are elements left in the map after cleaning.";
			} else {
				mIsInitialized = true;
				mMap = new HashMap<Tuple, ListNode>(mHashCapNoTuples);
			}
			mList = new DoublyLinkedList();
		}

		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			builder.append("(");
			builder.append(mMap);
			builder.append(", ");
			builder.append(mList);
			builder.append(", ");
			builder.append(mIsInitialized);
			builder.append(")");
			return builder.toString();
		}

		/**
		 * This class represents a list node for the {@link DoublyLinkedList}.
		 */
		private final class ListNode {
			/**
			 * The contained pair of states.
			 */
			private final Tuple mTuple;
			/**
			 * Next list node.
			 */
			private ListNode mNext;
			/**
			 * Previous list node.
			 */
			private ListNode mPrev;

			/**
			 * Constructor.
			 * 
			 * @param tuple
			 *            pair of states
			 */
			public ListNode(final Tuple tuple, final ListNode prev,
					final ListNode next) {
				mTuple = tuple;
				mPrev = prev;
				mNext = next;
			}

			@Override
			public String toString() {
				return mTuple.toString();
			}
		}

		/**
		 * This class implements a simple doubly-linked list where the list
		 * nodes can be accessed. This is used to store them in a hash map for
		 * fast access.
		 */
		private final class DoublyLinkedList {
			/**
			 * First list node.
			 */
			private ListNode mFirst;
			/**
			 * Last list node.
			 */
			private ListNode mLast;

			/**
			 * Constructor.
			 */
			public DoublyLinkedList() {
				mFirst = null;
				mLast = null;
			}

			/**
			 * This method adds a new pair of states to the end of the list in
			 * {@code O(1)}.
			 * 
			 * @param tuple
			 *            pair of states
			 * @return the new list node
			 */
			ListNode add(final Tuple tuple) {
				assert (tuple != null) : "null should not be inserted in the list.";

				// first node
				if (mLast == null) {
					assert (mFirst == null) : "The last list element is null unexpectedly.";

					mFirst = new ListNode(tuple, null, null);
					mFirst.mPrev = mFirst;
					mFirst.mNext = mFirst;
					mLast = mFirst;
				} else {
					// further node
					assert (mFirst != null) : "The first list element is null unexpectedly.";

					final ListNode prev = mLast;
					mLast = new ListNode(tuple, prev, mFirst);
					prev.mNext = mLast;
					mFirst.mPrev = mLast;
				}

				// return new node
				return mLast;
			}

			/**
			 * This method removes a given list node in {@code O(1)}.
			 * 
			 * @param listNode list node
			 */
			void remove(final ListNode listNode) {
				assert (listNode != null) : "null cannot not be removed from the list.";

				// only node
				if (listNode.mNext == listNode) {
					mFirst = null;
					mLast = null;
				} else {
					// further node
					final ListNode prev = listNode.mPrev;
					final ListNode next = listNode.mNext;
					prev.mNext = next;
					next.mPrev = prev;

					if (listNode == mFirst) {
						mFirst = next;

						assert (listNode != mLast) : "The node must not be first and last element.";
					} else if (listNode == mLast) {
						mLast = prev;
					}
				}
			}

			/**
			 * This method returns an iterator of the list elements.
			 * 
			 * <p>NOTE: It is assumed that the list is not modified during
			 * iteration.
			 * 
			 * @param size
			 *            the size of the list (known by the set)
			 * @return iterator of list elements
			 */
			Iterator<Tuple> iterator(final int size) {
				return new Iterator<Tuple>() {
					/**
					 * Number of elements.
					 */
					private int mItSize = size;
					/**
					 * Next element.
					 */
					private ListNode mItNext = mLast;

					@Override
					public boolean hasNext() {
						return (mItSize > 0);
					}

					@Override
					public Tuple next() {
						assert (mItSize > 0) : "The next method must not be called when finished.";
						--mItSize;
						assert (mItNext != null) : "An empty list should not be asked for the next "
								+ "element.";
						mItNext = mItNext.mNext;
						assert (mItNext != null) : "An empty list should not be asked for the next "
								+ "element.";
						return mItNext.mTuple;
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException(
								"Removal is not supported.");
					}
				};
			}

			@Override
			public String toString() {
				final StringBuilder builder = new StringBuilder();
				builder.append("{");
				if (mFirst != null) {
					builder.append(mFirst.toString());
					ListNode node = mFirst.mNext;
					while (node != mFirst) {
						builder.append(", ");
						builder.append(node.toString());
						node = node.mNext;
					}
				}
				builder.append("}");
				return builder.toString();
			}
		}
	}

	/**
	 * This class represents an auxiliary wrapper for stack elements. An
	 * instance contains both a pair of states and a flag indicating whether
	 * this pair has already been investigated or not. The stack is used is to
	 * give an explicit version of the recursive procedure in the equivalence
	 * checking algorithm.
	 */
	private class StackElem {
		/**
		 * Pair of states.
		 */
		private final Tuple mTuple;
		/**
		 * True iff already visited.
		 */
		private boolean mExpanded;

		/**
		 * Constructor.
		 * 
		 * @param tuple
		 *            pair of states
		 */
		public StackElem(final Tuple tuple) {
			mTuple = tuple;
			mExpanded = false;
		}

		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			builder.append("(");
			builder.append(mTuple);
			builder.append(", ");
			builder.append(mExpanded);
			builder.append(")");
			return builder.toString();
		}
	}
}
