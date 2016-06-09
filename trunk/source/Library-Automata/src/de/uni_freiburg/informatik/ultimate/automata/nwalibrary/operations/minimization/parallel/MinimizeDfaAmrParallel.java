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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.parallel;

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
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.AMinimizeIncremental;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.Interrupt;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;

/**
 * This class implements the incremental DFA minimization algorithm by Almeida,
 * Moreira, and Reis ('Incremental DFA minimisation').
 * 
 * The basic idea is to check equivalence of each pair of states exactly once
 * (with an order on the states even only once per two states, so
 * <code>q, q'</code> we either check as <code>(q, q')</code> or
 * <code>(q', q)</code>).
 * 
 * Initially each state is not equivalent to all states that have a different
 * final status (<code>q !~ q' <=> (q in F <=> q' not in F)</code>). Also it is
 * clear that each state is equivalent to itself.
 * 
 * If for a pair of states it is not clear whether they are equivalent, then the
 * they are equivalent if and only if all successor states (wrt. a symbol) are
 * equivalent, so we shift the task for one level. Loops are avoided by storing
 * the visited pairs.
 * 
 * If the result was finally found for a pair of states, typically some more
 * pairs of states were investigated. If the answer was positive, all pairs of
 * states that were tested are equivalent. If the answer was negative, some
 * pairs of states were not equivalent. All those pairs are stored and the
 * information is then propagated to avoid checking these states later.
 * 
 * @author Christian
 */
public class MinimizeDfaAmrParallel<LETTER, STATE> extends
		AMinimizeIncremental<LETTER, STATE> implements IMinimize,
		IOperation<LETTER, STATE> {
	/**
	 * Service Provider.
	 */
	private final AutomataLibraryServices mServices;
	/**
	 * The result automaton.
	 */
	private INestedWordAutomaton<LETTER, STATE> mResult;
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
	public static boolean sHelpHopcroft = true;

	/**
	 * Double holding the cpu time in seconds.
	 */
	private double mRunTime;

	/**
	 * Getter of runtime for testing.
	 */
	public double getRunTime() {
		return mRunTime;
	}

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

	/**
	 * Method for setting the flag before constructor is called.
	 * 
	 * @param parallel
	 *            True if MinimizeDfaParallel is called originally, false
	 *            otherwise.
	 */
	public static void setParallelFlag(boolean parallel) {
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

	// ----------------------- options for tweaking ----------------------- //

	/**
	 * Option: Separate states with different transitions.
	 * 
	 * That is, if there is a letter {@code l} where one of the states has an
	 * outgoing transitions with {@code l} and one has not (hence this
	 * transition would go to an implicit sink state.
	 * 
	 * NOTE: This is only reasonable if the input automaton is not total.
	 * Furthermore, the method becomes incomplete (i.e., may not find the
	 * minimum) if dead ends have not been removed beforehand.
	 */
	private final boolean moptionNeqTrans = false;

	// --------------------------- class methods --------------------------- //

	/**
	 * GUI Constructor.
	 * 
	 * @param operand
	 *            input automaton (DFA)
	 * @throws AutomataOperationCanceledException
	 *             thrown when execution is cancelled
	 * @throws AutomataLibraryException
	 *             thrown by DFA check
	 */
	public MinimizeDfaAmrParallel(final AutomataLibraryServices services,
			final StateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand)
			throws AutomataLibraryException, AutomataLibraryException {
		this(services, stateFactory, operand, new Interrupt());
	}

	/**
	 * Constructor.
	 * 
	 * @param operand
	 *            input automaton (DFA)
	 * @param interrupt
	 *            interrupt
	 * @throws AutomataOperationCanceledException
	 *             thrown when execution is cancelled
	 * @throws AutomataLibraryException
	 *             thrown by DFA check
	 */
	public MinimizeDfaAmrParallel(final AutomataLibraryServices services,
			final StateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final Interrupt interrupt) throws AutomataLibraryException,
			AutomataLibraryException {
		super(services, stateFactory, "MinimizeAMR", operand, interrupt);
		mServices = services;
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
	 * @param operand
	 *            input automaton (DFA)
	 * @param interrupt
	 *            interrupt
	 * @throws AutomataOperationCanceledException
	 *             thrown when execution is cancelled
	 * @throws AutomataLibraryException
	 *             thrown by DFA check
	 */
	public MinimizeDfaAmrParallel(final AutomataLibraryServices services,
			final StateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final Interrupt interrupt, ArrayList<STATE> int2state,
			HashMap<STATE, Integer> state2int)
			throws AutomataOperationCanceledException, AutomataLibraryException {
		super(services, stateFactory, "MinimizeAMR", operand, interrupt);
		mServices = services;
		mInt2state = int2state;
		mState2int = state2int;
		initialize();
		assert (mInt2state != null && mState2int != null);
		if (!sParallel) {
			executeAlgorithm();
		}
	}

	/**
	 * This method is only executed if the algorithm is run non-parallel.
	 * 
	 * @throws AutomataLibraryException
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

		assert super.checkForDfa() : "The input automaton is no DFA.";

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

			mResult = mOperand;
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
				mResult = minimize();
			} else {
				mResult = new NestedWordAutomaton<>(mServices,
						mOperand.getInternalAlphabet(),
						mOperand.getCallAlphabet(),
						mOperand.getReturnAlphabet(),
						mOperand.getStateFactory());
			}
		}
	}

	public void minimizeParallel(final LinkedBlockingQueue<Runnable> taskQueue,
			final MinimizeDfaHopcroftParallel<LETTER, STATE> hopcroft)
			throws AutomataLibraryException {
		mLogger.info("Inc: " + startMessage());
		mTaskQueue = taskQueue;
		mHopcroftAlgorithm = hopcroft;
		findEquiv();
	}

	/**
	 * This method invokes the minimization process.
	 * 
	 * @return the minimal DFA
	 * @throws AutomataOperationCanceledException
	 *             thrown when execution is cancelled
	 */
	private INestedWordAutomaton<LETTER, STATE> minimize()
			throws AutomataLibraryException {

		// try minimization as long as possible
		findEquiv();

		return constructResult();
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
	 * It terminates automatically, but can also be halted at any time.
	 * 
	 * pseudocode name: MIN-INCR
	 */
	private void findEquiv() {
		// initialization
		initializeUnionFind();
		intializeTupleSet();

		// refinement loop
		for (int p = 0; p < mSize; ++p) {
			for (int q = p + 1; q < mSize; ++q) {
				if (minterrupt.getStatus()) {
					return;
				}

				// termination signal found
				if ((minterrupt != null) && (minterrupt.getStatus())) {
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
					if (sParallel && sHelpHopcroft) {
						assert (mHopcroftAlgorithm != null);
						try {
							mTaskQueue.put(new HelpHopcroft(this,
									mHopcroftAlgorithm, tuple.mfirst,
									tuple.msecond));
						} catch (final InterruptedException e) {
							e.printStackTrace();
						}
					}
				}
				// the states are not equivalent
				else {
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
	 * The certain candidates are pairs where exactly one state is final.
	 * 
	 * There is a global option for separating states with different outgoing
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
				}
				/*
				 * optional separation of states with different outgoing
				 * transitions
				 */
				else if (moptionNeqTrans) {
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
	 * The recursion was transformed to an explicit form using a stack.
	 * 
	 * 
	 * 
	 * pseudocode name: EQUIV-P
	 * 
	 * @param origTuple
	 *            tuple to check equivalence of
	 * @return true iff the pair of states is equivalent
	 */
	private boolean isPairEquiv(Tuple origTuple) {
		assert (mStack.size() == 0) : "The stack must be empty.";
		mStack.add(new StackElem(origTuple));

		// NOTE: This line was moved here for faster termination.
		mEquiv.add(origTuple);

		assert (!mStack.isEmpty()) : "The stack must not be empty.";
		do {
			final StackElem elem = mStack.peekLast();
			final Tuple eTuple = elem.mtuple;

			// already expanded: end of (explicit) recursion
			if (elem.mexpanded) {
				// take element from stack
				mStack.pollLast();

				// all successors and hence also this pair of states equivalent
				mPath.remove(eTuple);
				continue;
			}
			// not yet expanded: continue (explicit) recursion
			else {
				elem.mexpanded = true;

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
	 * This method handles the case of {@link isPairEquiv(Tuple origTuple)} when
	 * the pair of states has not yet been expanded.
	 * 
	 * It pushes the pairs of successor states on the stack.
	 * 
	 * If the states have not been separated wrt. different outgoing transitions
	 * at the beginning, this is checked here and then possibly a reason for
	 * non-equivalence is found.
	 * 
	 * @param tuple
	 *            pair of states
	 * @return true iff no reason for non-equivalence was found
	 */
	private boolean putSuccOnStack(final Tuple tuple) {
		final STATE firstState = mInt2state.get(tuple.mfirst);
		final STATE secondState = mInt2state.get(tuple.msecond);

		/*
		 * NOTE: This could be problematic with nondeterministic automata.
		 */
		for (final OutgoingInternalTransition<LETTER, STATE> out : mOperand
				.internalSuccessors(firstState)) {
			final LETTER letter = out.getLetter();
			assert (mOperand.internalSuccessors(secondState, letter) != null);

			int succP = find(mState2int.get(out.getSucc()));
			int succQ;

			if (moptionNeqTrans) {
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

		if (!moptionNeqTrans) {
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
	 * 
	 * @return resulting automaton where equivalent states are merged
	 */
	private INestedWordAutomaton<LETTER, STATE> constructResult() {
		// mapping from states to their representative
		final HashMap<Integer, ? extends Collection<STATE>> state2equivStates = computeMapState2Equiv();

		// construct result
		final StateFactory<STATE> stateFactory = mOperand.getStateFactory();
		final NestedWordAutomaton<LETTER, STATE> result = new NestedWordAutomaton<LETTER, STATE>(
				mServices, mOperand.getInternalAlphabet(),
				mOperand.getCallAlphabet(), mOperand.getReturnAlphabet(),
				stateFactory);

		// mapping from old state to new state
		final HashMap<Integer, STATE> oldState2newState = new HashMap<Integer, STATE>(
				computeHashCap(state2equivStates.size()));

		// add states
		assert (mOperand.getInitialStates().iterator().hasNext()) : "There is no initial state in the automaton.";
		final int initRepresentative = find(mState2int.get(mOperand
				.getInitialStates().iterator().next()));
		for (final Entry<Integer, ? extends Collection<STATE>> entry : state2equivStates
				.entrySet()) {
			final int representative = entry.getKey();
			final Collection<STATE> equivStates = entry.getValue();

			final STATE newSTate = stateFactory.minimize(equivStates);
			oldState2newState.put(representative, newSTate);

			assert (equivStates.iterator().hasNext()) : "There is no equivalent state in the collection.";
			result.addState((representative == initRepresentative),
					mOperand.isFinal(equivStates.iterator().next()), newSTate);
		}

		/*
		 * add transitions
		 * 
		 * NOTE: This exploits the fact that the input is deterministic.
		 */
		for (final Integer oldStateInt : state2equivStates.keySet()) {
			for (final OutgoingInternalTransition<LETTER, STATE> out : mOperand
					.internalSuccessors(mInt2state.get(oldStateInt))) {
				result.addInternalTransition(
						oldState2newState.get(oldStateInt), out.getLetter(),
						oldState2newState.get(find(mState2int.get(out
								.getSucc()))));
			}
		}

		return result;
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
	public INestedWordAutomatonSimple<LETTER, STATE> getResult() {
		if (sParallel) {
			mResult = constructResult();
		}
		return mResult;
	}

	// --------------------- Union-Find data structure --------------------- //

	/**
	 * This method initializes the Union-Find data structure.
	 * 
	 * That is, each state points to itself.
	 * 
	 * pseudocode name: MAKE in for-loop
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
	 * That is, the representative chain is searched and afterwards all
	 * intermediate representatives in this chain are updated accordingly for
	 * faster future find operations.
	 * 
	 * pseudocode name: FIND
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
	 * That is, the representative of the second state is set to the
	 * representative of the first state.
	 * 
	 * NOTE: The find operation is used in order to safe one update later on.
	 * This way the direct representatives are certainly the true
	 * representatives.
	 * 
	 * pseudocode name: UNION
	 * 
	 * @param tuple
	 *            pair of states that shall be united
	 */
	public void union(final Tuple tuple) {
		synchronized (mUnionFind) {
			mUnionFind[tuple.msecond] = find(tuple.mfirst);
		}
	}

	// ------------------- auxiliary classes and methods ------------------- //

	/**
	 * This is a data structure containing a map and a list for fast operations
	 * on the data (tuples, i.e., pairs of states).
	 * 
	 * The map holds pairs(tuple, list node), i.e., it maps a pair of states to
	 * the list node containing it. For iteration the list is used.
	 * 
	 * Insertion and removal both work in {@code O(1)}. The problem here is that
	 * hash maps must be initialized and this takes time {@code O(size)}. Since
	 * {@code size} is in {@code O(n^2)} throughout the execution and the sets
	 * are repeatedly recreated, this comes with a big cost.
	 * 
	 * To avoid this, the map is instead cleaned for all entries, which might
	 * hopefully be much less than all possible entries.
	 */
	private final class SetList {
		/**
		 * Map from state to list node.
		 */
		HashMap<Tuple, ListNode> mmap;
		/**
		 * Doubly-linked list of states.
		 */
		DoublyLinkedList mlist;
		/**
		 * Flag that determines whether the map and list have been initialized.
		 */
		boolean misInitialized;

		/**
		 * Constructor.
		 */
		public SetList() {
			misInitialized = false;
		}

		/**
		 * This method adds a pair of states.
		 * 
		 * NOTE: The original pseudocode allows elements to be present
		 * beforehand and removes them first. That is avoided by this
		 * implementation.
		 * 
		 * pseudocode name: SET-INSERT
		 * 
		 * @param tuple
		 *            pair of states
		 */
		void add(final Tuple tuple) {
			assert (!mmap.containsKey(tuple)) : "Elements should not be contained twice.";

			// insert new pair of states
			mmap.put(tuple, mlist.add(tuple));
		}

		/**
		 * This method removes a pair of states.
		 * 
		 * NOTE: The original pseudocode allows elements to not be present
		 * beforehand. That is avoided by this implementation.
		 * 
		 * pseudocode name: SET-REMOVE
		 * 
		 * @param tuple
		 *            pair of states
		 */
		void remove(final Tuple tuple) {
			assert (mmap.containsKey(tuple)) : "Only elements contained should be removed.";

			// remove pair of states
			mlist.remove(mmap.remove(tuple));
		}

		/**
		 * This method checks containment of a pair of states.
		 * 
		 * pseudocode name: SET-SEARCH
		 * 
		 * @param tuple
		 *            pair of states
		 * @return true iff pair of states is contained
		 */
		boolean contains(final Tuple tuple) {
			return mmap.containsKey(tuple);
		}

		/**
		 * This method returns an iterator of all contained elements.
		 * 
		 * pseudocode name: SET-ELEMENTS
		 * 
		 * @return iterator
		 */
		Iterator<Tuple> iterator() {
			return mlist.iterator(mmap.size());
		}

		/**
		 * To avoid re-allocation of the whole memory (and default
		 * initialization), the map is instead cleaned for all entries in the
		 * list.
		 * 
		 * pseudocode name: SET-MAKE
		 */
		void clean() {
			if (misInitialized) {
				final Iterator<Tuple> it = mlist.iterator(mmap.size());
				while (it.hasNext()) {
					final Tuple t = it.next();
					assert (mmap.containsKey(t)) : "The element was not in the map: "
							+ t.toString();
					mmap.remove(t);
				}
				assert (mmap.size() == 0) : "There are elements left in the map after cleaning.";
			} else {
				misInitialized = true;
				mmap = new HashMap<Tuple, ListNode>(mHashCapNoTuples);
			}
			mlist = new DoublyLinkedList();
		}

		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			builder.append("(");
			builder.append(mmap);
			builder.append(", ");
			builder.append(mlist);
			builder.append(", ");
			builder.append(misInitialized);
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
			final Tuple mtuple;
			/**
			 * Next list node.
			 */
			ListNode mnext;
			/**
			 * Previous list node.
			 */
			ListNode mprev;

			/**
			 * Constructor.
			 * 
			 * @param tuple
			 *            pair of states
			 */
			public ListNode(final Tuple tuple, final ListNode prev,
					final ListNode next) {
				mtuple = tuple;
				mprev = prev;
				mnext = next;
			}

			@Override
			public String toString() {
				return mtuple.toString();
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
			ListNode mfirst;
			/**
			 * Last list node.
			 */
			ListNode mlast;

			/**
			 * Constructor.
			 */
			public DoublyLinkedList() {
				mfirst = null;
				mlast = null;
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
				if (mlast == null) {
					assert (mfirst == null) : "The last list element is null unexpectedly.";

					mfirst = new ListNode(tuple, null, null);
					mfirst.mprev = mfirst;
					mfirst.mnext = mfirst;
					mlast = mfirst;
				}
				// further node
				else {
					assert (mfirst != null) : "The first list element is null unexpectedly.";

					final ListNode prev = mlast;
					mlast = new ListNode(tuple, prev, mfirst);
					prev.mnext = mlast;
					mfirst.mprev = mlast;
				}

				// return new node
				return mlast;
			}

			/**
			 * This method removes a given list node in {@code O(1)}.
			 * 
			 * @param listNode
			 */
			void remove(final ListNode listNode) {
				assert (listNode != null) : "null cannot not be removed from the list.";

				// only node
				if (listNode.mnext == listNode) {
					mfirst = null;
					mlast = null;
				}
				// further node
				else {
					final ListNode prev = listNode.mprev;
					final ListNode next = listNode.mnext;
					prev.mnext = next;
					next.mprev = prev;

					if (listNode == mfirst) {
						mfirst = next;

						assert (listNode != mlast) : "The node must not be first and last element.";
					} else if (listNode == mlast) {
						mlast = prev;
					}
				}
			}

			/**
			 * This method returns an iterator of the list elements.
			 * 
			 * NOTE: It is assumed that the list is not modified during
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
					int mitSize = size;
					/**
					 * Next element.
					 */
					ListNode mitNext = mlast;

					@Override
					public boolean hasNext() {
						return (mitSize > 0);
					}

					@Override
					public Tuple next() {
						assert (mitSize > 0) : "The next method must not be called when finished.";
						--mitSize;
						assert (mitNext != null) : "An empty list should not be asked for the next "
								+ "element.";
						mitNext = mitNext.mnext;
						assert (mitNext != null) : "An empty list should not be asked for the next "
								+ "element.";
						return mitNext.mtuple;
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
				if (mfirst != null) {
					builder.append(mfirst.toString());
					ListNode node = mfirst.mnext;
					while (node != mfirst) {
						builder.append(", ");
						builder.append(node.toString());
						node = node.mnext;
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
		final Tuple mtuple;
		/**
		 * True iff already visited.
		 */
		boolean mexpanded;

		/**
		 * Constructor.
		 * 
		 * @param tuple
		 *            pair of states
		 */
		public StackElem(Tuple tuple) {
			mtuple = tuple;
			mexpanded = false;
		}

		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			builder.append("(");
			builder.append(mtuple);
			builder.append(", ");
			builder.append(mexpanded);
			builder.append(")");
			return builder.toString();
		}
	}
}
