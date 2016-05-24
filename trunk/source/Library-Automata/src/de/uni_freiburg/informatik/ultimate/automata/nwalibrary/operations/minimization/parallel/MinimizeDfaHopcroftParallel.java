/*
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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.concurrent.LinkedBlockingQueue;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.AMinimizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.Interrupt;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;

/**
 * Class for minimize deterministic finite automaton by the Hopcroft -
 * Algorithm.
 * 
 * @author Layla Franke
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class MinimizeDfaHopcroftParallel<LETTER, STATE> extends
		AMinimizeNwa<LETTER, STATE> implements IMinimize,
		IOperation<LETTER, STATE> {
	/**
	 * Result automaton.
	 */
	private INestedWordAutomaton<LETTER, STATE> mresult;
	/**
	 * Input automaton.
	 */
	private final INestedWordAutomaton<LETTER, STATE> moperand;
	/**
	 * ArrayList and HashMap for mapping STATE to integer and vice versa.
	 */
	private ArrayList<STATE> mint2state;
	private HashMap<STATE, Integer> mstate2int;

	/**
	 * Set keeping all partitions contained in the worklist.
	 */
	private Set<Block> mworklist;
	/**
	 * Map that keeps mappings of states to blocks.
	 */
	private Map<Integer, Block> mmappings;
	/**
	 * ArrayList keeping all blocks for construction of result.
	 */
	private ArrayList<Block> mblocks;
	/**
	 * Interrupt object. The algorithm terminates without the complete result if
	 * status is set to true.
	 */
	private Interrupt minterrupt;

	/**
	 * map states to their representatives - needed for constructing result.
	 */
	private int[] mstate2representative;

	/**
	 * True if Hopcroft algorithm shall help Incremental algorithm, false
	 * otherwise.
	 */
	public static boolean HelpIncremental = true;

	/**
	 * String holding the cpu time.
	 */
	private double mrunTime;

	/**
	 * Getter of runtime string builder for testing.
	 */
	public double getRunTime() {
		return mrunTime;
	}

	// ---- Variables and methods needed for parallel execution. ---- //
	/**
	 * Boolean variable for determining to run the algorithm with or without
	 * producing tasks for parallel execution.
	 */
	private static boolean sParallel = false;
	/**
	 * Reference on task queue for enqueueing the produced tasks.
	 */
	private LinkedBlockingQueue<Runnable> mtaskQueue;
	/**
	 * Instance of the running instance of the incremental algorithm.
	 */
	private MinimizeDfaAmrParallel<LETTER, STATE> mincrementalAlgorithm;
	/**
	 * This variable will be true as soon as the mappings of states to integer
	 * are entirely computed.
	 */
	private boolean minitialized = false;

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
	 * Getter for parallel computation.
	 * 
	 * @return True if mappings have already been computed entirely, false
	 *         otherwise.
	 */
	public boolean getMappings() {
		return minitialized;
	}

	/**
	 * Getter for mappings from integer to state.
	 * 
	 * @return
	 */
	public ArrayList<STATE> getInt2State() {
		return mint2state;
	}

	/**
	 * Getter for mappings from state to integer.
	 * 
	 * @return
	 */
	public HashMap<STATE, Integer> getState2Int() {
		return mstate2int;
	}

	/**
	 * Getter for current partition of states.
	 * 
	 * @return
	 *
	 */
	public void removePartition(int state) {
		mmappings.remove(state);
	}

	public HashSet<Integer> getBlock(int state) {
		return mmappings.get(state).getAll();
	}

	// ---- Starting minimization ---- //

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
	public MinimizeDfaHopcroftParallel(final AutomataLibraryServices services,
			final StateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand)
			throws AutomataLibraryException, AutomataLibraryException {
		this(services, operand, new Interrupt());
	}

	/**
	 * Constructor.
	 * 
	 * @param operand
	 *            the input automaton
	 */
	public MinimizeDfaHopcroftParallel(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final Interrupt interrupt) {
		super(services, operand.getStateFactory(),
				"MinimizeDfaHopcroftParallel", operand);
		minterrupt = interrupt;
		this.moperand = operand;
		// Initialize final partition
		// mfinalPartition = Collections.synchronizedList(new
		// LinkedList<HashSet<Integer>>());
		initialize();
		if (!sParallel) {
			executeAlgorithm();
		}
		assert (mstate2int != null && mint2state != null);
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
	public MinimizeDfaHopcroftParallel(final AutomataLibraryServices services,
			final StateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final Interrupt interrupt, ArrayList<STATE> int2state,
			HashMap<STATE, Integer> state2int)
			throws AutomataOperationCanceledException, AutomataLibraryException {
		super(services, operand.getStateFactory(),
				"MinimizeDfaHopcroftParallel", operand);
		minterrupt = interrupt;
		this.moperand = operand;
		mint2state = int2state;
		mstate2int = state2int;
		initialize();
		assert (mstate2int != null && mint2state != null);
		if (!sParallel) {
			executeAlgorithm();
		}
	}

	/**
	 * This method is only called when the algorithm is executed non-parallel.
	 */
	private void executeAlgorithm() {
		assert ((minterrupt == null) || (!minterrupt.getStatus())) : "HOP: The interrupt tells to terminate right at the beginning.";
		initialize();
		minimizeDfaHopcroft();
		if (mresult == null) {
			mresult = constructResult();
		}
		// Do time measurement
		// ThreadMXBean bean = ManagementFactory.getThreadMXBean();
		// mrunTime = bean.getThreadCpuTime(Thread.currentThread().getId())
		// / Math.pow(10, 9);
		// s_logger.info("Hopcroft2 CPU Time: " + mrunTime + "sec");
		mLogger.info(exitMessage());

	}

	/**
	 * Initialize mappings and partition.
	 */
	private void initialize() {
		if (mstate2int == null && mint2state == null) {
			initializeMappings();
		}
		// Initialize partition.
		createInitialPartition();
	}

	/**
	 * Method for calling minimization without changing constructor.
	 * 
	 * @param taskQueue
	 *            The task queue for the parallel computation.
	 * @param incremental
	 *            The instance of the parallel algorithm.
	 */
	public void minimizeParallel(final LinkedBlockingQueue<Runnable> taskQueue,
			final MinimizeDfaAmrParallel<LETTER, STATE> incremental) {

		mtaskQueue = taskQueue;
		mincrementalAlgorithm = incremental;
		minimizeDfaHopcroft();
	}

	/**
	 * Create and return initial partition for the given automaton.
	 * 
	 * @return Initialized partition.
	 */
	private void createInitialPartition() {
		// create new partition.
		mmappings = Collections.synchronizedMap(new HashMap<Integer, Block>());
		mworklist = new HashSet<Block>();
		mblocks = new ArrayList<Block>();
		Collection<STATE> finalStatesCol = moperand.getFinalStates();
		Collection<STATE> statesCol = moperand.getStates();

		int nOfFinalStates = finalStatesCol.size();
		int nOfStates = statesCol.size();

		Block.ID = 0;
		Block acceptingStates = new Block(new HashSet<Integer>(nOfFinalStates));
		Block nonAcceptingStates = new Block(new HashSet<Integer>(nOfStates
				- nOfFinalStates));

		Iterator<STATE> it = statesCol.iterator();
		while (it.hasNext()) {
			STATE st = it.next();
			if (finalStatesCol.contains(st)) {
				mmappings.put(mstate2int.get(st), acceptingStates);
				acceptingStates.add(mstate2int.get(st));
			} else {
				mmappings.put(mstate2int.get(st), nonAcceptingStates);
				nonAcceptingStates.add(mstate2int.get(st));
			}
		}

		mworklist.add(acceptingStates);
		mworklist.add(nonAcceptingStates);

		// Add every new block. Blocks are never destroyed.
		mblocks.add(acceptingStates);
		mblocks.add(nonAcceptingStates);
	}

	/**
	 * Method for mapping STATE/LETTER to int and vice versa.
	 */
	private void initializeMappings() {

		int nOfStates = moperand.getStates().size();

		// Allocate the finite space in ArrayList and HashMap.
		mint2state = new ArrayList<STATE>(nOfStates);
		mstate2int = new HashMap<STATE, Integer>(
				computeHashMapCapacity(nOfStates));

		int index = -1;
		for (final STATE state : moperand.getStates()) {
			mint2state.add(state);
			mstate2int.put(state, ++index);
		}

	}

	/**
	 * Minimize the input automaton using Hopcroft's algorithm.
	 */
	private void minimizeDfaHopcroft() {
		if (sParallel) {
			mLogger.info("HOP: " + startMessage());
		}

		while (mworklist.iterator().hasNext()) {
			if ((minterrupt != null) && (minterrupt.getStatus())) {
				return;
			}
			Block currentBlock = mworklist.iterator().next();
			mworklist.remove(currentBlock);

			HashSet<Integer> elem = currentBlock.getStates();

			for (LETTER letter : moperand.getAlphabet()) {
				// Initialize Predecessors on letter.
				Set<Integer> x = new HashSet<Integer>();
				for (int state : elem) {
					for (IncomingInternalTransition<LETTER, STATE> transition : moperand
							.internalPredecessors(letter,
									mint2state.get(state))) {
						x.add(mstate2int.get(transition.getPred()));
					}
				}

				if (x.isEmpty()) {
					continue;
				}
				// end initialization of X.

				// Find blocks
				HashSet<Block> blocks = new HashSet<Block>();
				for (Integer state : x) {
					Block b = mmappings.get(state);
					if (b == null) {
						continue;
					}
					blocks.add(b);
					b.mark(state);
				}

				// test non-empty condition
				for (Block b : blocks) {
					if (b.doSplit()) {

						Block newBlock = b.split();

						// Remove singleton partitions.
						if (newBlock.getStates().size() == 1) {
							int state = newBlock.getStates().iterator().next();
							mmappings.remove(state);
							// mfinalPartition.add(newBlock.getStates());
							if (b.getStates().size() == 1) {
								int state2 = b.getStates().iterator().next();
								mmappings.remove(state2);
								// mfinalPartition.add(b.getStates());
							}
						} else {
							// Update Map.
							for (int state : newBlock.getStates()) {
								mmappings.put(state, newBlock);
							}
						}

						// Create HelpIncremental
						if (sParallel && HelpIncremental) {
							assert (mincrementalAlgorithm != null);
							try {
								mtaskQueue.put(new HelpIncremental(
										mincrementalAlgorithm,
										new HashSet<Integer>(b.getStates()),
										new HashSet<Integer>(newBlock
												.getStates())));
							} catch (InterruptedException e) {
								e.printStackTrace();
							}
						}

						// Always add this because it is smaller.
						mworklist.add(newBlock);
						mblocks.add(newBlock);

					} else {
						b.reset();
					}
				}
			}

		}

	}

	// ----------------------------ConstructResult-----------------------------

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
		final StateFactory<STATE> stateFactory = moperand.getStateFactory();
		NestedWordAutomaton<LETTER, STATE> result = new NestedWordAutomaton<LETTER, STATE>(
				mServices, moperand.getInternalAlphabet(),
				moperand.getCallAlphabet(), moperand.getReturnAlphabet(),
				stateFactory);

		// mapping from old state to new state
		final HashMap<Integer, STATE> oldState2newState = new HashMap<Integer, STATE>(
				computeHashCap(state2equivStates.size()));

		// add states
		assert (moperand.getInitialStates().iterator().hasNext()) : "There is no initial state in the automaton.";

		final int initRepresentative = mstate2representative[mstate2int
				.get(moperand.getInitialStates().iterator().next())];
		for (final Entry<Integer, ? extends Collection<STATE>> entry : state2equivStates
				.entrySet()) {
			final int representative = entry.getKey();
			final Collection<STATE> equivStates = entry.getValue();

			final STATE newSTate = stateFactory.minimize(equivStates);
			oldState2newState.put(representative, newSTate);

			assert (equivStates.iterator().hasNext()) : "There is no equivalent state in the collection.";
			result.addState((representative == initRepresentative),
					moperand.isFinal(equivStates.iterator().next()), newSTate);
		}

		/*
		 * add transitions
		 * 
		 * NOTE: This exploits the fact that the input is deterministic.
		 */
		for (final Integer oldStateInt : state2equivStates.keySet()) {
			for (final OutgoingInternalTransition<LETTER, STATE> out : moperand
					.internalSuccessors(mint2state.get(oldStateInt))) {
				result.addInternalTransition(
						oldState2newState.get(oldStateInt), out.getLetter(),
						oldState2newState
								.get(mstate2representative[mstate2int.get(out
										.getSucc())]));
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
		// Initialize mapping of states to their representatives.
		mstate2representative = new int[moperand.size()];
		final HashMap<Integer, LinkedList<STATE>> state2equivStates = new HashMap<Integer, LinkedList<STATE>>(
				computeHashCap(moperand.size()));

		// Collection<Block> values = mpartitions.values();
		HashSet<Block> blocks = new HashSet<Block>(mmappings.values());
		for (Block b : blocks) {
			if (b.getStates().isEmpty()) {
				continue;
			}
			final int representative = b.getStates().iterator().next();
			LinkedList<STATE> equivStates = new LinkedList<STATE>();
			for (int j : b.getStates()) {
				equivStates.add(mint2state.get(j));
				mstate2representative[j] = representative;
			}
			state2equivStates.put(representative, equivStates);
		}

		for (Block elem : mblocks) {
			final int representative = elem.getStates().iterator().next();
			LinkedList<STATE> equivStates = new LinkedList<STATE>();
			for (int j : elem.getStates()) {
				equivStates.add(mint2state.get(j));
				mstate2representative[j] = representative;
			}
			state2equivStates.put(representative, equivStates);

		}
		return state2equivStates;
	}

	/**
	 * computes the size of a hash Map to avoid rehashing this is only sensible
	 * if the maximum size is already known Java standard sets the load factor
	 * to 0.75
	 * 
	 * @param size
	 * @return hash map size
	 */
	private int computeHashMapCapacity(int size) {
		return (int) (size / 0.75 + 1);
	}

	@Override
	public INestedWordAutomatonSimple<LETTER, STATE> getResult() {
		if (sParallel) {
			if (mresult == null) {
				mresult = constructResult();
			}
		}
		return mresult;
	}

	// --------------------------------------Subclass
	// Block--------------------------------------

	/**
	 * 
	 * @author layla
	 *
	 */
	private static class Block {
		public static int ID = 0;
		private int mid;

		/**
		 * Keeps all states that are important for one iteration.
		 */
		private HashSet<Integer> mmarked;
		/*
		 * Keeps all states from the beginning.
		 */
		private HashSet<Integer> munmarked;

		public Block(final HashSet<Integer> containedStates) {
			assert (containedStates != null);
			munmarked = containedStates;
			mmarked = new HashSet<Integer>();
			mid = ID;
			ID++;
		}

		public void mark(Integer state) {
			mmarked.add(state);
			munmarked.remove(state);
		}

		public void add(Integer state) {
			munmarked.add(state);
		}

		public HashSet<Integer> getStates() {
			return munmarked;
		}

		public HashSet<Integer> getAll() {
			HashSet<Integer> all = new HashSet<Integer>(munmarked);
			all.addAll(mmarked);
			return all;

		}

		/**
		 * Call this method to determine whether to split a block
		 * 
		 * @return true if the block should be split, false otherwise.
		 */
		public boolean doSplit() {
			return munmarked.size() > 0;
		}

		public Block split() {
			if (mmarked.size() <= munmarked.size()) {
				Block b = new Block(mmarked);
				mmarked = new HashSet<Integer>();
				return b;
			} else {
				Block b = new Block(munmarked);
				munmarked = mmarked;
				mmarked = new HashSet<Integer>();
				return b;
			}
		}

		/**
		 * This function is only called if the block can not be split.
		 */
		public void reset() {
			assert (munmarked.size() == 0);
			munmarked = mmarked;
			mmarked = new HashSet<Integer>();
		}

		@Override
		public int hashCode() {
			return this.mid;
		}
	}

}
