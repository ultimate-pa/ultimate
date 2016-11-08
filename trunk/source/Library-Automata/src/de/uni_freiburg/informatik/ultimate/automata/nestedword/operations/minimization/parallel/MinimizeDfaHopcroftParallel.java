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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.parallel;

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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.AbstractMinimizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.util.Interrupt;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Class for minimize deterministic finite automaton by the Hopcroft -
 * Algorithm.
 * 
 * @author Layla Franke
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class MinimizeDfaHopcroftParallel<LETTER, STATE> extends AbstractMinimizeNwa<LETTER, STATE>
		implements IMinimize {
	/**
	 * True if Hopcroft algorithm shall help Incremental algorithm, false
	 * otherwise.
	 */
	public static final boolean HELP_INCREMENTAL = true;
	/**
	 * Boolean variable for determining to run the algorithm with or without
	 * producing tasks for parallel execution.
	 */
	private static boolean sParallel = false;
	
	/**
	 * Whether the result is constructed yet.
	 */
	private boolean mResultConstructed = false;
	/**
	 * ArrayList and HashMap for mapping STATE to integer and vice versa.
	 */
	private ArrayList<STATE> mInt2state;
	private HashMap<STATE, Integer> mState2int;
	
	/**
	 * Set keeping all partitions contained in the worklist.
	 */
	private Set<Block> mWorklist;
	/**
	 * Map that keeps mappings of states to blocks.
	 */
	private Map<Integer, Block> mMappings;
	/**
	 * ArrayList keeping all blocks for construction of result.
	 */
	private ArrayList<Block> mBlocks;
	/**
	 * Interrupt object. The algorithm terminates without the complete result if
	 * status is set to true.
	 */
	private Interrupt mInterrupt;
	
	/**
	 * map states to their representatives - needed for constructing result.
	 */
	private int[] mState2representative;
	
	/**
	 * String holding the cpu time.
	 */
	private double mRunTime;
	
	// ---- Variables and methods needed for parallel execution. ---- //
	/**
	 * Reference on task queue for enqueueing the produced tasks.
	 */
	private LinkedBlockingQueue<Runnable> mTaskQueue;
	/**
	 * Instance of the running instance of the incremental algorithm.
	 */
	private MinimizeDfaIncrementalParallel<LETTER, STATE> mIncrementalAlgorithm;
	/**
	 * This variable will be true as soon as the mappings of states to integer
	 * are entirely computed.
	 * <p>
	 * Christian: 2016-08-02: This variable is neither used nor changed.
	 */
	private final boolean mInitialized = false;
	
	// ---- Starting minimization ---- //
	
	/**
	 * GUI Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            input automaton (DFA)
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public MinimizeDfaHopcroftParallel(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand)
					throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, new Interrupt());
	}
	
	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            the input automaton
	 * @param interrupt
	 *            interrupt
	 */
	public MinimizeDfaHopcroftParallel(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final Interrupt interrupt) {
		super(services, stateFactory, "MinimizeDfaHopcroftParallel", operand);
		mInterrupt = interrupt;
		// Initialize final partition
		// mfinalPartition = Collections.synchronizedList(new
		// LinkedList<HashSet<Integer>>());
		
		/*
		 * Christian: 2016-08-02:
		 *   initialize() is also executed by executeAlgorithm().
		 */
		initialize();
		if (!sParallel) {
			executeAlgorithm();
		}
		assert (mState2int != null && mInt2state != null);
	}
	
	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            input automaton (DFA)
	 * @param interrupt
	 *            interrupt
	 */
	public MinimizeDfaHopcroftParallel(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final Interrupt interrupt, final ArrayList<STATE> int2state,
			final HashMap<STATE, Integer> state2int) {
		super(services, stateFactory, "MinimizeDfaHopcroftParallel", operand);
		mInterrupt = interrupt;
		mInt2state = int2state;
		mState2int = state2int;
		
		/*
		 * Christian: 2016-08-02:
		 *   initialize() is also executed by executeAlgorithm().
		 */
		initialize();
		assert (mState2int != null && mInt2state != null);
		if (!sParallel) {
			executeAlgorithm();
		}
	}
	
	/**
	 * This method is only called when the algorithm is executed non-parallel.
	 */
	private void executeAlgorithm() {
		assert ((mInterrupt == null)
				|| (!mInterrupt.getStatus())) : "HOP: The interrupt tells to terminate right at the beginning.";
		initialize();
		minimizeDfaHopcroft();
		if (!mResultConstructed) {
			constructResult();
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
		if (mState2int == null && mInt2state == null) {
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
			final MinimizeDfaIncrementalParallel<LETTER, STATE> incremental) {
			
		mTaskQueue = taskQueue;
		mIncrementalAlgorithm = incremental;
		minimizeDfaHopcroft();
	}
	
	/**
	 * Create and return initial partition for the given automaton.
	 * 
	 * @return Initialized partition.
	 */
	private void createInitialPartition() {
		// create new partition.
		mMappings = Collections.synchronizedMap(new HashMap<Integer, Block>());
		mWorklist = new HashSet<>();
		mBlocks = new ArrayList<>();
		final Collection<STATE> finalStatesCol = mOperand.getFinalStates();
		final Collection<STATE> statesCol = mOperand.getStates();
		
		final int nOfFinalStates = finalStatesCol.size();
		final int nOfStates = statesCol.size();
		
		final Block acceptingStates = new Block(new HashSet<Integer>(nOfFinalStates));
		final Block nonAcceptingStates = new Block(new HashSet<Integer>(nOfStates
				- nOfFinalStates));
				
		final Iterator<STATE> it = statesCol.iterator();
		while (it.hasNext()) {
			final STATE st = it.next();
			if (finalStatesCol.contains(st)) {
				mMappings.put(mState2int.get(st), acceptingStates);
				acceptingStates.add(mState2int.get(st));
			} else {
				mMappings.put(mState2int.get(st), nonAcceptingStates);
				nonAcceptingStates.add(mState2int.get(st));
			}
		}
		
		mWorklist.add(acceptingStates);
		mWorklist.add(nonAcceptingStates);
		
		// Add every new block. Blocks are never destroyed.
		mBlocks.add(acceptingStates);
		mBlocks.add(nonAcceptingStates);
	}
	
	/**
	 * Method for mapping STATE/LETTER to int and vice versa.
	 */
	private void initializeMappings() {
		
		final int nOfStates = mOperand.getStates().size();
		
		// Allocate the finite space in ArrayList and HashMap.
		mInt2state = new ArrayList<>(nOfStates);
		mState2int = new HashMap<>(
				computeHashCap(nOfStates));
				
		int index = -1;
		for (final STATE state : mOperand.getStates()) {
			mInt2state.add(state);
			mState2int.put(state, ++index);
		}
		
	}
	
	/**
	 * Minimize the input automaton using Hopcroft's algorithm.
	 */
	private void minimizeDfaHopcroft() {
		if (sParallel) {
			mLogger.info("HOP: started");
		}
		
		while (mWorklist.iterator().hasNext()) {
			if ((mInterrupt != null) && (mInterrupt.getStatus())) {
				return;
			}
			final Block currentBlock = mWorklist.iterator().next();
			mWorklist.remove(currentBlock);
			
			final HashSet<Integer> elem = currentBlock.getStates();
			
			for (final LETTER letter : mOperand.getInternalAlphabet()) {
				// Initialize Predecessors on letter.
				final Set<Integer> x = new HashSet<>();
				for (final int state : elem) {
					for (final IncomingInternalTransition<LETTER, STATE> transition : mOperand
							.internalPredecessors(mInt2state.get(state), letter)) {
						x.add(mState2int.get(transition.getPred()));
					}
				}
				
				if (x.isEmpty()) {
					continue;
				}
				// end initialization of X.
				
				// Find blocks
				final HashSet<Block> blocks = new HashSet<>();
				for (final Integer state : x) {
					final Block b = mMappings.get(state);
					if (b == null) {
						continue;
					}
					blocks.add(b);
					b.mark(state);
				}
				
				// test non-empty condition
				for (final Block b : blocks) {
					if (b.doSplit()) {
						
						final Block newBlock = b.split();
						
						// Remove singleton partitions.
						if (newBlock.getStates().size() == 1) {
							final int state = newBlock.getStates().iterator().next();
							mMappings.remove(state);
							// mfinalPartition.add(newBlock.getStates());
							if (b.getStates().size() == 1) {
								final int state2 = b.getStates().iterator().next();
								mMappings.remove(state2);
								// mfinalPartition.add(b.getStates());
							}
						} else {
							// Update Map.
							for (final int state : newBlock.getStates()) {
								mMappings.put(state, newBlock);
							}
						}
						
						// Create HelpIncremental
						if (sParallel && HELP_INCREMENTAL) {
							assert (mIncrementalAlgorithm != null);
							try {
								mTaskQueue.put(new HelpIncremental(
										mIncrementalAlgorithm,
										new HashSet<>(b.getStates()),
										new HashSet<>(newBlock
												.getStates())));
							} catch (final InterruptedException e) {
								e.printStackTrace();
							}
						}
						
						// Always add this because it is smaller.
						mWorklist.add(newBlock);
						mBlocks.add(newBlock);
						
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
	 */
	private void constructResult() {
		assert (!mResultConstructed);
		
		// mapping from states to their representative
		final HashMap<Integer, ? extends Collection<STATE>> state2equivStates = computeMapState2Equiv();
		
		// mapping from old state to new state
		final HashMap<Integer, STATE> oldState2newState = new HashMap<>(
				computeHashCap(state2equivStates.size()));
				
		// add states
		assert (mOperand.getInitialStates().iterator().hasNext()) : "There is no initial state in the automaton.";
		
		final int initRepresentative = mState2representative[mState2int
				.get(mOperand.getInitialStates().iterator().next())];
		startResultConstruction();
		for (final Entry<Integer, ? extends Collection<STATE>> entry : state2equivStates
				.entrySet()) {
			final int representative = entry.getKey();
			final Collection<STATE> equivStates = entry.getValue();
			final boolean isInitial = (representative == initRepresentative);
			assert equivStates.iterator().hasNext() : "There is no equivalent state in the collection.";
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
						oldState2newState
								.get(mState2representative[mState2int.get(out
										.getSucc())]));
			}
		}
		finishResultConstruction(null, false);
		mResultConstructed = true;
	}
	
	/**
	 * This method computes a mapping from old states to new representatives.
	 * 
	 * @return map old state -> new state
	 */
	private HashMap<Integer, ? extends Collection<STATE>> computeMapState2Equiv() {
		// Initialize mapping of states to their representatives.
		mState2representative = new int[mOperand.size()];
		final HashMap<Integer, LinkedList<STATE>> state2equivStates = new HashMap<>(
				computeHashCap(mOperand.size()));
				
		// Collection<Block> values = mpartitions.values();
		final HashSet<Block> blocks = new HashSet<>(mMappings.values());
		for (final Block b : blocks) {
			if (b.getStates().isEmpty()) {
				continue;
			}
			final int representative = b.getStates().iterator().next();
			final LinkedList<STATE> equivStates = new LinkedList<>();
			for (final int j : b.getStates()) {
				equivStates.add(mInt2state.get(j));
				mState2representative[j] = representative;
			}
			state2equivStates.put(representative, equivStates);
		}
		
		for (final Block elem : mBlocks) {
			final int representative = elem.getStates().iterator().next();
			final LinkedList<STATE> equivStates = new LinkedList<>();
			for (final int j : elem.getStates()) {
				equivStates.add(mInt2state.get(j));
				mState2representative[j] = representative;
			}
			state2equivStates.put(representative, equivStates);
			
		}
		return state2equivStates;
	}
	
	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		if (sParallel) {
			if (!mResultConstructed) {
				constructResult();
			}
		}
		return super.getResult();
	}
	
	/**
	 * @return The runtime for testing.
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
	 * Getter for parallel computation.
	 * 
	 * @return True if mappings have already been computed entirely, false
	 *         otherwise.
	 */
	public boolean getMappings() {
		return mInitialized;
	}
	
	/**
	 * Getter for mappings from integer to state.
	 * 
	 * @return state
	 */
	public ArrayList<STATE> getInt2State() {
		return mInt2state;
	}
	
	/**
	 * Getter for mappings from state to integer.
	 * 
	 * @return integer
	 */
	public HashMap<STATE, Integer> getState2Int() {
		return mState2int;
	}
	
	public void removePartition(final int state) {
		mMappings.remove(state);
	}
	
	public HashSet<Integer> getBlock(final int state) {
		return mMappings.get(state).getAll();
	}
	
	// --------------------------------------Subclass
	// Block--------------------------------------
	
	/**
	 * @author layla
	 */
	private static class Block {
		private static int sId = 0;
		private final int mId;
		
		/**
		 * Keeps all states that are important for one iteration.
		 */
		private HashSet<Integer> mMarked;
		/*
		 * Keeps all states from the beginning.
		 */
		private HashSet<Integer> mUnmarked;
		
		public Block(final HashSet<Integer> containedStates) {
			assert (containedStates != null);
			mUnmarked = containedStates;
			mMarked = new HashSet<>();
			mId = sId;
			sId++;
		}
		
		public void mark(final Integer state) {
			mMarked.add(state);
			mUnmarked.remove(state);
		}
		
		public void add(final Integer state) {
			mUnmarked.add(state);
		}
		
		public HashSet<Integer> getStates() {
			return mUnmarked;
		}
		
		public HashSet<Integer> getAll() {
			final HashSet<Integer> all = new HashSet<>(mUnmarked);
			all.addAll(mMarked);
			return all;
			
		}
		
		/**
		 * Call this method to determine whether to split a block.
		 * 
		 * @return true if the block should be split, false otherwise.
		 */
		public boolean doSplit() {
			return !mUnmarked.isEmpty();
		}
		
		public Block split() {
			if (mMarked.size() <= mUnmarked.size()) {
				final Block b = new Block(mMarked);
				mMarked = new HashSet<>();
				return b;
			} else {
				final Block b = new Block(mUnmarked);
				mUnmarked = mMarked;
				mMarked = new HashSet<>();
				return b;
			}
		}
		
		/**
		 * This function is only called if the block can not be split.
		 */
		public void reset() {
			assert (mUnmarked.isEmpty());
			mUnmarked = mMarked;
			mMarked = new HashSet<>();
		}
		
		@Override
		public boolean equals(final Object other) {
			if (other == null) {
				return false;
			}
			assert (this.getClass() == other.getClass());
			return mId == ((Block) other).mId;
		}
		
		@Override
		public int hashCode() {
			return this.mId;
		}
	}
	
}
