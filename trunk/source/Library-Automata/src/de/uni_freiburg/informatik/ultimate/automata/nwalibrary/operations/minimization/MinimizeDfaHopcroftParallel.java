package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

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
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

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
	private INestedWordAutomaton<LETTER, STATE> m_result;
	/**
	 * Input automaton.
	 */
	private final INestedWordAutomaton<LETTER, STATE> m_operand;
	/**
	 * ArrayList and HashMap for mapping STATE to integer and vice versa.
	 */
	private ArrayList<STATE> m_int2state;
	private HashMap<STATE, Integer> m_state2int;

	/**
	 * Set keeping all partitions contained in the worklist.
	 */
	private Set<Block> m_worklist;
	/**
	 * Map that keeps mappings of states to blocks.
	 */
	private Map<Integer, Block> m_mappings;
	/**
	 * ArrayList keeping all blocks for construction of result.
	 */
	private ArrayList<Block> m_blocks;
	/**
	 * Interrupt object. The algorithm terminates without the complete result if
	 * status is set to true.
	 */
	private Interrupt m_interrupt;

	/**
	 * map states to their representatives - needed for constructing result.
	 */
	private int[] m_state2representative;

	/**
	 * True if Hopcroft algorithm shall help Incremental algorithm, false
	 * otherwise.
	 */
	public static boolean HelpIncremental = true;

	/**
	 * String holding the cpu time.
	 */
	private double m_runTime;

	/**
	 * Getter of runtime string builder for testing.
	 */
	public double getRunTime() {
		return m_runTime;
	}

	// ---- Variables and methods needed for parallel execution. ---- //
	/**
	 * Boolean variable for determining to run the algorithm with or without
	 * producing tasks for parallel execution.
	 */
	private static boolean s_parallel = false;
	/**
	 * Reference on task queue for enqueueing the produced tasks.
	 */
	private LinkedBlockingQueue<Runnable> m_taskQueue;
	/**
	 * Instance of the running instance of the incremental algorithm.
	 */
	private MinimizeDfaAmrParallel<LETTER, STATE> m_incrementalAlgorithm;
	/**
	 * This variable will be true as soon as the mappings of states to integer
	 * are entirely computed.
	 */
	private boolean m_initialized = false;

	/**
	 * Method for setting the flag before constructor is called.
	 * 
	 * @param parallel
	 *            True if MinimizeDfaParallel is called originally, false
	 *            otherwise.
	 */
	public static void setParallelFlag(boolean parallel) {
		s_parallel = parallel;
	}

	/**
	 * Getter for parallel computation.
	 * 
	 * @return True if mappings have already been computed entirely, false
	 *         otherwise.
	 */
	public boolean getMappings() {
		return m_initialized;
	}

	/**
	 * Getter for mappings from integer to state.
	 * 
	 * @return
	 */
	public ArrayList<STATE> getInt2State() {
		return m_int2state;
	}

	/**
	 * Getter for mappings from state to integer.
	 * 
	 * @return
	 */
	public HashMap<STATE, Integer> getState2Int() {
		return m_state2int;
	}

	/**
	 * Getter for current partition of states.
	 * 
	 * @return
	 *
	 */
	public void removePartition(int state) {
		m_mappings.remove(state);
	}

	public HashSet<Integer> getBlock(int state) {
		return m_mappings.get(state).getAll();
	}

	// ---- Starting minimization ---- //

	/**
	 * GUI Constructor.
	 * 
	 * @param operand
	 *            input automaton (DFA)
	 * @throws OperationCanceledException
	 *             thrown when execution is cancelled
	 * @throws AutomataLibraryException
	 *             thrown by DFA check
	 */
	public MinimizeDfaHopcroftParallel(final IUltimateServiceProvider services,
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
	public MinimizeDfaHopcroftParallel(final IUltimateServiceProvider services,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final Interrupt interrupt) {
		super(services, operand.getStateFactory(),
				"MinimizeDfaHopcroftParallel", operand);
		m_interrupt = interrupt;
		this.m_operand = operand;
		// Initialize final partition
		// m_finalPartition = Collections.synchronizedList(new
		// LinkedList<HashSet<Integer>>());
		initialize();
		if (!s_parallel) {
			executeAlgorithm();
		}
		assert (m_state2int != null && m_int2state != null);
	}

	/**
	 * Constructor.
	 * 
	 * @param operand
	 *            input automaton (DFA)
	 * @param interrupt
	 *            interrupt
	 * @throws OperationCanceledException
	 *             thrown when execution is cancelled
	 * @throws AutomataLibraryException
	 *             thrown by DFA check
	 */
	public MinimizeDfaHopcroftParallel(final IUltimateServiceProvider services,
			final StateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final Interrupt interrupt, ArrayList<STATE> int2state,
			HashMap<STATE, Integer> state2int)
			throws OperationCanceledException, AutomataLibraryException {
		super(services, operand.getStateFactory(),
				"MinimizeDfaHopcroftParallel", operand);
		m_interrupt = interrupt;
		this.m_operand = operand;
		m_int2state = int2state;
		m_state2int = state2int;
		initialize();
		assert (m_state2int != null && m_int2state != null);
		if (!s_parallel) {
			executeAlgorithm();
		}
	}

	/**
	 * This method is only called when the algorithm is executed non-parallel.
	 */
	private void executeAlgorithm() {
		assert ((m_interrupt == null) || (!m_interrupt.getStatus())) : "HOP: The interrupt tells to terminate right at the beginning.";
		initialize();
		minimizeDfaHopcroft();
		if (m_result == null) {
			m_result = constructResult();
		}
		// Do time measurement
		// ThreadMXBean bean = ManagementFactory.getThreadMXBean();
		// m_runTime = bean.getThreadCpuTime(Thread.currentThread().getId())
		// / Math.pow(10, 9);
		// s_logger.info("Hopcroft2 CPU Time: " + m_runTime + "sec");
		s_logger.info(exitMessage());

	}

	/**
	 * Initialize mappings and partition.
	 */
	private void initialize() {
		if (m_state2int == null && m_int2state == null) {
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

		m_taskQueue = taskQueue;
		m_incrementalAlgorithm = incremental;
		minimizeDfaHopcroft();
	}

	/**
	 * Create and return initial partition for the given automaton.
	 * 
	 * @return Initialized partition.
	 */
	private void createInitialPartition() {
		// create new partition.
		m_mappings = Collections.synchronizedMap(new HashMap<Integer, Block>());
		m_worklist = new HashSet<Block>();
		m_blocks = new ArrayList<Block>();
		Collection<STATE> finalStatesCol = m_operand.getFinalStates();
		Collection<STATE> statesCol = m_operand.getStates();

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
				m_mappings.put(m_state2int.get(st), acceptingStates);
				acceptingStates.add(m_state2int.get(st));
			} else {
				m_mappings.put(m_state2int.get(st), nonAcceptingStates);
				nonAcceptingStates.add(m_state2int.get(st));
			}
		}

		m_worklist.add(acceptingStates);
		m_worklist.add(nonAcceptingStates);

		// Add every new block. Blocks are never destroyed.
		m_blocks.add(acceptingStates);
		m_blocks.add(nonAcceptingStates);
	}

	/**
	 * Method for mapping STATE/LETTER to int and vice versa.
	 */
	private void initializeMappings() {

		int nOfStates = m_operand.getStates().size();

		// Allocate the finite space in ArrayList and HashMap.
		m_int2state = new ArrayList<STATE>(nOfStates);
		m_state2int = new HashMap<STATE, Integer>(
				computeHashMapCapacity(nOfStates));

		int index = -1;
		for (final STATE state : m_operand.getStates()) {
			m_int2state.add(state);
			m_state2int.put(state, ++index);
		}

	}

	/**
	 * Minimize the input automaton using Hopcroft's algorithm.
	 */
	private void minimizeDfaHopcroft() {
		if (s_parallel) {
			s_logger.info("HOP: " + startMessage());
		}

		while (m_worklist.iterator().hasNext()) {
			if ((m_interrupt != null) && (m_interrupt.getStatus())) {
				return;
			}
			Block currentBlock = m_worklist.iterator().next();
			m_worklist.remove(currentBlock);

			HashSet<Integer> elem = currentBlock.getStates();

			for (LETTER letter : m_operand.getAlphabet()) {
				// Initialize Predecessors on letter.
				Set<Integer> x = new HashSet<Integer>();
				for (int state : elem) {
					for (IncomingInternalTransition<LETTER, STATE> transition : m_operand
							.internalPredecessors(letter,
									m_int2state.get(state))) {
						x.add(m_state2int.get(transition.getPred()));
					}
				}

				if (x.isEmpty()) {
					continue;
				}
				// end initialization of X.

				// Find blocks
				HashSet<Block> blocks = new HashSet<Block>();
				for (Integer state : x) {
					Block b = m_mappings.get(state);
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
							m_mappings.remove(state);
							// m_finalPartition.add(newBlock.getStates());
							if (b.getStates().size() == 1) {
								int state2 = b.getStates().iterator().next();
								m_mappings.remove(state2);
								// m_finalPartition.add(b.getStates());
							}
						} else {
							// Update Map.
							for (int state : newBlock.getStates()) {
								m_mappings.put(state, newBlock);
							}
						}

						// Create HelpIncremental
						if (s_parallel && HelpIncremental) {
							assert (m_incrementalAlgorithm != null);
							try {
								m_taskQueue.put(new HelpIncremental(
										m_incrementalAlgorithm,
										new HashSet<Integer>(b.getStates()),
										new HashSet<Integer>(newBlock
												.getStates())));
							} catch (InterruptedException e) {
								e.printStackTrace();
							}
						}

						// Always add this because it is smaller.
						m_worklist.add(newBlock);
						m_blocks.add(newBlock);

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
		final StateFactory<STATE> stateFactory = m_operand.getStateFactory();
		NestedWordAutomaton<LETTER, STATE> result = new NestedWordAutomaton<LETTER, STATE>(
				m_Services, m_operand.getInternalAlphabet(),
				m_operand.getCallAlphabet(), m_operand.getReturnAlphabet(),
				stateFactory);

		// mapping from old state to new state
		final HashMap<Integer, STATE> oldState2newState = new HashMap<Integer, STATE>(
				computeHashCap(state2equivStates.size()));

		// add states
		assert (m_operand.getInitialStates().iterator().hasNext()) : "There is no initial state in the automaton.";

		final int initRepresentative = m_state2representative[m_state2int
				.get(m_operand.getInitialStates().iterator().next())];
		for (final Entry<Integer, ? extends Collection<STATE>> entry : state2equivStates
				.entrySet()) {
			final int representative = entry.getKey();
			final Collection<STATE> equivStates = entry.getValue();

			final STATE newSTate = stateFactory.minimize(equivStates);
			oldState2newState.put(representative, newSTate);

			assert (equivStates.iterator().hasNext()) : "There is no equivalent state in the collection.";
			result.addState((representative == initRepresentative),
					m_operand.isFinal(equivStates.iterator().next()), newSTate);
		}

		/*
		 * add transitions
		 * 
		 * NOTE: This exploits the fact that the input is deterministic.
		 */
		for (final Integer oldStateInt : state2equivStates.keySet()) {
			for (final OutgoingInternalTransition<LETTER, STATE> out : m_operand
					.internalSuccessors(m_int2state.get(oldStateInt))) {
				result.addInternalTransition(
						oldState2newState.get(oldStateInt), out.getLetter(),
						oldState2newState
								.get(m_state2representative[m_state2int.get(out
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
		m_state2representative = new int[m_operand.size()];
		final HashMap<Integer, LinkedList<STATE>> state2equivStates = new HashMap<Integer, LinkedList<STATE>>(
				computeHashCap(m_operand.size()));

		// Collection<Block> values = m_partitions.values();
		HashSet<Block> blocks = new HashSet<Block>(m_mappings.values());
		for (Block b : blocks) {
			if (b.getStates().isEmpty()) {
				continue;
			}
			final int representative = b.getStates().iterator().next();
			LinkedList<STATE> equivStates = new LinkedList<STATE>();
			for (int j : b.getStates()) {
				equivStates.add(m_int2state.get(j));
				m_state2representative[j] = representative;
			}
			state2equivStates.put(representative, equivStates);
		}

		for (Block elem : m_blocks) {
			final int representative = elem.getStates().iterator().next();
			LinkedList<STATE> equivStates = new LinkedList<STATE>();
			for (int j : elem.getStates()) {
				equivStates.add(m_int2state.get(j));
				m_state2representative[j] = representative;
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
		if (s_parallel) {
			if (m_result == null) {
				m_result = constructResult();
			}
		}
		return m_result;
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
		private int m_id;

		/**
		 * Keeps all states that are important for one iteration.
		 */
		private HashSet<Integer> m_marked;
		/*
		 * Keeps all states from the beginning.
		 */
		private HashSet<Integer> m_unmarked;

		public Block(final HashSet<Integer> containedStates) {
			assert (containedStates != null);
			m_unmarked = containedStates;
			m_marked = new HashSet<Integer>();
			m_id = ID;
			ID++;
		}

		public void mark(Integer state) {
			m_marked.add(state);
			m_unmarked.remove(state);
		}

		public void add(Integer state) {
			m_unmarked.add(state);
		}

		public HashSet<Integer> getStates() {
			return m_unmarked;
		}

		public HashSet<Integer> getAll() {
			HashSet<Integer> all = new HashSet<Integer>(m_unmarked);
			all.addAll(m_marked);
			return all;

		}

		/**
		 * Call this method to determine whether to split a block
		 * 
		 * @return true if the block should be split, false otherwise.
		 */
		public boolean doSplit() {
			return m_unmarked.size() > 0;
		}

		public Block split() {
			if (m_marked.size() <= m_unmarked.size()) {
				Block b = new Block(m_marked);
				m_marked = new HashSet<Integer>();
				return b;
			} else {
				Block b = new Block(m_unmarked);
				m_unmarked = m_marked;
				m_marked = new HashSet<Integer>();
				return b;
			}
		}

		/**
		 * This function is only called if the block can not be split.
		 */
		public void reset() {
			assert (m_unmarked.size() == 0);
			m_unmarked = m_marked;
			m_marked = new HashSet<Integer>();
		}

		@Override
		public int hashCode() {
			return this.m_id;
		}
	}

}
