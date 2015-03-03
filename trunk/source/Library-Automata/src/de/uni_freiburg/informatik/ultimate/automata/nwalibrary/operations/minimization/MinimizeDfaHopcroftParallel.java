package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.LinkedBlockingQueue;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
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
	 * Logger for debug - information.
	 */
	private static final Logger s_logger = NestedWordAutomata.getLogger();
	/**
	 * Service Provider.
	 */
	private final IUltimateServiceProvider m_services;
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
	 * Worklist.
	 */
	private Queue<ArrayList<Integer>> m_worklist;
	/**
	 * Partition of sets of states.
	 */
	private Queue<ArrayList<Integer>> m_partition;
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
	 * Partition of sets of states where all are in the same equivalence class
	 * already.
	 */
	private final Queue<ArrayList<Integer>> m_finalPartition;
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
	 */
	public Queue<ArrayList<Integer>> getSetList() {
		return m_partition;
	}

	/**
	 * Getter for partition of states that are already minimal.
	 * 
	 * @return
	 */
	public Queue<ArrayList<Integer>> getFinalPartitions() {
		return m_finalPartition;
	}

	// ---- Starting minimization ---- //
	/**
	 * Constructor.
	 * 
	 * @param operand
	 *            the input automaton
	 */
	public MinimizeDfaHopcroftParallel(
			final IUltimateServiceProvider services,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final Interrupt interrupt) {
		super(services, operand.getStateFactory(),
				"MinimizeDfaHopcroftParallel", operand);
		m_services = services;
		m_interrupt = interrupt;
		this.m_operand = operand;
		// Initialize final partition
		m_finalPartition = new LinkedList<ArrayList<Integer>>();
		initialize();
		assert (m_state2int == null && m_int2state == null);
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
	public MinimizeDfaHopcroftParallel(
			final IUltimateServiceProvider services,
			final StateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final Interrupt interrupt, ArrayList<STATE> int2state,
			HashMap<STATE, Integer> state2int)
			throws OperationCanceledException, AutomataLibraryException {
		super(services, operand.getStateFactory(),
				"MinimizeDfaHopcroftParallel", operand);
		m_services = services;
		m_interrupt = interrupt;
		this.m_operand = operand;
		// Initialize final partition
		m_finalPartition = new LinkedList<ArrayList<Integer>>();
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
		m_result = constructResult();
		// Do time measurement
		ThreadMXBean bean = ManagementFactory.getThreadMXBean();
		m_runTime = bean.getThreadCpuTime(Thread.currentThread().getId())
				/ Math.pow(10, 9);
		s_logger.info("Hopcroft2 CPU Time: " + m_runTime + "sec");
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
		m_partition = new LinkedList<ArrayList<Integer>>();
		Collection<STATE> finalStatesCol = m_operand.getFinalStates();
		Collection<STATE> statesCol = m_operand.getStates();

		int nOfFinalStates = finalStatesCol.size();
		int nOfStates = statesCol.size();

		ArrayList<Integer> finalStates = new ArrayList<Integer>(nOfFinalStates);
		ArrayList<Integer> nonfinalStates = new ArrayList<Integer>(nOfStates
				- nOfFinalStates);

		Iterator<STATE> it = statesCol.iterator();
		while (it.hasNext()) {
			STATE st = it.next();
			if (finalStatesCol.contains(st)) {
				finalStates.add(m_state2int.get(st));
			} else {
				nonfinalStates.add(m_state2int.get(st));
			}
		}

		synchronized (m_partition) {
			m_partition.add(finalStates);
			m_partition.add(nonfinalStates);
			m_partition.add(null);
		}
		m_worklist = new LinkedList<ArrayList<Integer>>();
		m_worklist.add(finalStates);
		// TODO Check whether automaton is total?
		m_worklist.add(nonfinalStates);
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
	 * Initialize structure for lables. Iterate over all states and get their
	 * OutgoingInternalTransition<LETTER, STATE> for storing nOfLabel,
	 * headOfLabel and tailOfLabel.
	 */
	/*
	 * private void initializeLables() { int nOfLables =
	 * m_operand.getInternalAlphabet().size(); m_int2letter = new
	 * ArrayList<LETTER>(nOfLables); m_letter2int = new HashMap<LETTER,
	 * Integer>( computeHashMapCapacity(nOfLables));
	 * 
	 * int index = -1; for (final LETTER letter : m_operand.getAlphabet()) {
	 * m_int2letter.add(letter); m_letter2int.put(letter, ++index); }
	 * 
	 * int capacity = (int) Math.min((double) Integer.MAX_VALUE, (double)
	 * m_operand.size() * m_operand.size() m_operand.getAlphabet().size());
	 * m_labels = new int[capacity]; m_labelTails = new int[capacity];
	 * m_labelHeads = new int[capacity]; // Contains arrays of [state_int,
	 * firstIndex, numOfIndexes] m_mapStatesToTransitionTails = new
	 * ArrayList<int[]>();
	 * 
	 * // Iterate over all states in m_int2state. index = 0; for (int i = 0; i <
	 * m_int2state.size(); ++i) { STATE st = m_int2state.get(i); // Get outgoing
	 * transition. Iterator<OutgoingInternalTransition<LETTER, STATE>> it =
	 * m_operand .internalSuccessors(st).iterator(); // hasNext? --> add to
	 * labels. int count = 0; while (it.hasNext()) {
	 * OutgoingInternalTransition<LETTER, STATE> oit = it.next();
	 * m_labels[index] = m_letter2int.get(oit.getLetter()); m_labelTails[index]
	 * = m_state2int.get(st); m_labelHeads[index] =
	 * m_state2int.get(oit.getSucc()); index++; count++; } int[] map = new int[]
	 * { i, index - count, count }; m_mapStatesToTransitionTails.add(map); }
	 * m_nOfTransitions = index; // resize arrays to used size for saving memory
	 * // Maybe too much computing time? m_labels = Arrays.copyOf(m_labels,
	 * m_nOfTransitions); m_labelTails = Arrays.copyOf(m_labelTails,
	 * m_nOfTransitions); m_labelHeads = Arrays.copyOf(m_labelHeads,
	 * m_nOfTransitions); }
	 */
	/**
	 * Minimize the input automaton using Hopcroft's algorithm.
	 */
	private void minimizeDfaHopcroft() {
		if (s_parallel) {
			s_logger.info("HOP: " + startMessage());
		}
		while (!m_worklist.isEmpty()) {
			// TODO Right spot
			if ((m_interrupt != null) && (m_interrupt.getStatus())) {
				return;
			}
			ArrayList<Integer> elem = m_worklist.remove();
			for (LETTER letter : m_operand.getAlphabet()) {
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
				ArrayList<Integer> y;
				while (true) {
					synchronized (m_partition) {
						y = m_partition.poll();
						if (y == null) {
							m_partition.add(y);
							break;
						}
					}

					// TODO Right spot?
					if ((m_interrupt != null) && (m_interrupt.getStatus())) {
						return;
					}

					// test condition on y
					ArrayList<Integer> intersection = new ArrayList<Integer>(y);
					intersection.retainAll(x);
					ArrayList<Integer> complement = new ArrayList<Integer>(y);
					complement.removeAll(x);
					if (!intersection.isEmpty() && !complement.isEmpty()) {
						synchronized (m_partition) {
							// Remove singleton sets from partition.
							if (intersection.size() > 1) {
								m_partition.add(intersection);
							} else {
								m_finalPartition.add(intersection);
							}
							if (complement.size() > 1) {
								m_partition.add(complement);
							} else {
								m_finalPartition.add(complement);
							}
						}
						// Partition was split up. Create helper thread.
						if (s_parallel && HelpIncremental) {
							assert (m_incrementalAlgorithm != null);
							try {
								m_taskQueue.put(new HelpIncremental(
										m_incrementalAlgorithm, intersection,
										complement));
							} catch (InterruptedException e) {
								// TODO Auto-generated catch block
								e.printStackTrace();
							}
						}

						// Change worklist.
						if (m_worklist.contains(y)) {
							m_worklist.remove(y);
							m_worklist.add(intersection);
							m_worklist.add(complement);
						} else {
							if (intersection.size() <= complement.size()) {
								m_worklist.add(intersection);
							} else {
								m_worklist.add(complement);
							}
						}
					} else {
						synchronized (m_partition) {
							m_partition.add(y);
						}
					}
				}

			}
		}
	}

	/**
	 * This method constructs the resulting automaton from the set of equivalent
	 * states.
	 * 
	 * @return resulting automaton where equivalent states are merged
	 */
	private INestedWordAutomaton<LETTER, STATE> constructResult() {
		synchronized (m_partition) {
			for (ArrayList<Integer> equivalenceClass : m_partition) {
				m_finalPartition.add(equivalenceClass);

			}
			// Clear list so the helper threads won't work any more.
			m_partition.clear();
		}
		// mapping from states to their representative
		final HashMap<Integer, ? extends Collection<STATE>> state2equivStates = computeMapState2Equiv();

		// construct result
		final StateFactory<STATE> stateFactory = m_operand.getStateFactory();
		NestedWordAutomaton<LETTER, STATE> result = new NestedWordAutomaton<LETTER, STATE>(
				m_services, m_operand.getInternalAlphabet(),
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
		for (ArrayList<Integer> elem : m_finalPartition) {
			if (elem == null) {
				continue;
			}
			if (!elem.isEmpty()) {
				final int representative = elem.get(0);
				LinkedList<STATE> equivStates = new LinkedList<STATE>();
				for (int j : elem) {
					equivStates.add(m_int2state.get(j));
					m_state2representative[j] = representative;
				}
				state2equivStates.put(representative, equivStates);
			}
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
			m_result = constructResult();
		}
		return m_result;
	}
}