package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.concurrent.LinkedBlockingQueue;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
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
	 * ArrayList and HashMap for mapping LETTER to integer and vice versa.
	 */
	private ArrayList<LETTER> m_int2letter;
	private HashMap<LETTER, Integer> m_letter2int;
	/**
	 * Partition of sets of states.
	 */
	private Partition m_partition;
	/**
	 * Interrupt object. The algorithm terminates without the complete result if
	 * status is set to true.
	 */
	private Interrupt m_interrupt;
	/**
	 * Structure for transitions.
	 */
	private int[] m_labels;
	private int[] m_labelTails;
	private int[] m_labelHeads;
	private int m_nOfTransitions;
	private ArrayList<int[]> m_mapStatesToTransitionTails;
	/**
	 * map states to their representatives - needed for constructing result.
	 */
	private int[] m_state2representative;

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
	private final ArrayList<int[]> m_finalPartition;
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
	public ArrayList<int[]> getSetList() {
		return m_partition.getPartitions();
	}

	/**
	 * Getter for partition of states that are already minimal.
	 * 
	 * @return
	 */
	public ArrayList<int[]> getFinalPartitions() {
		return m_finalPartition;
	}

	// ---- Starting minimization ---- //
	/**
	 * Constructor.
	 * 
	 * @param operand
	 *            the input automaton
	 */
	public MinimizeDfaHopcroftParallel(final IUltimateServiceProvider services,
			final INestedWordAutomaton<LETTER, STATE> operand) {
		super(services, operand.getStateFactory(), "MinimizeDfaHopcroftParallel", operand);
		m_services = services;
		this.m_operand = operand;
		if (s_parallel) {
			s_logger.info("HOP: Hopcroft Algorithm starts initialization");
		}
		initializeData();
		// Initialize partition.
		m_partition = createInitialPartition();
		// Initialize finalPartition
		m_finalPartition = new ArrayList<int[]>(m_partition.getPartitions()
				.size());
		if (s_parallel) {
			m_initialized = true;
			synchronized (this) {
				try {
					this.notify();
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
			s_logger.info("HOP: Hopcroft Algorithm initialized");
		}
		if (!s_parallel) {
			minimizeDfaHopcroft();
			m_result = constructResult();
			// Do time measurement
			ThreadMXBean bean = ManagementFactory.getThreadMXBean();
			s_logger.info("CPU Time: "
					+ bean.getThreadCpuTime(Thread.currentThread().getId())
					/ Math.pow(10, 9) + "ns");
			s_logger.info(exitMessage());
		}
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
	public MinimizeDfaHopcroftParallel(final IUltimateServiceProvider services, final StateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final Interrupt interrupt) throws OperationCanceledException,
			AutomataLibraryException {
		this(services, operand);
		m_interrupt = interrupt;
		assert ((m_interrupt == null) || (!m_interrupt.getStatus())) : "HOP: The interrupt tells to terminate right at the beginning.";
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
		m_result = constructResult();
		s_logger.info("HOP: " + exitMessage());
	}

	/**
	 * Create and return initial partition for the given automaton.
	 * 
	 * @return Initialized partition.
	 */
	private Partition createInitialPartition() {
		// create new partition.
		Partition ret = new Partition();
		ret.init();

		return ret;
	}

	/**
	 * Get number of states and labels for calling initializeMappings and
	 * initializeLables.
	 */
	private void initializeData() {
		int nOfStates = m_operand.getStates().size();
		int nOfLables = m_operand.getInternalAlphabet().size();
		initializeMappings(nOfStates, nOfLables);
		initializeLables();
	}

	/**
	 * Method for mapping STATE/LETTER to int and vice versa.
	 */
	private void initializeMappings(int nOfStates, int nOfLables) {
		// Allocate the finite space in ArrayList and HashMap.
		m_int2state = new ArrayList<STATE>(nOfStates);
		m_state2int = new HashMap<STATE, Integer>(
				computeHashMapCapacity(nOfStates));
		m_int2letter = new ArrayList<LETTER>(nOfLables);
		m_letter2int = new HashMap<LETTER, Integer>(
				computeHashMapCapacity(nOfLables));

		int index = -1;
		for (final STATE state : m_operand.getStates()) {
			m_int2state.add(state);
			m_state2int.put(state, ++index);
		}
		index = -1;
		for (final LETTER letter : m_operand.getAlphabet()) {
			m_int2letter.add(letter);
			m_letter2int.put(letter, ++index);
		}
	}

	/**
	 * Initialize structure for lables. Iterate over all states and get their
	 * OutgoingInternalTransition<LETTER, STATE> for storing nOfLabel,
	 * headOfLabel and tailOfLabel.
	 */
	private void initializeLables() {
		int capacity = (int) Math.min((double) Integer.MAX_VALUE,
				(double) m_operand.size() * m_operand.size()
						* m_operand.getAlphabet().size());
		m_labels = new int[capacity];
		m_labelTails = new int[capacity];
		m_labelHeads = new int[capacity];
		// Contains arrays of [state_int, firstIndex, numOfIndexes]
		m_mapStatesToTransitionTails = new ArrayList<int[]>();

		// Iterate over all states in m_int2state.
		int index = 0;
		for (int i = 0; i < m_int2state.size(); ++i) {
			STATE st = m_int2state.get(i);
			// Get outgoing transition.
			Iterator<OutgoingInternalTransition<LETTER, STATE>> it = m_operand
					.internalSuccessors(st).iterator();
			// hasNext? --> add to labels.
			int count = 0;
			while (it.hasNext()) {
				OutgoingInternalTransition<LETTER, STATE> oit = it.next();
				m_labels[index] = m_letter2int.get(oit.getLetter());
				m_labelTails[index] = m_state2int.get(st);
				m_labelHeads[index] = m_state2int.get(oit.getSucc());
				index++;
				count++;
			}
			int[] map = new int[] { i, index - count, count };
			m_mapStatesToTransitionTails.add(map);
		}
		m_nOfTransitions = index;
		// resize arrays to used size for saving memory
		// Maybe too much computing time?
		m_labels = Arrays.copyOf(m_labels, m_nOfTransitions);
		m_labelTails = Arrays.copyOf(m_labelTails, m_nOfTransitions);
		m_labelHeads = Arrays.copyOf(m_labelHeads, m_nOfTransitions);
	}

	/**
	 * Minimize the input automaton using Hopcroft's algorithm.
	 */
	private void minimizeDfaHopcroft() {
		if (s_parallel) {
			s_logger.info("HOP: " + startMessage());
		}
		Worklist worklist = m_partition.getWorklist();
		while (!worklist.isEmpty()) {
			// TODO Right spot
			if ((m_interrupt != null) && (m_interrupt.getStatus())) {
				return;
			}
			int[] elem = worklist.popFromWorklist();
			for (LETTER letter : m_operand.getAlphabet()) {
				// This is far from optimal (hopefully): Find X, set of all
				// states for which a transition on letter leads to a state in
				// elem.
				ArrayList<Integer> x = new ArrayList<Integer>();
				int letterInt = m_letter2int.get(letter);
				for (int i = 0; i < m_nOfTransitions; i++) {
					// TODO Right spot?
					if ((m_interrupt != null) && (m_interrupt.getStatus())) {
						return;
					}
					if (m_labels[i] == letterInt) {
						for (int stateInt : elem) {
							if (stateInt == m_labelHeads[i]) {
								x.add(m_labelTails[i]);
							}
						}
						// Doesn't work (always evaluates to false): &&
						// Arrays.asList(elem).contains(m_labelHeads[i]))
					}
				}
				// end initialization of X.
				synchronized (m_partition.getPartitions()) {
					for (int j = 0; j < m_partition.getPartitions().size(); j++) {
						// TODO Right spot?
						if ((m_interrupt != null) && (m_interrupt.getStatus())) {
							return;
						}
						int[] set = m_partition.getPartitions().get(j);
						// set intersects X != emptyset and set \ X != emptyset
						// Iterate set. Increment counter if element in X is
						// found,
						// and increment if element not in X is found.
						ArrayList<Integer> intersection = new ArrayList<Integer>();
						ArrayList<Integer> complement = new ArrayList<Integer>();
						for (int i = 0; i < set.length; i++) {
							if (x.contains(set[i])) {
								intersection.add(set[i]);
							} else {
								complement.add(set[i]);
							}
						}
						int[] intersect = toIntArray(intersection);
						int[] comp = toIntArray(complement);
						if (intersection.size() > 0 && complement.size() > 0) {
							m_partition.replaceSetBy2Sets(j, intersect, comp);
							if (s_parallel) {
								try {
									m_taskQueue.put(new HelpIncremental(
											m_incrementalAlgorithm, intersect,
											comp));
									s_logger.info("HOP: Size of task queue: "
											+ m_taskQueue.size());
									;
								} catch (InterruptedException e) {
									e.printStackTrace();
								}
							}
							// set in W
							int position = findSet(set, worklist);
							if (!(position < 0)) {
								worklist.replaceSetBy2Sets(position, intersect,
										comp);
							} else {
								if (intersect.length <= comp.length) {
									worklist.addToWorklist(intersect);
								} else {
									worklist.addToWorklist(comp);
								}
							}
						}
					}
				}

			}
		}
	}

	/**
	 * Find a set in the worklist.
	 * 
	 * @param set
	 * @param worklist
	 * @return Natural number (position of set in worklist) if worklist contains
	 *         set, -1 otherwise.
	 */
	private int findSet(int[] set, Worklist worklist) {
		for (int i = 0; i < worklist.getSize(); i++) {
			if (arrayEquals(set, worklist.get(i))) {
				return i;
			}
		}
		return -1;
	}

	/**
	 * Compare equality of two arrays.
	 * 
	 * @param a
	 * @param b
	 * @return True if arrays contain the same numbers, false otherwise.
	 */
	private boolean arrayEquals(int[] a, int[] b) {
		if (b.length != a.length) {
			return false;
		}
		for (int number : b) {
			if (!Arrays.asList(a).contains(number)) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Create an integer array from a list.
	 * 
	 * @param list
	 * @return
	 */
	private int[] toIntArray(List<Integer> list) {
		int[] ret = new int[list.size()];
		int i = 0;
		for (Integer e : list)
			ret[i++] = e.intValue();
		return ret;
	}

	/**
	 * This method constructs the resulting automaton from the set of equivalent
	 * states.
	 * 
	 * @return resulting automaton where equivalent states are merged
	 */
	private INestedWordAutomaton<LETTER, STATE> constructResult() {
		synchronized (m_partition) {
			for (int[] equivalenceClass : m_partition.getPartitions()) {
				m_finalPartition.add(equivalenceClass);
				
			}
			// Clear list so the helper threads won't work any more.
			m_partition.getPartitions().clear();
		}
		// mapping from states to their representative
		final HashMap<Integer, ? extends Collection<STATE>> state2equivStates = computeMapState2Equiv();

		// construct result
		final StateFactory<STATE> stateFactory = m_operand.getStateFactory();
		NestedWordAutomaton<LETTER, STATE> result = new NestedWordAutomaton<LETTER, STATE>(m_services,
				m_operand.getInternalAlphabet(), m_operand.getCallAlphabet(),
				m_operand.getReturnAlphabet(), stateFactory);

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
		for (int i = 0; i < m_finalPartition.size(); i++) {
			if (m_finalPartition.get(i).length > 0) {
				final int representative = m_finalPartition.get(i)[0];
				LinkedList<STATE> equivStates = new LinkedList<STATE>();
				for (int j : m_finalPartition.get(i)) {
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

	// ---------------------------------------------------------------------------------------------//
	/**
	 * Class for representing a partition. A partition P contains blocks of
	 * states Y_1 ... Y_n. As initial blocks a partition P should contain P =
	 * {Y_1, Y_2} with Y_1 = {F} and Y_2 = {Q\F}.
	 * 
	 * @author bjoern
	 *
	 */
	public class Partition {
		// ArrayList, to represent the sets in partition.
		private ArrayList<int[]> m_setsOfPartition;
		private int m_size;
		// All final states.
		private int[] m_finalStates;
		// All non - final states.
		private int[] m_nonfinalStates;
		// WorkList of partition.
		private Worklist m_workList;

		/**
		 * Constructor. Initialize arrays finalStates and nonfinalStates.
		 * 
		 * @param nOfStates
		 * @param nOfFinalStates
		 */
		public Partition() {
			m_size = 0;
		}

		/**
		 * Initialize Partition. Transfer collection of finalStates and states
		 * to int[] m_finalStates and int[] m_nonfinalStates and create
		 * workList.
		 * 
		 * @param finalStates
		 * @param states
		 */
		public void init() {
			Collection<STATE> finalStates = m_operand.getFinalStates();
			Collection<STATE> states = m_operand.getStates();

			int nOfFinalStates = finalStates.size();
			int nOfStates = states.size();

			m_finalStates = new int[nOfFinalStates];
			m_nonfinalStates = new int[nOfStates - nOfFinalStates];
			m_setsOfPartition = new ArrayList<int[]>(nOfStates);

			int fStatesInd = -1;
			int nfStatesInd = -1;
			Iterator<STATE> it = states.iterator();
			while (it.hasNext()) {
				STATE st = it.next();
				if (finalStates.contains(st)) {
					m_finalStates[++fStatesInd] = m_state2int.get(st);
				} else {
					m_nonfinalStates[++nfStatesInd] = m_state2int.get(st);
				}
				m_size++;
			}
			m_setsOfPartition.add(m_finalStates);
			m_setsOfPartition.add(m_nonfinalStates);
			// initialize workList with finalStates.
			m_workList = new Worklist(states.size());
			m_workList.addToWorklist(m_finalStates);
		}

		/**
		 * Size of partition = number of containing sets.
		 * 
		 * @return number of containing sets.
		 */
		public synchronized int size() {
			return m_size;
		}

		/**
		 * Replaces one set by another two sets.
		 */
		public synchronized void replaceSetBy2Sets(int setToReplace, int[] a,
				int[] b) {
			m_setsOfPartition.remove(setToReplace);
			m_setsOfPartition.add(a);
			m_setsOfPartition.add(b);
			m_size++;
		}

		public synchronized ArrayList<int[]> getPartitions() {
			return m_setsOfPartition;
		}

		/**
		 * The algorithm needs to operate on the worklist of partition.
		 * 
		 * @return current worklist.
		 */
		public Worklist getWorklist() {
			return m_workList;
		}
	}

	/**
	 * Class for representing worklist.
	 * 
	 * @author bjoern
	 */
	public class Worklist {
		private ArrayList<int[]> m_setsOfStates;
		private int m_size;

		/**
		 * Constructor. Initialize ArrayList<int[]> with maxSize = nOfStates.
		 */
		public Worklist(int maxSize) {
			m_setsOfStates = new ArrayList<int[]>(maxSize);
			m_size = m_setsOfStates.size();
		}

		/**
		 * Pop last element of worklist.
		 */
		public int[] popFromWorklist() {
			if (m_setsOfStates.isEmpty())
				return null;
			int[] ret = m_setsOfStates.remove(m_size - 1);
			m_size--;
			return ret;
		}

		/**
		 * Add collection of states to worklist.
		 */
		public void addToWorklist(int[] set) {
			m_setsOfStates.add(set);
			m_size++;
		}

		/**
		 * Replace specific Set by two other sets.
		 */
		public boolean replaceSetBy2Sets(int setToReplace, int[] a, int[] b) {
			m_setsOfStates.remove(setToReplace);
			boolean a_added = m_setsOfStates.add(a);
			boolean b_added = m_setsOfStates.add(b);
			m_size++;
			return (a_added && b_added);
		}

		/**
		 * Returns true, if and only if worklist is empty.
		 */
		public boolean isEmpty() {
			return m_setsOfStates.isEmpty();
		}

		/**
		 * Get number of arrays currently in the list.
		 * 
		 * @return
		 */
		public int getSize() {
			return m_size;
		}

		public int[] get(int i) {
			return m_setsOfStates.get(i);
		}
	}

	@Override
	public INestedWordAutomatonSimple<LETTER, STATE> getResult() {
		return m_result;
	}
}