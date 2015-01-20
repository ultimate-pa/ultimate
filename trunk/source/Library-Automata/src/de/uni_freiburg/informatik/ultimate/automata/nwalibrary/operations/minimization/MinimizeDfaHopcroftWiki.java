package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.MinimizeDfaHopcroft.Partition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.MinimizeDfaHopcroft.Worklist;
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
public class MinimizeDfaHopcroftWiki<LETTER, STATE> implements IMinimize,
		IOperation<LETTER, STATE> {
	// Logger for debug - information.
	private static Logger s_Logger = NestedWordAutomata.getLogger();
	// Service provider
	private final IUltimateServiceProvider m_services;
	// Result automaton.
	private INestedWordAutomaton<LETTER, STATE> m_result;
	// Input automaton.
	private INestedWordAutomaton<LETTER, STATE> m_operand;
	// ArrayList and HashMap for mapping STATE to int and vice versa.
	private ArrayList<STATE> m_int2state;
	private HashMap<STATE, Integer> m_state2int;
	// ArrayList and HashMap for mapping LETTER to int and vice versa.
	private ArrayList<LETTER> m_int2letter;
	private HashMap<LETTER, Integer> m_letter2int;
	// Partition of sets of states.
	private Partition m_partition;
	// Structure for transitions.
	private int[] m_labels;
	private int[] m_labelTails;
	private int[] m_labelHeads;
	private int m_nOfTransitions;
	private ArrayList<int[]> m_mapStatesToTransitionTails;
	private ArrayList<Integer>[] m_mapStatesToTransitionHeads;
	// map states to their representatives - needed for constructing result.
	private int[] m_state2representative;

	// Constructor.
	public MinimizeDfaHopcroftWiki(IUltimateServiceProvider services, INestedWordAutomaton<LETTER, STATE> operand) {
		this.m_services = services;
		this.m_operand = operand;

		// Start minimization.
		System.out.println(startMessage());
		initializeData();
		// Initialize partition.
		m_partition = createInitialPartition();
		minimizeDfaHopcroft();
		m_result = constructResult();
		System.out.println(exitMessage());
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

	// NOTE: Is this necessary - how could the algorithm even use it??
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

	private void minimizeDfaHopcroft() {
		Worklist worklist = m_partition.getWorklist();
		while (!worklist.isEmpty()) {
			int[] elem = worklist.popFromWorklist();
			for (LETTER letter : m_operand.getAlphabet()) {
				// This is far from optimal (hopefully): Find X, set of all
				// states for which a transition on letter leads to a state in
				// elem.
				ArrayList<Integer> x = new ArrayList<Integer>();
				int letterInt = m_letter2int.get(letter);
				for (int i = 0; i < m_nOfTransitions; i++) {
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
				for (int j = 0; j < m_partition.getPartitions().size(); j++) {
					int[] set = m_partition.getPartitions().get(j);
					// set intersects X != emptyset and set \ X != emptyset
					// Iterate set. Increment counter if element in X is found,
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

	/**
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
		for (int i = 0; i < m_partition.getPartitions().size(); i++) {
			if (m_partition.getPartitions().get(i).length > 0) {
				final int representative = m_partition.getPartitions().get(i)[0];
				LinkedList<STATE> equivStates = new LinkedList<STATE>();
				for (int j : m_partition.getPartitions().get(i)) {
					equivStates.add(m_int2state.get(j));
					m_state2representative[j] = representative;
				}
				state2equivStates.put(representative, equivStates);
			}
		}
		return state2equivStates;
	}

	/**
	 * This method computes the capacity size for hash sets and hash maps given
	 * the expected number of elements to avoid resizing.
	 * 
	 * @param size
	 *            expected number of elements before resizing
	 * @return the parameter for initializing the hash structure
	 */
	protected final int computeHashCap(int size) {
		return (int) (size * 1.34 + 1);
	}

	// ---------- Unused methods.---------- //
	/**
	 * Returns true, if there exists an incoming transition to <state> labeled
	 * with letter <letter>.
	 * 
	 * @param state
	 * @param letter
	 * @return if incoming transition labeled with letter exists.
	 */
	private boolean hasIncomingTransitionWithLetter(int state, int letter) {
		STATE st = m_int2state.get(state);
		LETTER let = m_int2letter.get(letter);
		return m_operand.internalPredecessors(let, st).iterator().hasNext();
	}

	/**
	 * Returns true, if an outgoing transition from <state> labeled with
	 * <letter> exists.
	 * 
	 * @param state
	 * @param letter
	 * @return if outgoing transition labeled with <letter> exists.
	 */
	private boolean hasOutgoingTransitionWithLetter(int state, int letter) {
		STATE st = m_int2state.get(state);
		LETTER let = m_int2letter.get(letter);
		return m_operand.internalSuccessors(st, let).iterator().hasNext();
	}

	// NOTE: There can be several such states in a DFA!!
	/**
	 * Returns number of state, which is predecessor of <state> with transition
	 * labeled with <letter>.
	 * 
	 * @param state
	 * @param letter
	 * @return Number of predecessor state.
	 */
	private int getPredecessor(int state, int letter) {
		STATE st = m_int2state.get(state);
		LETTER let = m_int2letter.get(letter);
		STATE pred = m_operand.internalPredecessors(let, st).iterator().next()
				.getPred();
		return m_state2int.get(pred);
	}

	/**
	 * Returns number of state, which is successor of <state> with transition
	 * labeled with <letter>.
	 * 
	 * @param state
	 * @param letter
	 * @return Number of successor state.
	 */
	private int getSuccessor(int state, int letter) {
		STATE st = m_int2state.get(state);
		LETTER let = m_int2letter.get(letter);
		STATE succ = m_operand.internalSuccessors(st, let).iterator().next()
				.getSucc();
		return m_state2int.get(succ);
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
		public int size() {
			return m_size;
		}

		/**
		 * Replaces one set by another two sets.
		 */
		public void replaceSetBy2Sets(int setToReplace, int[] a, int[] b) {
			m_setsOfPartition.remove(setToReplace);
			m_setsOfPartition.add(a);
			m_setsOfPartition.add(b);
			m_size++;
		}

		public ArrayList<int[]> getPartitions() {
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

	// -------------------Juno-----------------------------------------------------------
	@Override
	public String operationName() {
		return "minimizeDfaHopcroftWiki";
	}

	@Override
	public String startMessage() {
		return "Starting Minimization using Hopcroft's Algorithm";
	}

	@Override
	public String exitMessage() {
		return "Minimization using Hopcroft's Algorithm finished";
	}

	@Override
	public Object getResult() {
		return m_result;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		// TODO Rewrite and test correctness.
		/*
		 * s_Logger.info("Start testing correctness of " + operationName());
		 * boolean correct = true; correct &=
		 * (ResultChecker.nwaLanguageInclusion(m_operand, m_result,
		 * stateFactory) == null); correct &=
		 * (ResultChecker.nwaLanguageInclusion(m_result, m_operand,
		 * stateFactory) == null); if (!correct) {
		 * ResultChecker.writeToFileIfPreferred(operationName() + "Failed", "",
		 * m_operand); } s_Logger.info("Finished testing correctness of " +
		 * operationName());
		 */
		return true;
	}
}