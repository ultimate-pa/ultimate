package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

@SuppressWarnings("deprecation")
/**
 * Class for minimize deterministic finite automaton by the Hopcroft - Algorithm.
 * @author Björn Hagemeister
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class MinimizeDfaHopcroft<LETTER, STATE> implements
		IOperation<LETTER, STATE> {
	// Logger for debug - information.
	private static Logger s_Logger = NestedWordAutomata.getLogger();
	// Result automaton.
	private INestedWordAutomatonOldApi<LETTER, STATE> m_Result;
	// Input automaton.
	private INestedWordAutomatonOldApi<LETTER, STATE> m_operand;
	// ArrayList and HashMap for mapping STATE to int and vice versa.
	private ArrayList<STATE> m_int2state;
	private HashMap<STATE, Integer> m_state2int;
	// ArrayList and HashMap for mapping LETTER to int and vice versa.
	private ArrayList<LETTER> m_int2letter;
	private HashMap<LETTER, Integer> m_letter2int;
	// Structure for transitions.
	private int[] m_labels;
	private int[] m_labelTails;
	private int[] m_labelHeads;
	private int m_nOfTransitions;

	// Constructor.
	public MinimizeDfaHopcroft(INestedWordAutomatonOldApi<LETTER, STATE> operand) {
		this.m_operand = operand;

		// Start minimization.
		System.out.println(startMessage());
		minimizeDfaHopcroft();
		System.out.println(exitMessage());
	}

	private void minimizeDfaHopcroft() {
		initializeData();

		// initialize partition.
		Partition partition = createInitialPartition();
	}

	/**
	 * Create and return initial partition for the given automaton.
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
	 * Initialize structure for lables.
	 * Iterate over all states and get their OutgoingInternalTransistion<LETTER, STATE>
	 * for storing nOfLabel, headOfLabel and tailOfLabel.
	 */
	private void initializeLables() {
		m_labels = new int[Integer.MAX_VALUE];
		m_labelTails = new int[Integer.MAX_VALUE];
		m_labelHeads = new int[Integer.MAX_VALUE];
		
		// Iterate over all states in m_int2state.
		int index = 0;
		for (int i = 0; i < m_int2state.size(); ++i) {
			STATE st = m_int2state.get(i);
			// Get outgoing transition.
			Iterator<OutgoingInternalTransition<LETTER, STATE>> it = 
					m_operand.internalSuccessors(st).iterator();
			// hasNext? --> add to labels.
			while (it.hasNext()) {
				OutgoingInternalTransition< LETTER, STATE> oit = it.next();
				m_labels[index] = m_letter2int.get(oit.getLetter());
				m_labelTails[index] = m_state2int.get(st);
				m_labelHeads[index] = m_state2int.get(oit.getSucc());
				index++;
			}
		}
		m_nOfTransitions = index;
		// resize arrays to used size for saving memory
		// Maybe too much computing time?
		m_labels = Arrays.copyOf(m_labels, m_nOfTransitions);
		m_labelTails = Arrays.copyOf(m_labelTails, m_nOfTransitions);
		m_labelHeads = Arrays.copyOf(m_labelHeads, m_nOfTransitions);
	}
	
	/**
	 * Returns true, if there exists an incoming transition to <state> labeled
	 * with letter <letter>.
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
	 * @param state
	 * @param letter
	 * @return if outgoing transition labeled with <letter> exists.
	 */
	private boolean hasOutgoingTransitionWithLetter(int state, int letter) {
		STATE st = m_int2state.get(state);
		LETTER let = m_int2letter.get(letter);
		return m_operand.internalSuccessors(st, let).iterator().hasNext();
	}
	
	/**
	 * Returns number of state, which is predecessor of <state> with transition
	 * labeled with <letter>.
	 * @param state
	 * @param letter
	 * @return Number of predecessor state.
	 */
	private int getPredecessor(int state, int letter) {
		STATE st = m_int2state.get(state);
		LETTER let = m_int2letter.get(letter);
		STATE pred = m_operand.internalPredecessors(let, st).iterator().next().getPred();
		return m_state2int.get(pred);
	}
	
	/**
	 * Returns number of state, which is successor of <state> with transition
	 * labeled with <letter>.
	 * @param state
	 * @param letter
	 * @return Number of successor state.
	 */
	private int getSuccessor(int state, int letter) {
		STATE st = m_int2state.get(state);
		LETTER let = m_int2letter.get(letter);
		STATE succ = m_operand.internalSuccessors(st, let).iterator().next().getSucc();
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
	}
	
	@Override
	public String operationName() {
		return "minimizeDfaHopcroft";
	}

	@Override
	public String startMessage() {
		return "Starting minimization";
	}

	@Override
	public String exitMessage() {
		return "Finished minimization";
	}

	@Override
	public Object getResult() throws OperationCanceledException {
		return m_Result;
	}

	@SuppressWarnings("deprecation")
	@Override
	public final boolean checkResult(final StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		s_Logger.info("Start testing correctness of " + operationName());
		boolean correct = true;
		correct &= (ResultChecker.nwaLanguageInclusion(m_operand, m_Result, stateFactory) == null);
		correct &= (ResultChecker.nwaLanguageInclusion(m_Result, m_operand, stateFactory) == null);
		if (!correct) {
			ResultChecker.writeToFileIfPreferred(operationName() + "Failed", "", m_operand);
		}
		s_Logger.info("Finished testing correctness of " + operationName());
		return correct;
	}
}