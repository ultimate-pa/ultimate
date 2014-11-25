package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

@SuppressWarnings("deprecation")
/**
 * Class for minimize deterministic finite automaton by the Hopcroft - Algorithm.
 * @author Björn Hagemeister
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class MinimizeDfaSymbolic<LETTER, STATE> implements
		IOperation<LETTER, STATE> {
	// Logger for debug - information.
	private static Logger s_Logger = NestedWordAutomata.getLogger();
	// Result automaton.
	private NestedWordAutomaton<LETTER, STATE> m_Result;
	// Input automaton.
	private INestedWordAutomaton<LETTER, STATE> m_operand;
	
	/***********************************************************************//**
	 * Necessary data elements for computing the minimal DFA.
	 */
	private int 
		m_nOfTransitions,	// number of transitions.
		m_nOfStates,		// number of states.
		m_nOfFinalStates,	// number of final states.
	    m_nOfLetters;		// number of letters in alphabet.
	
	private STATE
		m_initialState;		// initial state. In DFA there exists just one.
	
	private HashMap<STATE, Block>
		m_partition;		// Partition
	
	private Worklist
		m_worklist;			// Worklist
	
	private Collection<LETTER>
		m_alphabet;			// alphabet of automaton.
	
	private SMTInterpol
		m_smtInterpol;		// Logic solver object.
	
	private Sort
		m_bool;
	
	private Sort[]
		m_emptyArray;
	/**************************************************************************/
	
	
	
	/***********************************************************************//**
	 * Constructor
	 * @param operand
	 */
	public MinimizeDfaSymbolic(INestedWordAutomatonOldApi<LETTER, STATE> operand) {
		this.m_operand = operand;

		// Start minimization.
		System.out.println(startMessage());
		minimizeDfaSymbolic();
		System.out.println(exitMessage());
	}

	private void minimizeDfaSymbolic() {
		preprocessingData();

		// initialize partition and worklist.
		initializePartitionAndWorklist();
		
		// initialize logic solver and simplifier.
		initializeSolver();
		
		/*******************************************************************//**
		 * Start with main algorithm.
		 */
		// While worklist is not empty.
		s_Logger.info("Size of worklist: " + m_worklist.size());
		s_Logger.info("Size of partition: " + m_partition.size());
		while (!m_worklist.isEmpty()) {
			// Choose and remove a block r from worklist.
			Block r = m_worklist.pop();
			// Create mapping of predecessor states leading into block r.
			HashMap<STATE, MyFormula> labelMapping = constructMapping(r);
			// Get all predecessors and store into collection s.
			Block s = new Block(labelMapping.keySet());
			
			// Building collection of blocks P of m_partition for which is known
			// 			P intersect with s = NON - EMPTY
			// and		P \ s = NON - EMPTY.
			HashMap<Block, Block> relevant = buildIntersectingBlocksMap(s);
			Iterator<Block> relevantIt = relevant.keySet().iterator();
			// iterate over relevant and split m_partition and m_worklist if necessary.
			while (relevantIt.hasNext()) {
				Block p = relevantIt.next();
				Block p1 = relevant.get(p);
				// if p1 is smaller than p, the difference of P\S is non - empty.
				// Remove each state from p1 and change belonging block in m_partition.
				if (p1.size() < p.size()) {
					for (int i = 0; i < p1.size(); ++i) {
						p.remove(p1.get(i));
						m_partition.put(p1.get(i), p1);
					}
					// Add new block to worklist, if already contains, or just add the
					// smaller one.
					if (m_worklist.contains(p)) {
						m_worklist.push(p1);
					} else {
						if (p.size() <= p1.size()) {
							m_worklist.push(p);
						} else {
							m_worklist.push(p1);
						}
					}
				}
			}
			
			boolean iterate = true;
			while (iterate) {
				iterate = false;
				// Create blocks P from m_partition, which are non - empty after 
				// intersecting with block s.
				ArrayList<Block> intersectingBlocks =
						buildIntersectingBlocksSet(s);
				// Iterate over blocks P - for Loop over
				// intersecting blocks in paper.
				for (int i = 0; i < intersectingBlocks.size(); ++i) {
					Block p = intersectingBlocks.get(i);
					Block p1 = new Block();
					// Start with some element of P.
					// Get formula of first state.
					MyFormula psi = labelMapping.get(p.get(0));
					boolean splitterFound = false;
					p1.add(p.get(0));
					
					// iterate over rest of currentBlock P. (States).
					for (int j = 1; j < p.size(); ++j) {
						STATE q = p.get(j);
						// Get formula of current state.
						MyFormula phi = labelMapping.get(q);
						if (splitterFound) {
							MyFormula psiAndPhi = conjunct(psi, phi);
							if (isValidFormula(psiAndPhi)) {
								p1.add(q);
								psi = psiAndPhi;
							} 
						} else {
							MyFormula negPhi = negate(phi);
							MyFormula psiAndNegPhi = conjunct(psi, negPhi);
							if (isValidFormula(psiAndNegPhi)) {
								// refine the local minterm.
								psi = psiAndNegPhi;
								splitterFound = true;
							} else { // psi implies phi.
								MyFormula negPsi = negate(psi);
								MyFormula phiAndNegPsi = conjunct(phi, negPsi);
								if (isValidFormula(phiAndNegPsi)) {
									p1.clear();
									p1.add(q);
									psi = phiAndNegPsi;
									splitterFound = true;
								} else {
									p1.add(q);
								}
							}	
						}
						// If p1 < p. The difference of P\P1 is not - empty.
						if (p1.size() < p.size()) {
							iterate = (iterate || (p.size() > 2));
							// Remove each state from p1 and change belonging
							// block in m_partition.
							for (int k = 0; k < p1.size(); ++k) {
								p.remove(p1.get(k));
								m_partition.put(p1.get(k), p1);
							}
							// Check if worklist already contains block p.
							// If yes, add p1 too, if not, add the smaller one.
							if (m_worklist.contains(p)) {
								m_worklist.push(p1);
							} else if (p.size() <= p1.size()) {
								m_worklist.push(p);
							} else {
								m_worklist.push(p1);
							}
						}
					}
				}
			}
		}
		/*******************************************************************//**
		 * New automaton should be ready, build the result automaton.
		 */
		buildResult();
	}

	/**
	 * Get number of states and labels for calling initializeMappings and
	 * initializeLables.
	 */
	private void preprocessingData() {
		m_nOfStates= m_operand.getStates().size();
		m_nOfFinalStates = m_operand.getFinalStates().size();
		m_nOfLetters= m_operand.getInternalAlphabet().size();
		
		// There is only one initial state in a DFA.
		m_initialState = m_operand.getInitialStates().iterator().next();
		
		// get internal alphabet of m_operand.
		m_alphabet = m_operand.getInternalAlphabet();
		s_Logger.info("m_alphabet: " + m_alphabet.toString());
	}

	private void initializePartitionAndWorklist() {
		// First create initial partition. Therefor create block with final
		// states and block with nonfinal states.
		Block finalStates = new Block(m_operand.getFinalStates());
		Block nonFinalStates = new Block(m_operand.getStates());
		// Iterate over all states which are currently stored in nonFinalStates
		// and remove final states from nonFinalStates - block.
		for (int i = 0; i < nonFinalStates.size(); ++i) {
			STATE nFS = nonFinalStates.get(i);
			if (finalStates.contains(nFS))
				nonFinalStates.remove(nFS);
		}
		
		// Set hasInitialState.
		if (nonFinalStates.contains(m_initialState)) {
			nonFinalStates.hasInitialState(true);
		} else if (finalStates.contains(m_initialState)) {
			finalStates.hasInitialState(true);
		}
		
		// Create mapping STATE -> Block.
		m_partition = new HashMap<STATE, Block>(computeHashMapCapacity(m_nOfStates));
		for (int i = 0; i < finalStates.size(); ++i) {
			m_partition.put(finalStates.get(i), finalStates);
		}
		for (int i = 0; i < nonFinalStates.size(); ++i) {
			m_partition.put(nonFinalStates.get(i), nonFinalStates);
		}
		
		// Second, create initial Worklist. Therefor just insert the smaller
		// block of finalStates and nonFinalStates.
		m_worklist = new Worklist();
//		if (finalStates.size() <= nonFinalStates.size()) {
			m_worklist.push(finalStates);
//		} else {
			m_worklist.push(nonFinalStates);
//		}
	}
	
	private void initializeSolver() {
		m_smtInterpol = new SMTInterpol();
		
		// Set logic of solver object.
		m_smtInterpol.setLogic(Logics.QF_UF);
		
		m_bool = m_smtInterpol.sort("Bool");
		m_emptyArray = new Sort[]{};
	}

	// Construct mapping for transitions of predecessor states leading into block r.
	private HashMap<STATE, MyFormula> constructMapping(Block r) {
		// create HashMap with max size of number of states.
		HashMap<STATE, MyFormula> retMap = new HashMap<STATE, MyFormula>(
				computeHashMapCapacity(m_nOfStates));
		
		// Iterate over all containing states of block r.
		for (int i = 0; i < r.size(); ++i) {
			STATE st = r.get(i);
			// Iterating over whole alphabet for catching each label.
			Iterator<LETTER> it = m_alphabet.iterator();
			while (it.hasNext()) {
				LETTER letter = it.next();
				if (hasIncomingTransitionWithLetter(st, letter)) {
					// Get all predecessors with transition into state
					// labled with letter.
					Collection<STATE> predecessors = getPredecessor(st, letter);
					MyFormula atomLetter = makeAtom(letter);
					// Iterate over predecessors.
					Iterator<STATE> predIt = predecessors.iterator();
					while (predIt.hasNext()) {
						STATE pred = predIt.next();
						if (retMap.containsKey(pred)) {
							// HashMap contains pred already.
							// Just add formula as disjunction.
							retMap.put(pred, disjunct(atomLetter, retMap.get(pred)));
						} else {
							// HashMap does not contain pred yet. Add new key.
							retMap.put(pred, atomLetter);
						}
					}
				}
			}
		}
		return retMap;
	}
	
	private ArrayList<Block> buildIntersectingBlocksSet(Block s) {
		ArrayList<Block> ret = new ArrayList<Block>(m_nOfStates);
		// Iterate over STATEs in s and lookup to which block they belong to.
		for (int i = 0; i < s.size(); ++i) {
			Block block = m_partition.get(s.get(i));
			// If ArrayList<Block> already contains block do not add twice.
			if (!ret.contains(block)) {
				ret.add(block);
			}
		}
		return ret;
	}
	
	private HashMap<Block, Block> buildIntersectingBlocksMap(Block s) {
		HashMap<Block, Block> ret =
				new HashMap<Block, Block>(computeHashMapCapacity(m_nOfStates));
		// Lookup all Blocks to which the STATEs of s belong to and add to Map.
		for (int i = 0; i < s.size(); ++i) {
			Block block = m_partition.get(s.get(i));
			if (ret.containsKey(block)) {
				// Block is already existing in Map. Just add the state.
				ret.get(block).add(s.get(i));
			} else {
				// Block does not exist already in Map. Create new Block with 
				// this first state in it.
				Block b = new Block();
				b.add(s.get(i));
				ret.put(block, b);
			}
		}
		return ret;
	}
	
	/**
	 * Returns true, if there exists an incoming transition to state labeled
	 * with letter letter.
	 * @param state
	 * @param letter
	 * @return if incoming transition labeled with letter exists.
	 */
	private boolean hasIncomingTransitionWithLetter(STATE state, LETTER letter) {
		return m_operand.internalPredecessors(letter, state).iterator().hasNext();
	}
	
	/**
	 * Returns true, if an outgoing transition from <state> labeled with
	 * <letter> exists.
	 * @param state
	 * @param letter
	 * @return if outgoing transition labeled with <letter> exists.
	 */
	private boolean hasOutgoingTransitionWithLetter(STATE st, LETTER letter) {
		return m_operand.internalSuccessors(st, letter).iterator().hasNext();
	}
	
	/**
	 * Returns state, which is predecessors of state with transition
	 * labeled with letter.
	 * @param state
	 * @param letter
	 * @return predecessor state.
	 */
	private Collection<STATE> getPredecessor(STATE state, LETTER letter) {
		Collection<STATE> retColl = new ArrayList<STATE>(m_nOfStates);
		Iterator<IncomingInternalTransition<LETTER, STATE>> it =
				m_operand.internalPredecessors(letter, state).iterator();
		while (it.hasNext()) {
			retColl.add(it.next().getPred());
		}
		return retColl;
	}
	
	/**
	 * Returns state, which is successor of <state> with transition
	 * labeled with <letter>.
	 * @param state
	 * @param letter
	 * @return successor state.
	 */
	private STATE getSuccessor(STATE state, LETTER letter) {
		Iterator<OutgoingInternalTransition<LETTER, STATE>> it =
				m_operand.internalSuccessors(state, letter).iterator();
		if (it.hasNext())
			return it.next().getSucc();
		return null;
	}
	
	// Compute the intersection of two blocks b1 and b2.
	private Block computeIntersection(Block b1, Block b2) {
		// Search for elements, which occur in both blocks and build new result
		// block for returning.
		Block result = new Block();
		STATE x;
		for (int i = 0; i < b1.size(); ++i) {
			x = b1.get(i);
			if (b2.contains(x)) {
				result.add(x);
				if (x == m_initialState) {
					result.hasInitialState(true);
				}
			}
		}
		return result;
	}
	
	// Compute the difference of two blocks (b1 \ b2).
	private Block computeDifference(Block b1, Block b2) {
		// Iterate over Block b2 and remove all elements of b2 from b1 if occuring.
		Block result = new Block(b1);
		STATE x;
		for (int i = 0; i < b2.size(); ++i) {
			x = b2.get(i);
			if (result.contains(x)) {
				result.remove(x);
				if (x == m_initialState) {
					result.hasInitialState(false);
				} else {
					result.hasInitialState(true);
				}
			}
		}
		return result;
	}
	
	// Create logic variable from Letter <letter>.
	private MyFormula makeAtom(LETTER letter) {
		try {
			m_smtInterpol.declareFun(letter.toString(), m_emptyArray, m_bool);
		} catch (SMTLIBException e) {
			// Function already exists. Not necessary to create a new one.
		}
		Term var = m_smtInterpol.term(letter.toString());
		Atom atom = new Atom(var);
		return atom;
	}
	
	// Create a conjunction from a collection of formulas.
	private MyFormula conjunct(MyFormula f1, MyFormula f2) {
		Collection<MyFormula> mF = new ArrayList<MyFormula>(2);
		mF.add(f1);
		mF.add(f2);
		Iterator<MyFormula> it = mF.iterator();
		Term[] conjuncts = new Term[mF.size()];
		int index = -1;
		while(it.hasNext()) {
			conjuncts[++index] = it.next().getTerm();
		}
		Term var = m_smtInterpol.term("and", conjuncts);
		Conjunction con = new Conjunction(var);
		return con;
	}
	
	// Create a disjunction from a collection of formulas.
	private MyFormula disjunct(MyFormula f1, MyFormula f2) {
		Collection<MyFormula> mF = new ArrayList<MyFormula>(2);
		mF.add(f1);
		mF.add(f2);
		Iterator<MyFormula> it = mF.iterator();
		Term[] disjuncts = new Term[mF.size()];
		int index = -1;
		while(it.hasNext()) {
			disjuncts[++index] = it.next().getTerm();
		}
		Term var = m_smtInterpol.term("or", disjuncts);
		Disjunction dis = new Disjunction(var);
		return dis;
	}
	
	// Negate a given formula.
	private MyFormula negate(MyFormula formula) {
		Term[] negation = new Term[1];
		negation[0] = formula.getTerm();
		Term var = m_smtInterpol.term("not", negation);
		Negation neg = new Negation(var);
		return neg;
	}
	
	private boolean isValidFormula(MyFormula formula) {
		m_smtInterpol.push(1);
		m_smtInterpol.assertTerm(formula.getTerm());
		
		LBool isSat = m_smtInterpol.checkSat();
		m_smtInterpol.pop(1);
		return (isSat == LBool.SAT);
	}
	
	// Return number of Block in m_partition to witch <state> belongs to.
	// If <state> is not found, return -1.
	private int numOfBlockInPartition(STATE state) {
		for (int i = 0; i < m_partition.size(); ++i) {
			if (m_partition.get(i).contains(state)) {
				return i;
			}
		}
		return -1;
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

//	/***********************************************************************//**
//	 * Class for representing a partition.
//	 * 
//	 * @author bjoern
//	 */
//	public class Partition {
//		private ArrayList<Block> m_setsOfStates;
//		private int m_size;
//		
//		// Constructor. Allocates space for ArrayList<Block> m_setsOfStates.
//		public Partition() {
//			m_setsOfStates = new ArrayList<Block>(m_nOfStates);
//			m_size = 0;
//		}
//		
//		// Adds block to Partition.
//		public void add(Block block) {
//			m_setsOfStates.add(block);
//			m_size++;
//		}
//		
//		// Remove block from Partition.
//		// Returns true if current Partition contained <block>.
//		public boolean remove(Block block) {
//			m_size--;
//			return m_setsOfStates.remove(block);
//		}
//		
//		// Returns block <index> of Partition.
//		public Block get(int index) {
//			return m_setsOfStates.get(index);
//		}
//		
//		// Returns size of current Partition.
//		public int size() {
//			return m_size;
//		}
//		
//		public String toString() {
//			String ret = "(";
//			for (int i = 0; i < m_setsOfStates.size(); ++i) {
//				ret += m_setsOfStates.get(i).toString();
//			}
//			ret += ")";
//			return ret;
//		}
//	}

	/***********************************************************************//**
	 * Class for representing worklist.
	 * 
	 * @author bjoern
	 */
	public class Worklist {
		private LinkedList<Block> m_setsOfStates;
		private int m_size;

		 // Constructor. Initialize an empty LinkedList<Block>.
		public Worklist() {
			m_setsOfStates = new LinkedList<Block>();
			m_size = 0;
		}

		// Pop first element of worklist.
		public Block pop() {
			if (m_setsOfStates.isEmpty())
				return null;
			m_size--;
			return m_setsOfStates.pop();
		}

		// Push element into worklist.
		public void push(Block block) {
			m_setsOfStates.push(block);
			m_size++;
		}
		
		// Returns Block i from worklist.
		public Block get(int i) {
			return m_setsOfStates.get(i);
		}

		// Remove given block from worklist.
		public boolean remove(Block block) {
			return m_setsOfStates.remove(block);
		}
		
		// Returns if worklist contains given block or not.
		public boolean contains(Block block) {
			return m_setsOfStates.contains(block);
		}
		
		// Return current size of Worklist.
		public int size() {
			return m_size;
		}

		// Returns if Worklist is currently empty or not.
		public boolean isEmpty() {
			return m_setsOfStates.isEmpty();
		}
		
		public String toString() {
			String ret = "(";
			for (int i = 0; i < m_setsOfStates.size(); ++i) {
				ret += m_setsOfStates.get(i).toString();
			}
			ret += ")";
			return ret;
		}

	}
	
	/***********************************************************************//**
	 * Class for representing a block of states.
	 * @author bjoern
	 *
	 */
	public class Block {
		private ArrayList<STATE> m_states;
		private int m_size = 0;
		private boolean m_hasInitialState = false;
		
		// Constructor.
		public Block(Collection<STATE> block) {
			// create new ArrayList<STATE> with allocated space.
			m_states = new ArrayList<STATE>(m_nOfStates);
			Iterator<STATE> it = block.iterator();
			while (it.hasNext()) {
				m_states.add(it.next());
				m_size++;
			}
		}
		
		// Copy constructor.
		public Block(Block block) {
			this(block.returnStates());
		}
		
		// Default constructor. Just allocates space for ArrayList<STATE> m_states.
		public Block() {
			m_states = new ArrayList<STATE>(m_nOfStates);
		}
		
		// Remove state <st> from block.
		public boolean remove(STATE st) {
			m_size--;
			return m_states.remove(st);
		}
		
		// Add state <st> to block.
		public void add(STATE st) {
			m_states.add(st);
			m_size++;
		}
		
		// Clear current block.
		public void clear() {
			m_states.clear();
		}
		
		// Returns state <i> from block.
		public STATE get(int i) {
			return m_states.get(i);
		}
		
		// Returns current size of block.
		public int size() {
			return m_states.size();
		}
		
		// Returns if block contains currently state <state> or not.
		public boolean contains(STATE state) {
			return m_states.contains(state);
		}
		
		// Returns if block is currently empty or not.
		public boolean isEmpty() {
			return m_states.isEmpty();
		}
		
		// Returns if block contains initial state.
		public boolean hasInitialState() {
			return m_hasInitialState;
		}
		
		// Set the variable m_hasInitialState.
		public void hasInitialState(boolean hasInitState) {
			m_hasInitialState = hasInitState;
		}
		
		public ArrayList<STATE> returnStates() {
			return m_states;
		}
		
		public String toString() {
			String ret = "(";
			for (int i = 0; i < m_states.size(); ++i) {
				ret += "{";
				ret += m_states.get(i).toString();
				ret += "}";
			}
			ret += ")";
			return ret;
		}
	}
	
	/***********************************************************************//**
	 * Abstract class for representing a formula.
	 * @author bjoern
	 *
	 */
	public abstract class MyFormula {
		protected Term m_term;
		
		public abstract String toString();
		
		public abstract Term getTerm();
	}
	
	// Class for representing a atom inheriting from MyFormula.
	public class Atom extends MyFormula {
		public Atom(Term term) {
			m_term = term;
		}
		
		@Override
		public Term getTerm() {
			return m_term;
		}

		@Override
		public String toString() {
			return m_term.toString();
		}
	}
	
	// Class for representing a conjunction inheriting from MyFormula.
	public class Conjunction extends MyFormula {
		public Conjunction(Term term) {
			m_term = term;
		}

		public Term getTerm() {
			return m_term;
		}
		
		@Override
		public String toString() {
			return m_term.toString();
		}
	}
	
	// Class for representing a disjunction inheriting from MyFormula.
	public class Disjunction extends MyFormula {
		public Disjunction(Term term) {
			m_term = term;
		}

		@Override
		public Term getTerm() {
			return m_term;
		}
		
		@Override
		public String toString() {
			return m_term.toString();
		}
	}
	
	// Class for representing a negation inheriting from MyFormula.
	public class Negation extends MyFormula {
		public Negation(Term term) {
			m_term = term;
		}
		
		@Override
		public Term getTerm() {
			return m_term;
		}

		@Override
		public String toString() {
			return m_term.toString();
		}
	}
	
	/***********************************************************************//**
	 * Method for building the result automaton with reduced states
	 * and transitions.
	 */
	private void buildResult() {
		m_Result = new NestedWordAutomaton<LETTER, STATE>(
				m_operand.getInternalAlphabet(), null,
				null, m_operand.getStateFactory());
		
		// Get StateFactory from old automaton to build new one.
		StateFactory<STATE> sF = m_operand.getStateFactory();
		// Store new states in ArrayList with size = # blocks in partition.
		HashMap<Block, STATE> blockToNewStates = new HashMap<Block, STATE>(
				computeHashMapCapacity(m_partition.size()));
		
		// Iterate over blocks in m_partition and build new state out of the
		// states belonging to one block. Therefor first get values of HashMap.
		Collection<Block> blocksInPartition = m_partition.values();
		Iterator<Block> it = blocksInPartition.iterator();
		while (it.hasNext()) {
			Block blockOfPartition = it.next();
			s_Logger.info("Block in partition: " + blockOfPartition.toString());
			// Get states of this block;
			Collection<STATE> statesOfBlock = blockOfPartition.returnStates();
			// Build the new state by using the minimize-function of StateFactory.
			STATE newState = sF.minimize(statesOfBlock);
			s_Logger.info("new State: " + newState.toString());
			// Add new state to the new result automaton.
			STATE firstOfBlock = blockOfPartition.get(0);
			// Just add new state if not already exists in new automata.
			if (!blockToNewStates.containsValue(newState)) {
				blockToNewStates.put(blockOfPartition, newState);
				m_Result.addState(
						blockOfPartition.hasInitialState(),
						m_operand.isFinal(firstOfBlock),
						newState);
			}
		}
		
		
		// Iterate over each block to get the outgoing transitions of every
		// first element of block.
		it = blocksInPartition.iterator();
		while (it.hasNext()) {
			// Get block of partition.
			Block blockOfPartition = it.next();
			// Get first state of current block.
			STATE firstOfBlock = blockOfPartition.get(0);
			// As predecessor for the transition take the states created above.
			STATE newPred = blockToNewStates.get(blockOfPartition);
			// Get all outgoing transitions of firstOfBlock for taking all
			// existing successors to build new transitions.
			Iterator<OutgoingInternalTransition<LETTER, STATE>> transitionIt =
					m_operand.internalSuccessors(firstOfBlock).iterator();
			// Iterate over all outgoing transitions of each block to create a
			// new transition add it to the new automaton.
			while (transitionIt.hasNext()) {
				// Get next outgoing transition.
				OutgoingInternalTransition<LETTER, STATE> next = transitionIt.next();
				// Get the successor if the transition.
				STATE succ = next.getSucc();
				// Get block in m_partition succ belongs to.
				Block blockOfSucc = m_partition.get(succ);
				// Get new successor out of new states created above.
				STATE newSucc = blockToNewStates.get(blockOfSucc);
				// Add the new transition to the result automaton.
				m_Result.addInternalTransition(newPred, next.getLetter(), newSucc);
			}
		}
	}
	
	/***********************************************************************//**
	 * Some overridden methods.
	 */
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
	public INestedWordAutomatonSimple<LETTER, STATE> getResult()
			throws OperationCanceledException {
		return m_Result;
	}

	@SuppressWarnings("deprecation")
	@Override
	public final boolean checkResult(final StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		s_Logger.info("Start testing correctness of " + operationName());
		final String message;
		
		if (checkInclusion(m_operand, getResult(), stateFactory)) {
			if (checkInclusion(getResult(), m_operand, stateFactory)) {
				s_Logger.info("Finished testing correctness of " +
						operationName());
				return true;
			}
			else {
				message = "The result recognizes less words than before.";
			}
		}
		else {
			message = "The result recognizes more words than before.";
		}
		
		ResultChecker.writeToFileIfPreferred(
				operationName() + " failed",
				message,
				m_operand);
		return false;
	}
	
	/*******************************************************************//**
	 * This method checks language inclusion of the first automaton with the
	 * second automaton.
	 *  
	 * @param subset automaton describing the subset language
	 * @param superset automaton describing the superset language
	 * @param stateFactory state factory
	 * @return true iff language is included
	 * @throws AutomataLibraryException thrown by inclusion check
	 */
	private final boolean checkInclusion(
			final INestedWordAutomatonSimple<LETTER, STATE> subset,
			final INestedWordAutomatonSimple<LETTER, STATE> superset,
			final StateFactory<STATE> stateFactory)
				throws AutomataLibraryException {
		return ResultChecker.nwaLanguageInclusion(
				ResultChecker.getOldApiNwa(subset),
				ResultChecker.getOldApiNwa(superset),
				stateFactory) == null;
	}
}