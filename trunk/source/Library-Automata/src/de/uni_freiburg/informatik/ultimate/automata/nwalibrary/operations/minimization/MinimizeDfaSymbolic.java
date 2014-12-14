package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;

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
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
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
	private final IUltimateServiceProvider m_Services;
	// Logger for debug - information.
	private static Logger s_Logger = NestedWordAutomata.getLogger();
	// Result automaton.
	private NestedWordAutomaton<LETTER, STATE> m_Result;
	// Input automaton.
	private INestedWordAutomaton<LETTER, STATE> m_operand;

	/***********************************************************************/
	/**
	 * Necessary data elements for computing the minimal DFA.
	 */
	private int m_nOfStates; // number of states.

	private STATE m_initialState; // initial state. In DFA there exists just
									// one.

	private HashMap<STATE, Block> m_partition; // Partition

	private Worklist m_worklist; // Worklist

	private Collection<LETTER> m_alphabet; // alphabet of automaton.

	private HashMap<LETTER, Term> m_letter2Formular;

	private SMTInterpol m_smtInterpol; // Logic solver object.

	private Sort m_bool;

	private Sort[] m_emptyArray;

	/**************************************************************************/

	/***********************************************************************/
	/**
	 * Constructor
	 * 
	 * @param operand
	 */
	public MinimizeDfaSymbolic(IUltimateServiceProvider services,
			INestedWordAutomatonOldApi<LETTER, STATE> operand) {
		m_Services = services;
		this.m_operand = operand;

		// Start minimization.
		System.out.println(startMessage());
		long startTime = System.currentTimeMillis();
		minimizeDfaSymbolic();
		long endTime = System.currentTimeMillis();
		System.out.println(exitMessage());
		s_Logger.info("Symbolic minimization time: " + (endTime - startTime) + " ms.");
	}

	private void minimizeDfaSymbolic() {
		// initialize logic solver and simplifier.
		initializeSolver();

		preprocessingData();

		// initialize partition and worklist.
		initializePartitionAndWorklist();

		/*******************************************************************/
		/**
		 * Start with main algorithm.
		 */
		// While worklist is not empty.
		long mainStartTime = System.currentTimeMillis();
		while (!m_worklist.isEmpty()) {
			// Choose and remove a block r from worklist.
			Block r = m_worklist.pop();
			// Create mapping of predecessor states leading into block r.
			HashMap<STATE, Term> labelMapping = constructMapping(r);
			// Get all predecessors and store into collection s.
			Iterator<STATE> s = labelMapping.keySet().iterator();

			// Building collection of blocks P of m_partition for which is known
			// P intersect with s = NON - EMPTY
			// and P \ s = NON - EMPTY.
			HashMap<Block, Block> relevant = buildIntersectingBlocksMap(s);
			Iterator<Block> relevantIt = relevant.keySet().iterator();
			// iterate over relevant and split m_partition and m_worklist if
			// necessary.
			while (relevantIt.hasNext()) {
				Block p = relevantIt.next();
				Block p1 = relevant.get(p);
				// if p1 is smaller than p, the difference of P\S is non -
				// empty.
				// Remove each state from p1 and change belonging block in
				// m_partition.
				if (p1.size() < p.size()) {
					Iterator<STATE> p1It = p1.iterator();
					while (p1It.hasNext()) {
						STATE belongingState = p1It.next();
						p.remove(belongingState);
						m_partition.put(belongingState, p1);
					}
					// Add new block to worklist, if already contains, or just
					// add the
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
				s = labelMapping.keySet().iterator();
				HashSet<Block> intersectingBlocks = buildIntersectingBlocksSet(s);
				// Iterate over blocks P - for Loop over
				// intersecting blocks in paper.
				Iterator<Block> intersectingBlocksIt = 
						intersectingBlocks.iterator();
				while (intersectingBlocksIt.hasNext()) {
					Block p = intersectingBlocksIt.next();
					Block p1 = new Block();
					// Start with some element of P.
					// Get formula of first state.
					Iterator<STATE> pIterator = p.iterator();
					STATE startState = pIterator.next();
					Term psi = labelMapping.get(startState);
					boolean splitterFound = false;
					p1.add(startState);

					// iterate over rest of currentBlock P. (States).
					while (pIterator.hasNext()) {
						STATE q = pIterator.next();
						// Get formula of current state.
						Term phi = labelMapping.get(q);
						if (splitterFound) {
							Term psiAndPhi = conjunct(psi, phi);
							if (isSatFormula(psiAndPhi)) {
								p1.add(q);
								psi = psiAndPhi;
							}
						} else {
							Term negPhi = negate(phi);
							Term psiAndNegPhi = conjunct(psi, negPhi);
							if (isSatFormula(psiAndNegPhi)) {
								// refine the local minterm.
								psi = psiAndNegPhi;
								splitterFound = true;
							} else { // psi implies phi.
								Term negPsi = negate(psi);
								Term phiAndNegPsi = conjunct(phi, negPsi);
								if (isSatFormula(phiAndNegPsi)) {
									p1.clear();
									p1.add(q);
									psi = phiAndNegPsi;
									splitterFound = true;
								} else {
									p1.add(q);
								}
							}
						}
					}
					// If p1 < p. The difference of P\P1 is not - empty.
					if (p1.size() < p.size()) {
						iterate = (iterate || (p.size() > 2));
						// Remove each state from p1 and change belonging
						// block in m_partition.
						Iterator<STATE> p1It = p1.iterator();
						while (p1It.hasNext()) {
							STATE belongingBlock = p1It.next();
							p.remove(belongingBlock);
							m_partition.put(belongingBlock, p1);
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
		/*******************************************************************/
		/**
		 * New automaton should be ready, build the result automaton.
		 */
		buildResult();
		long mainEndTime = System.currentTimeMillis();
		s_Logger.info("Symbolic main time: " + (mainEndTime - mainStartTime) + " ms");
	}

	/**
	 * Get number of states and labels for calling initializeMappings and
	 * initializeLables.
	 */
	private void preprocessingData() {
		m_nOfStates = m_operand.getStates().size();

		// There is only one initial state in a DFA.
		m_initialState = m_operand.getInitialStates().iterator().next();

		// get internal alphabet of m_operand.
		m_alphabet = m_operand.getInternalAlphabet();

		// iterate over whole alphabet and construct letter --> atom mapping.
		Iterator<LETTER> alphabetIt = m_alphabet.iterator();
		m_letter2Formular = new HashMap<LETTER, Term>(
				computeHashMapCapacity(m_alphabet.size()));
		while (alphabetIt.hasNext()) {
			LETTER letter = alphabetIt.next();
			try {
				m_smtInterpol.declareFun(letter.toString(), m_emptyArray,
						m_bool);
			} catch (SMTLIBException e) {
				s_Logger.error(
						"Function already exists! Not able to build twice!", e);
			}
			Term var = m_smtInterpol.term(letter.toString());
			m_letter2Formular.put(letter, var);

		}
	}

	private void initializePartitionAndWorklist() {
		// First create initial partition. Therefor create block with final
		// states and block with nonfinal states.
		Block finalStates = new Block();
		Block nonFinalStates = new Block();
		// Iterate over all states of m_operand and sort states either to
		// finaslStates - block or to nonfinalStates - Block.
		// Therby also create Mapping STATE --> Block.
		m_partition = new HashMap<STATE, Block>(
				computeHashMapCapacity(m_nOfStates));
		Iterator<STATE> allStatesIt = m_operand.getStates().iterator();
		while (allStatesIt.hasNext()) {
			STATE st = allStatesIt.next();
			if (m_operand.isFinal(st)) {
				finalStates.add(st);
				m_partition.put(st, finalStates);
			} else {
				nonFinalStates.add(st);
				m_partition.put(st, nonFinalStates);
			}
		}

		// Second, create initial Worklist.
		m_worklist = new Worklist(2);
		m_worklist.push(finalStates);
		m_worklist.push(nonFinalStates);
	}

	private void initializeSolver() {
		m_smtInterpol = new SMTInterpol();

		// Set logic of solver object.
		m_smtInterpol.setLogic(Logics.QF_UF);

		m_bool = m_smtInterpol.sort("Bool");
		m_emptyArray = new Sort[] {};
	}

	// Construct mapping for transitions of predecessor states leading into
	// block r.
	private HashMap<STATE, Term> constructMapping(Block r) {
		// create HashMap with max size of number of states.
		HashMap<STATE, Term> retMap = new HashMap<STATE, Term>(
				computeHashMapCapacity(m_nOfStates));

		// Iterate over all containing states of block r.
		Iterator<STATE> rIt = r.iterator();
		while (rIt.hasNext()) {
			STATE st = rIt.next();
			// All letters over incoming transitions.
			Set<LETTER> incomingLabels = m_operand.lettersInternalIncoming(st);
			// Iterating over all incoming transitions and build term.
			Iterator<LETTER> incomingLabelsIt = incomingLabels.iterator();
			while (incomingLabelsIt.hasNext()) {
				LETTER letter = incomingLabelsIt.next();
				assert (hasIncomingTransitionWithLetter(st, letter)); 
				// Get all predecessors with transition into state
				// labled with letter.
				Collection<STATE> predecessors = getPredecessor(st, letter);
				Term atomLetter = m_letter2Formular.get(letter);
				// Iterate over predecessors.
				Iterator<STATE> predIt = predecessors.iterator();
				while (predIt.hasNext()) {
					STATE pred = predIt.next();
					Term existingTermOfPred = retMap.get(pred);
					if (existingTermOfPred != null) {
						// HashMap contains pred already.
						// Just add formula as disjunction.
						retMap.put(pred,
								disjunct(atomLetter, existingTermOfPred));
					} else {
						// HashMap does not contain pred yet. Add new key.
						retMap.put(pred, atomLetter);
					}
				}
			}
		}
		return retMap;
	}

	private HashSet<Block> buildIntersectingBlocksSet(Iterator<STATE> s) {
		HashSet<Block> ret = new HashSet<Block>(m_nOfStates);
		// Iterate over STATEs in s and lookup to which block they belong to.
		while (s.hasNext()) {
			Block block = m_partition.get(s.next());
			// If ArrayList<Block> already contains block do not add twice.
			if (!ret.contains(block)) {
				ret.add(block);
			}
		}
		return ret;
	}

	private HashMap<Block, Block> buildIntersectingBlocksMap(Iterator<STATE> s) {
		HashMap<Block, Block> ret = new HashMap<Block, Block>(
				computeHashMapCapacity(m_nOfStates));
		// Lookup all Blocks to which the STATEs of s belong to and add to Map.
		while (s.hasNext()) {
			STATE sState = s.next();
			Block block = m_partition.get(sState);
			if (ret.containsKey(block)) {
				// Block is already existing in Map. Just add the state.
				ret.get(block).add(sState);
			} else {
				// Block does not exist already in Map. Create new Block with
				// this first state in it.
				Block b = new Block();
				b.add(sState);
				ret.put(block, b);
			}
		}
		return ret;
	}

	/**
	 * Returns true, if there exists an incoming transition to state labeled
	 * with letter letter.
	 * 
	 * @param state
	 * @param letter
	 * @return if incoming transition labeled with letter exists.
	 */
	private boolean hasIncomingTransitionWithLetter(STATE state, LETTER letter) {
		return m_operand.internalPredecessors(letter, state).iterator()
				.hasNext();
	}

	/**
	 * Returns state, which is predecessors of state with transition labeled
	 * with letter.
	 * 
	 * @param state
	 * @param letter
	 * @return predecessor state.
	 */
	private LinkedList<STATE> getPredecessor(STATE state, LETTER letter) {
		LinkedList<STATE> ret = new LinkedList<STATE>();
		Iterator<IncomingInternalTransition<LETTER, STATE>> it = m_operand
				.internalPredecessors(letter, state).iterator();
		while (it.hasNext()) {
			ret.add(it.next().getPred());
		}
		return ret;
	}

	// Create a conjunction from a collection of formulas.
	private Term conjunct(Term f1, Term f2) {
		Term[] conjuncts = new Term[2];
		conjuncts[0] = f1;
		conjuncts[1] = f2;
		Term con = m_smtInterpol.term("and", conjuncts);
		return con;
	}

	// Create a disjunction from a collection of formulas.
	private Term disjunct(Term f1, Term f2) {
		Term[] disjuncts = new Term[2];
		disjuncts[0] = f1;
		disjuncts[1] = f2;
		Term dis = m_smtInterpol.term("or", disjuncts);
		return dis;
	}

	// Negate a given formula.
	private Term negate(Term formula) {
		Term[] negation = new Term[1];
		negation[0] = formula;
		Term neg = m_smtInterpol.term("not", negation);
		return neg;
	}

	private boolean isSatFormula(Term formula) {
		m_smtInterpol.push(1);
		m_smtInterpol.assertTerm(formula);

		LBool isSat = m_smtInterpol.checkSat();
		m_smtInterpol.pop(1);
		return (isSat == LBool.SAT);
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

	/***********************************************************************/
	/**
	 * Class for representing worklist.
	 * 
	 * @author bjoern
	 */
	public class Worklist {
		private HashSet<Block> m_setsOfStates;

		// Constructor. Initialize an empty LinkedList<Block>.
		public Worklist(int size) {
			m_setsOfStates = new HashSet<Block>(size);
		}

		// Pop first element of worklist.
		public Block pop() {
			if (m_setsOfStates.size() <= 0)
				return null;
			Block toPop = m_setsOfStates.iterator().next();
			m_setsOfStates.remove(toPop);
			return toPop;
		}

		// Push element into worklist.
		public void push(Block block) {
			m_setsOfStates.add(block);
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
			return m_setsOfStates.size();
		}

		// Returns if Worklist is currently empty or not.
		public boolean isEmpty() {
			return m_setsOfStates.isEmpty();
		}

		public String toString() {
			String ret = "(";
			Iterator<Block> it = m_setsOfStates.iterator();
			while (it.hasNext()) {
				ret += it.next().toString();
			}
			ret += ")";
			return ret;
		}

	}

	/***********************************************************************/
	/**
	 * Class for representing a block of states.
	 * 
	 * @author bjoern
	 *
	 */
	public class Block {
		private HashSet<STATE> m_states;

		// Constructor.
		public Block(Collection<STATE> block) {
			// create new ArrayList<STATE> with allocated space.
			m_states = new HashSet<STATE>(block.size());
			Iterator<STATE> it = block.iterator();
			while (it.hasNext()) {
				m_states.add(it.next());
			}
		}

		// Copy constructor.
		public Block(Block block) {
			this(block.returnStates());
		}

		// Default constructor. Just allocates space for HashSet<STATE>
		// m_states.
		public Block() {
			m_states = new HashSet<STATE>(m_nOfStates);
		}

		// Remove state <st> from block.
		public boolean remove(STATE st) {
			return m_states.remove(st);
		}

		// Add state <st> to block.
		public void add(STATE st) {
			m_states.add(st);
		}

		// Clear current block.
		public void clear() {
			m_states.clear();
		}

		// Returns iterator for Block - Object.
		public Iterator<STATE> iterator() {
			return m_states.iterator();
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

		public HashSet<STATE> returnStates() {
			return m_states;
		}

		public String toString() {
			String ret = "(";
			Iterator<STATE> it = m_states.iterator();
			while (it.hasNext()) {
				ret += "{";
				ret += it.next().toString();
				ret += "}";
			}
			ret += ")";
			return ret;
		}
	}

	/***********************************************************************/
	/**
	 * Method for building the result automaton with reduced states and
	 * transitions.
	 */
	private void buildResult() {
		m_Result = new NestedWordAutomaton<LETTER, STATE>(m_Services,
				m_operand.getInternalAlphabet(), null, null,
				m_operand.getStateFactory());

		// Get StateFactory from old automaton to build new one.
		StateFactory<STATE> sF = m_operand.getStateFactory();
		// Store new states in ArrayList with size = # blocks in partition.
		HashMap<Block, STATE> blockToNewStates = new HashMap<Block, STATE>(
				computeHashMapCapacity(m_partition.size()));

		Block blockWithinInitialState = m_partition.get(m_initialState);
		// Iterate over blocks in m_partition and build new state out of the
		// states belonging to one block. Therefor first get values of HashMap.
		Collection<Block> blocksInPartition = m_partition.values();
		Iterator<Block> it = blocksInPartition.iterator();
		HashSet<Block> alreadyLookedUp = new HashSet<Block>(
				blocksInPartition.size());
		while (it.hasNext()) {
			Block blockOfPartition = it.next();
			if (alreadyLookedUp.contains(blockOfPartition)) {
				// State for this block was already created.
				continue;
			}
			alreadyLookedUp.add(blockOfPartition);
			// Get states of this block;
			Collection<STATE> statesOfBlock = blockOfPartition.returnStates();
			// Build the new state by using the minimize-function of
			// StateFactory.
			STATE newState = sF.minimize(statesOfBlock);
			// Add new state to the new result automaton.
			STATE firstOfBlock = blockOfPartition.iterator().next();
			blockToNewStates.put(blockOfPartition, newState);
			m_Result.addState(blockOfPartition == blockWithinInitialState,
					m_operand.isFinal(firstOfBlock), newState);
		}

		// Iterate over each block to get the outgoing transitions of every
		// first element of block.
		it = blocksInPartition.iterator();
		while (it.hasNext()) {
			// Get block of partition.
			Block blockOfPartition = it.next();
			// Get first state of current block.
			STATE firstOfBlock = blockOfPartition.iterator().next();
			// As predecessor for the transition take the states created above.
			STATE newPred = blockToNewStates.get(blockOfPartition);
			// Get all outgoing transitions of firstOfBlock for taking all
			// existing successors to build new transitions.
			Iterator<OutgoingInternalTransition<LETTER, STATE>> transitionIt = m_operand
					.internalSuccessors(firstOfBlock).iterator();
			// Iterate over all outgoing transitions of each block to create a
			// new transition add it to the new automaton.
			while (transitionIt.hasNext()) {
				// Get next outgoing transition.
				OutgoingInternalTransition<LETTER, STATE> next = transitionIt
						.next();
				// Get the successor if the transition.
				STATE succ = next.getSucc();
				// Get block in m_partition succ belongs to.
				Block blockOfSucc = m_partition.get(succ);
				// Get new successor out of new states created above.
				STATE newSucc = blockToNewStates.get(blockOfSucc);
				// Add the new transition to the result automaton.
				m_Result.addInternalTransition(newPred, next.getLetter(),
						newSucc);
			}
		}
	}

	/***********************************************************************/
	/**
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
	public INestedWordAutomaton<LETTER, STATE> getResult()
			throws OperationCanceledException {
		return m_Result;
	}

	@Override
	public final boolean checkResult(final StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		s_Logger.info("Start testing correctness of " + operationName());
		final String message;

		if (checkInclusion(m_operand, getResult(), stateFactory)) {
			if (checkInclusion(getResult(), m_operand, stateFactory)) {
				s_Logger.info("Finished testing correctness of "
						+ operationName());
				return true;
			} else {
				message = "The result recognizes less words than before.";
			}
		} else {
			message = "The result recognizes more words than before.";
		}

		ResultChecker.writeToFileIfPreferred(m_Services, operationName()
				+ " failed", message, m_operand);
		return false;
	}

	/*******************************************************************/
	/**
	 * This method checks language inclusion of the first automaton with the
	 * second automaton.
	 * 
	 * @param subset
	 *            automaton describing the subset language
	 * @param superset
	 *            automaton describing the superset language
	 * @param stateFactory
	 *            state factory
	 * @return true iff language is included
	 * @throws AutomataLibraryException
	 *             thrown by inclusion check
	 */
	private final boolean checkInclusion(
			final INestedWordAutomatonSimple<LETTER, STATE> subset,
			final INestedWordAutomatonSimple<LETTER, STATE> superset,
			final StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		return ResultChecker.nwaLanguageInclusion(m_Services,
				ResultChecker.getOldApiNwa(m_Services, subset),
				ResultChecker.getOldApiNwa(m_Services, superset), stateFactory) == null;
	}
}