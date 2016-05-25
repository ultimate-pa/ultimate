/*
 * Copyright (C) 2014-2015 Björn Hagemeister
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
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
public class MinimizeDfaSymbolic<LETTER, STATE> implements IOperation<LETTER, STATE> {
	private final AutomataLibraryServices mServices;
	// ILogger for debug - information.
	private final ILogger mLogger;
	// Result automaton.
	private NestedWordAutomaton<LETTER, STATE> mResult;
	// Input automaton.
	private final INestedWordAutomaton<LETTER, STATE> moperand;

	/***********************************************************************/
	/**
	 * Necessary data elements for computing the minimal DFA.
	 */
	private int mnOfStates; // number of states.

	private STATE minitialState; // initial state. In DFA there exists just
									// one.

	private HashMap<STATE, Block> mpartition; // Partition

	private Worklist mworklist; // Worklist

	private Collection<LETTER> malphabet; // alphabet of automaton.

	private HashMap<LETTER, Term> mletter2Formular;

	private SMTInterpol msmtInterpol; // Logic solver object.

	private Sort mbool;

	private Sort[] memptyArray;

	/**************************************************************************/

	/***********************************************************************/
	/**
	 * Constructor
	 * 
	 * @param operand
	 */
	public MinimizeDfaSymbolic(AutomataLibraryServices services, INestedWordAutomatonOldApi<LETTER, STATE> operand) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		this.moperand = operand;

		// Start minimization.
		System.out.println(startMessage());
		final long startTime = System.currentTimeMillis();
		minimizeDfaSymbolic();
		final long endTime = System.currentTimeMillis();
		System.out.println(exitMessage());
		mLogger.info("Symbolic minimization time: " + (endTime - startTime) + " ms.");
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
		final long mainStartTime = System.currentTimeMillis();
		while (!mworklist.isEmpty()) {
			// Choose and remove a block r from worklist.
			final Block r = mworklist.pop();
			// Create mapping of predecessor states leading into block r.
			final HashMap<STATE, Term> labelMapping = constructMapping(r);
			// Get all predecessors and store into collection s.
			Iterator<STATE> s = labelMapping.keySet().iterator();

			// Building collection of blocks P of mpartition for which is known
			// P intersect with s = NON - EMPTY
			// and P \ s = NON - EMPTY.
			final HashMap<Block, Block> relevant = buildIntersectingBlocksMap(s);
			final Iterator<Block> relevantIt = relevant.keySet().iterator();
			// iterate over relevant and split mpartition and mworklist if
			// necessary.
			while (relevantIt.hasNext()) {
				final Block p = relevantIt.next();
				final Block p1 = relevant.get(p);
				// if p1 is smaller than p, the difference of P\S is non -
				// empty.
				// Remove each state from p1 and change belonging block in
				// mpartition.
				if (p1.size() < p.size()) {
					final Iterator<STATE> p1It = p1.iterator();
					while (p1It.hasNext()) {
						final STATE belongingState = p1It.next();
						p.remove(belongingState);
						mpartition.put(belongingState, p1);
					}
					// Add new block to worklist, if already contains, or just
					// add the
					// smaller one.
					if (mworklist.contains(p)) {
						mworklist.push(p1);
					} else {
						if (p.size() <= p1.size()) {
							mworklist.push(p);
						} else {
							mworklist.push(p1);
						}
					}
				}
			}

			boolean iterate = true;
			while (iterate) {
				iterate = false;
				// Create blocks P from mpartition, which are non - empty after
				// intersecting with block s.
				s = labelMapping.keySet().iterator();
				final HashSet<Block> intersectingBlocks = buildIntersectingBlocksSet(s);
				// Iterate over blocks P - for Loop over
				// intersecting blocks in paper.
				final Iterator<Block> intersectingBlocksIt = intersectingBlocks.iterator();
				while (intersectingBlocksIt.hasNext()) {
					final Block p = intersectingBlocksIt.next();
					final Block p1 = new Block();
					// Start with some element of P.
					// Get formula of first state.
					final Iterator<STATE> pIterator = p.iterator();
					final STATE startState = pIterator.next();
					Term psi = labelMapping.get(startState);
					boolean splitterFound = false;
					p1.add(startState);

					// iterate over rest of currentBlock P. (States).
					while (pIterator.hasNext()) {
						final STATE q = pIterator.next();
						// Get formula of current state.
						final Term phi = labelMapping.get(q);
						if (splitterFound) {
							final Term psiAndPhi = conjunct(psi, phi);
							if (isSatFormula(psiAndPhi)) {
								p1.add(q);
								psi = psiAndPhi;
							}
						} else {
							final Term negPhi = negate(phi);
							final Term psiAndNegPhi = conjunct(psi, negPhi);
							if (isSatFormula(psiAndNegPhi)) {
								// refine the local minterm.
								psi = psiAndNegPhi;
								splitterFound = true;
							} else { // psi implies phi.
								final Term negPsi = negate(psi);
								final Term phiAndNegPsi = conjunct(phi, negPsi);
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
						// block in mpartition.
						final Iterator<STATE> p1It = p1.iterator();
						while (p1It.hasNext()) {
							final STATE belongingBlock = p1It.next();
							p.remove(belongingBlock);
							mpartition.put(belongingBlock, p1);
						}
						// Check if worklist already contains block p.
						// If yes, add p1 too, if not, add the smaller one.
						if (mworklist.contains(p)) {
							mworklist.push(p1);
						} else if (p.size() <= p1.size()) {
							mworklist.push(p);
						} else {
							mworklist.push(p1);
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
		final long mainEndTime = System.currentTimeMillis();
		mLogger.info("Symbolic main time: " + (mainEndTime - mainStartTime) + " ms");
	}

	/**
	 * Get number of states and labels for calling initializeMappings and
	 * initializeLables.
	 */
	private void preprocessingData() {
		mnOfStates = moperand.getStates().size();

		// There is only one initial state in a DFA.
		minitialState = moperand.getInitialStates().iterator().next();

		// get internal alphabet of moperand.
		malphabet = moperand.getInternalAlphabet();

		// iterate over whole alphabet and construct letter --> atom mapping.
		final Iterator<LETTER> alphabetIt = malphabet.iterator();
		mletter2Formular = new HashMap<LETTER, Term>(computeHashMapCapacity(malphabet.size()));
		while (alphabetIt.hasNext()) {
			final LETTER letter = alphabetIt.next();
			try {
				msmtInterpol.declareFun(letter.toString(), memptyArray, mbool);
			} catch (final SMTLIBException e) {
				mLogger.error("Function already exists! Not able to build twice!", e);
			}
			final Term var = msmtInterpol.term(letter.toString());
			mletter2Formular.put(letter, var);

		}
	}

	private void initializePartitionAndWorklist() {
		// First create initial partition. Therefor create block with final
		// states and block with nonfinal states.
		final Block finalStates = new Block();
		final Block nonFinalStates = new Block();
		// Iterate over all states of moperand and sort states either to
		// finaslStates - block or to nonfinalStates - Block.
		// Therby also create Mapping STATE --> Block.
		mpartition = new HashMap<STATE, Block>(computeHashMapCapacity(mnOfStates));
		final Iterator<STATE> allStatesIt = moperand.getStates().iterator();
		while (allStatesIt.hasNext()) {
			final STATE st = allStatesIt.next();
			if (moperand.isFinal(st)) {
				finalStates.add(st);
				mpartition.put(st, finalStates);
			} else {
				nonFinalStates.add(st);
				mpartition.put(st, nonFinalStates);
			}
		}

		// Second, create initial Worklist.
		mworklist = new Worklist(2);
		mworklist.push(finalStates);
		mworklist.push(nonFinalStates);
	}

	private void initializeSolver() {
		msmtInterpol = new SMTInterpol();

		// Set logic of solver object.
		msmtInterpol.setLogic(Logics.QF_UF);

		mbool = msmtInterpol.sort("Bool");
		memptyArray = new Sort[] {};
		throw new UnsupportedOperationException("Contact DD about creating SMTInterpol without SolverBuilder");
	}

	// Construct mapping for transitions of predecessor states leading into
	// block r.
	private HashMap<STATE, Term> constructMapping(Block r) {
		// create HashMap with max size of number of states.
		final HashMap<STATE, Term> retMap = new HashMap<STATE, Term>(computeHashMapCapacity(mnOfStates));

		// Iterate over all containing states of block r.
		final Iterator<STATE> rIt = r.iterator();
		while (rIt.hasNext()) {
			final STATE st = rIt.next();
			// All letters over incoming transitions.
			final Set<LETTER> incomingLabels = moperand.lettersInternalIncoming(st);
			// Iterating over all incoming transitions and build term.
			final Iterator<LETTER> incomingLabelsIt = incomingLabels.iterator();
			while (incomingLabelsIt.hasNext()) {
				final LETTER letter = incomingLabelsIt.next();
				assert (hasIncomingTransitionWithLetter(st, letter));
				// Get all predecessors with transition into state
				// labled with letter.
				final Collection<STATE> predecessors = getPredecessor(st, letter);
				final Term atomLetter = mletter2Formular.get(letter);
				// Iterate over predecessors.
				final Iterator<STATE> predIt = predecessors.iterator();
				while (predIt.hasNext()) {
					final STATE pred = predIt.next();
					final Term existingTermOfPred = retMap.get(pred);
					if (existingTermOfPred != null) {
						// HashMap contains pred already.
						// Just add formula as disjunction.
						retMap.put(pred, disjunct(atomLetter, existingTermOfPred));
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
		final HashSet<Block> ret = new HashSet<Block>(mnOfStates);
		// Iterate over STATEs in s and lookup to which block they belong to.
		while (s.hasNext()) {
			final Block block = mpartition.get(s.next());
			// If ArrayList<Block> already contains block do not add twice.
			if (!ret.contains(block)) {
				ret.add(block);
			}
		}
		return ret;
	}

	private HashMap<Block, Block> buildIntersectingBlocksMap(Iterator<STATE> s) {
		final HashMap<Block, Block> ret = new HashMap<Block, Block>(computeHashMapCapacity(mnOfStates));
		// Lookup all Blocks to which the STATEs of s belong to and add to Map.
		while (s.hasNext()) {
			final STATE sState = s.next();
			final Block block = mpartition.get(sState);
			if (ret.containsKey(block)) {
				// Block is already existing in Map. Just add the state.
				ret.get(block).add(sState);
			} else {
				// Block does not exist already in Map. Create new Block with
				// this first state in it.
				final Block b = new Block();
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
		return moperand.internalPredecessors(letter, state).iterator().hasNext();
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
		final LinkedList<STATE> ret = new LinkedList<STATE>();
		final Iterator<IncomingInternalTransition<LETTER, STATE>> it = moperand.internalPredecessors(letter, state)
				.iterator();
		while (it.hasNext()) {
			ret.add(it.next().getPred());
		}
		return ret;
	}

	// Create a conjunction from a collection of formulas.
	private Term conjunct(Term f1, Term f2) {
		final Term[] conjuncts = new Term[2];
		conjuncts[0] = f1;
		conjuncts[1] = f2;
		final Term con = msmtInterpol.term("and", conjuncts);
		return con;
	}

	// Create a disjunction from a collection of formulas.
	private Term disjunct(Term f1, Term f2) {
		final Term[] disjuncts = new Term[2];
		disjuncts[0] = f1;
		disjuncts[1] = f2;
		final Term dis = msmtInterpol.term("or", disjuncts);
		return dis;
	}

	// Negate a given formula.
	private Term negate(Term formula) {
		final Term[] negation = new Term[1];
		negation[0] = formula;
		final Term neg = msmtInterpol.term("not", negation);
		return neg;
	}

	private boolean isSatFormula(Term formula) {
		msmtInterpol.push(1);
		msmtInterpol.assertTerm(formula);

		final LBool isSat = msmtInterpol.checkSat();
		msmtInterpol.pop(1);
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
		private final HashSet<Block> msetsOfStates;

		// Constructor. Initialize an empty LinkedList<Block>.
		public Worklist(int size) {
			msetsOfStates = new HashSet<Block>(size);
		}

		// Pop first element of worklist.
		public Block pop() {
			if (msetsOfStates.size() <= 0) {
				return null;
			}
			final Block toPop = msetsOfStates.iterator().next();
			msetsOfStates.remove(toPop);
			return toPop;
		}

		// Push element into worklist.
		public void push(Block block) {
			msetsOfStates.add(block);
		}

		// Remove given block from worklist.
		public boolean remove(Block block) {
			return msetsOfStates.remove(block);
		}

		// Returns if worklist contains given block or not.
		public boolean contains(Block block) {
			return msetsOfStates.contains(block);
		}

		// Return current size of Worklist.
		public int size() {
			return msetsOfStates.size();
		}

		// Returns if Worklist is currently empty or not.
		public boolean isEmpty() {
			return msetsOfStates.isEmpty();
		}

		@Override
		public String toString() {
			String ret = "(";
			final Iterator<Block> it = msetsOfStates.iterator();
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
		private HashSet<STATE> mstates;

		// Constructor.
		public Block(Collection<STATE> block) {
			// create new ArrayList<STATE> with allocated space.
			mstates = new HashSet<STATE>(block.size());
			final Iterator<STATE> it = block.iterator();
			while (it.hasNext()) {
				mstates.add(it.next());
			}
		}

		// Copy constructor.
		public Block(Block block) {
			this(block.returnStates());
		}

		// Default constructor. Just allocates space for HashSet<STATE>
		// mstates.
		public Block() {
			mstates = new HashSet<STATE>(mnOfStates);
		}

		// Remove state <st> from block.
		public boolean remove(STATE st) {
			return mstates.remove(st);
		}

		// Add state <st> to block.
		public void add(STATE st) {
			mstates.add(st);
		}

		// Clear current block.
		public void clear() {
			mstates.clear();
		}

		// Returns iterator for Block - Object.
		public Iterator<STATE> iterator() {
			return mstates.iterator();
		}

		// Returns current size of block.
		public int size() {
			return mstates.size();
		}

		// Returns if block contains currently state <state> or not.
		public boolean contains(STATE state) {
			return mstates.contains(state);
		}

		// Returns if block is currently empty or not.
		public boolean isEmpty() {
			return mstates.isEmpty();
		}

		public HashSet<STATE> returnStates() {
			return mstates;
		}

		@Override
		public String toString() {
			String ret = "(";
			final Iterator<STATE> it = mstates.iterator();
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
		mResult = new NestedWordAutomaton<LETTER, STATE>(mServices, moperand.getInternalAlphabet(), null, null,
				moperand.getStateFactory());

		// Get StateFactory from old automaton to build new one.
		final StateFactory<STATE> sF = moperand.getStateFactory();
		// Store new states in ArrayList with size = # blocks in partition.
		final HashMap<Block, STATE> blockToNewStates = new HashMap<Block, STATE>(computeHashMapCapacity(mpartition.size()));

		final Block blockWithinInitialState = mpartition.get(minitialState);
		// Iterate over blocks in mpartition and build new state out of the
		// states belonging to one block. Therefor first get values of HashMap.
		final Collection<Block> blocksInPartition = mpartition.values();
		Iterator<Block> it = blocksInPartition.iterator();
		final HashSet<Block> alreadyLookedUp = new HashSet<Block>(blocksInPartition.size());
		while (it.hasNext()) {
			final Block blockOfPartition = it.next();
			if (alreadyLookedUp.contains(blockOfPartition)) {
				// State for this block was already created.
				continue;
			}
			alreadyLookedUp.add(blockOfPartition);
			// Get states of this block;
			final Collection<STATE> statesOfBlock = blockOfPartition.returnStates();
			// Build the new state by using the minimize-function of
			// StateFactory.
			final STATE newState = sF.minimize(statesOfBlock);
			// Add new state to the new result automaton.
			final STATE firstOfBlock = blockOfPartition.iterator().next();
			blockToNewStates.put(blockOfPartition, newState);
			mResult.addState(blockOfPartition == blockWithinInitialState, moperand.isFinal(firstOfBlock), newState);
		}

		// Iterate over each block to get the outgoing transitions of every
		// first element of block.
		it = blocksInPartition.iterator();
		while (it.hasNext()) {
			// Get block of partition.
			final Block blockOfPartition = it.next();
			// Get first state of current block.
			final STATE firstOfBlock = blockOfPartition.iterator().next();
			// As predecessor for the transition take the states created above.
			final STATE newPred = blockToNewStates.get(blockOfPartition);
			// Get all outgoing transitions of firstOfBlock for taking all
			// existing successors to build new transitions.
			final Iterator<OutgoingInternalTransition<LETTER, STATE>> transitionIt = moperand.internalSuccessors(
					firstOfBlock).iterator();
			// Iterate over all outgoing transitions of each block to create a
			// new transition add it to the new automaton.
			while (transitionIt.hasNext()) {
				// Get next outgoing transition.
				final OutgoingInternalTransition<LETTER, STATE> next = transitionIt.next();
				// Get the successor if the transition.
				final STATE succ = next.getSucc();
				// Get block in mpartition succ belongs to.
				final Block blockOfSucc = mpartition.get(succ);
				// Get new successor out of new states created above.
				final STATE newSucc = blockToNewStates.get(blockOfSucc);
				// Add the new transition to the result automaton.
				mResult.addInternalTransition(newPred, next.getLetter(), newSucc);
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
	public INestedWordAutomaton<LETTER, STATE> getResult() throws AutomataLibraryException {
		return mResult;
	}

	@Override
	public final boolean checkResult(final StateFactory<STATE> stateFactory) throws AutomataLibraryException {
		mLogger.info("Start testing correctness of " + operationName());
		final String message;

		if (checkInclusion(moperand, getResult(), stateFactory)) {
			if (checkInclusion(getResult(), moperand, stateFactory)) {
				mLogger.info("Finished testing correctness of " + operationName());
				return true;
			} else {
				message = "The result recognizes less words than before.";
			}
		} else {
			message = "The result recognizes more words than before.";
		}

		ResultChecker.writeToFileIfPreferred(mServices, operationName() + " failed", message, moperand);
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
	private final boolean checkInclusion(final INestedWordAutomatonSimple<LETTER, STATE> subset,
			final INestedWordAutomatonSimple<LETTER, STATE> superset, final StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		return ResultChecker.nwaLanguageInclusion(mServices, ResultChecker.getOldApiNwa(mServices, subset),
				ResultChecker.getOldApiNwa(mServices, superset), stateFactory) == null;
	}
}
