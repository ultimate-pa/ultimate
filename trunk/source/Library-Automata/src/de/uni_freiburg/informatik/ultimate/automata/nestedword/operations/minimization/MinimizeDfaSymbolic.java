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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 * Class for minimize deterministic finite automaton by the Hopcroft - Algorithm.
 * 
 * @author Björn Hagemeister
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class MinimizeDfaSymbolic<LETTER, STATE> extends AbstractMinimizeNwa<LETTER, STATE> {
	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	/***********************************************************************/
	/**
	 * Necessary data elements for computing the minimal DFA.
	 */
	// number of states.
	private int mNumberOfStates;
	// initial state. In DFA there exists just one.
	private STATE mInitialState;
	// Partition
	private HashMap<STATE, Block> mPartition;
	// Worklist
	private Worklist mWorklist;
	
	private HashMap<LETTER, Term> mLetter2Formular;
	// Logic solver object.
	private SMTInterpol mSmtInterpol;
	
	private Sort mBool;
	
	private Sort[] mEmptyArray;
	
	/**************************************************************************/
	
	/***********************************************************************/
	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 */
	public <FACTORY extends IMergeStateFactory<STATE> & IEmptyStackStateFactory<STATE>> MinimizeDfaSymbolic(
			final AutomataLibraryServices services, final FACTORY stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand) {
		super(services, stateFactory);
		mOperand = operand;
		
		// Start minimization.
		printStartMessage();
		
		final long startTime = System.currentTimeMillis();
		minimizeDfaSymbolic();
		final long endTime = System.currentTimeMillis();
		mLogger.info("Symbolic minimization time: " + (endTime - startTime) + " ms.");
		
		printExitMessage();
	}
	
	@Override
	protected INestedWordAutomaton<LETTER, STATE> getOperand() {
		return mOperand;
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
		final long mainStartTime = System.currentTimeMillis();
		runLoop();
		
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
		mNumberOfStates = mOperand.size();
		
		// There is only one initial state in a DFA.
		mInitialState = mOperand.getInitialStates().iterator().next();
		
		// get internal alphabet of moperand.
		final Collection<LETTER> alphabet = mOperand.getInternalAlphabet();
		
		// iterate over whole alphabet and construct letter --> atom mapping.
		final Iterator<LETTER> alphabetIt = alphabet.iterator();
		mLetter2Formular = new HashMap<>(computeHashCap(alphabet.size()));
		while (alphabetIt.hasNext()) {
			final LETTER letter = alphabetIt.next();
			try {
				mSmtInterpol.declareFun(letter.toString(), mEmptyArray, mBool);
			} catch (final SMTLIBException e) {
				mLogger.error("Function already exists! Not able to build twice!", e);
			}
			final Term var = mSmtInterpol.term(letter.toString());
			mLetter2Formular.put(letter, var);
			
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
		mPartition = new HashMap<>(computeHashCap(mNumberOfStates));
		final Iterator<STATE> allStatesIt = mOperand.getStates().iterator();
		while (allStatesIt.hasNext()) {
			final STATE st = allStatesIt.next();
			if (mOperand.isFinal(st)) {
				finalStates.add(st);
				mPartition.put(st, finalStates);
			} else {
				nonFinalStates.add(st);
				mPartition.put(st, nonFinalStates);
			}
		}
		
		// Second, create initial Worklist.
		mWorklist = new Worklist(2);
		mWorklist.push(finalStates);
		mWorklist.push(nonFinalStates);
	}
	
	private void runLoop() {
		// While worklist is not empty.
		while (!mWorklist.isEmpty()) {
			// Choose and remove a block r from worklist.
			final Block r = mWorklist.pop();
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
						mPartition.put(belongingState, p1);
					}
					// Add new block to worklist, if already contains, or just
					// add the
					// smaller one.
					if (mWorklist.contains(p)) {
						mWorklist.push(p1);
					} else {
						if (p.size() <= p1.size()) {
							mWorklist.push(p);
						} else {
							mWorklist.push(p1);
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
							} else {
								// psi implies phi.
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
						iterate = iterate || (p.size() > 2);
						// Remove each state from p1 and change belonging
						// block in mpartition.
						final Iterator<STATE> p1It = p1.iterator();
						while (p1It.hasNext()) {
							final STATE belongingBlock = p1It.next();
							p.remove(belongingBlock);
							mPartition.put(belongingBlock, p1);
						}
						// Check if worklist already contains block p.
						// If yes, add p1 too, if not, add the smaller one.
						if (mWorklist.contains(p)) {
							mWorklist.push(p1);
						} else if (p.size() <= p1.size()) {
							mWorklist.push(p);
						} else {
							mWorklist.push(p1);
						}
					}
				}
			}
		}
	}
	
	private void initializeSolver() {
		mSmtInterpol = new SMTInterpol();
		
		// Set logic of solver object.
		mSmtInterpol.setLogic(Logics.QF_UF);
		
		mBool = mSmtInterpol.sort("Bool");
		mEmptyArray = new Sort[] {};
		throw new UnsupportedOperationException("Contact DD about creating SMTInterpol without SolverBuilder");
	}
	
	// Construct mapping for transitions of predecessor states leading into
	// block r.
	private HashMap<STATE, Term> constructMapping(final Block r) {
		// create HashMap with max size of number of states.
		final HashMap<STATE, Term> retMap = new HashMap<>(computeHashCap(mNumberOfStates));
		
		// Iterate over all containing states of block r.
		final Iterator<STATE> rIt = r.iterator();
		while (rIt.hasNext()) {
			final STATE st = rIt.next();
			// All letters over incoming transitions.
			final Set<LETTER> incomingLabels = mOperand.lettersInternalIncoming(st);
			// Iterating over all incoming transitions and build term.
			final Iterator<LETTER> incomingLabelsIt = incomingLabels.iterator();
			while (incomingLabelsIt.hasNext()) {
				final LETTER letter = incomingLabelsIt.next();
				assert hasIncomingTransitionWithLetter(st, letter);
				// Get all predecessors with transition into state
				// labled with letter.
				final Collection<STATE> predecessors = getPredecessor(st, letter);
				final Term atomLetter = mLetter2Formular.get(letter);
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
	
	private HashSet<Block> buildIntersectingBlocksSet(final Iterator<STATE> s) {
		final HashSet<Block> ret = new HashSet<>(mNumberOfStates);
		// Iterate over STATEs in s and lookup to which block they belong to.
		while (s.hasNext()) {
			final Block block = mPartition.get(s.next());
			// If ArrayList<Block> already contains block do not add twice.
			if (!ret.contains(block)) {
				ret.add(block);
			}
		}
		return ret;
	}
	
	private HashMap<Block, Block> buildIntersectingBlocksMap(final Iterator<STATE> s) {
		final HashMap<Block, Block> ret = new HashMap<>(computeHashCap(mNumberOfStates));
		// Lookup all Blocks to which the STATEs of s belong to and add to Map.
		while (s.hasNext()) {
			final STATE sState = s.next();
			final Block block = mPartition.get(sState);
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
	 *            state
	 * @param letter
	 *            letter
	 * @return if incoming transition labeled with letter exists.
	 */
	private boolean hasIncomingTransitionWithLetter(final STATE state, final LETTER letter) {
		return mOperand.internalPredecessors(state, letter).iterator().hasNext();
	}
	
	/**
	 * Returns state, which is predecessors of state with transition labeled
	 * with letter.
	 * 
	 * @param state
	 *            state
	 * @param letter
	 *            letter
	 * @return predecessor state.
	 */
	private LinkedList<STATE> getPredecessor(final STATE state, final LETTER letter) {
		final LinkedList<STATE> ret = new LinkedList<>();
		final Iterator<IncomingInternalTransition<LETTER, STATE>> it = mOperand.internalPredecessors(state, letter)
				.iterator();
		while (it.hasNext()) {
			ret.add(it.next().getPred());
		}
		return ret;
	}
	
	// Create a conjunction from a collection of formulas.
	private Term conjunct(final Term f1, final Term f2) {
		final Term[] conjuncts = new Term[2];
		conjuncts[0] = f1;
		conjuncts[1] = f2;
		return mSmtInterpol.term("and", conjuncts);
	}
	
	// Create a disjunction from a collection of formulas.
	private Term disjunct(final Term f1, final Term f2) {
		final Term[] disjuncts = new Term[2];
		disjuncts[0] = f1;
		disjuncts[1] = f2;
		return mSmtInterpol.term("or", disjuncts);
	}
	
	// Negate a given formula.
	private Term negate(final Term formula) {
		final Term[] negation = new Term[1];
		negation[0] = formula;
		return mSmtInterpol.term("not", negation);
	}
	
	private boolean isSatFormula(final Term formula) {
		mSmtInterpol.push(1);
		mSmtInterpol.assertTerm(formula);
		
		final LBool isSat = mSmtInterpol.checkSat();
		mSmtInterpol.pop(1);
		return isSat == LBool.SAT;
	}
	
	/***********************************************************************/
	/**
	 * Class for representing worklist.
	 * 
	 * @author bjoern
	 */
	public class Worklist {
		private final HashSet<Block> mSetsOfStates;
		
		// Constructor. Initialize an empty LinkedList<Block>.
		public Worklist(final int size) {
			mSetsOfStates = new HashSet<>(size);
		}
		
		// Pop first element of worklist.
		public Block pop() {
			if (mSetsOfStates.isEmpty()) {
				return null;
			}
			final Block toPop = mSetsOfStates.iterator().next();
			mSetsOfStates.remove(toPop);
			return toPop;
		}
		
		// Push element into worklist.
		public void push(final Block block) {
			mSetsOfStates.add(block);
		}
		
		// Remove given block from worklist.
		public boolean remove(final Block block) {
			return mSetsOfStates.remove(block);
		}
		
		// Returns if worklist contains given block or not.
		public boolean contains(final Block block) {
			return mSetsOfStates.contains(block);
		}
		
		// Return current size of Worklist.
		public int size() {
			return mSetsOfStates.size();
		}
		
		// Returns if Worklist is currently empty or not.
		public boolean isEmpty() {
			return mSetsOfStates.isEmpty();
		}
		
		@Override
		public String toString() {
			final StringBuilder b = new StringBuilder();
			b.append('(');
			final Iterator<Block> it = mSetsOfStates.iterator();
			while (it.hasNext()) {
				b.append(it.next().toString());
			}
			b.append(')');
			return b.toString();
		}
		
	}
	
	/***********************************************************************/
	/**
	 * Class for representing a block of states.
	 * 
	 * @author bjoern
	 */
	public class Block {
		private HashSet<STATE> mStates;
		
		// Constructor.
		public Block(final Collection<STATE> block) {
			// create new ArrayList<STATE> with allocated space.
			mStates = new HashSet<>(block.size());
			final Iterator<STATE> it = block.iterator();
			while (it.hasNext()) {
				mStates.add(it.next());
			}
		}
		
		// Copy constructor.
		public Block(final Block block) {
			this(block.returnStates());
		}
		
		// Default constructor. Just allocates space for HashSet<STATE>
		// mstates.
		public Block() {
			mStates = new HashSet<>(mNumberOfStates);
		}
		
		// Remove state <st> from block.
		public boolean remove(final STATE st) {
			return mStates.remove(st);
		}
		
		// Add state <st> to block.
		public void add(final STATE st) {
			mStates.add(st);
		}
		
		// Clear current block.
		public void clear() {
			mStates.clear();
		}
		
		// Returns iterator for Block - Object.
		public Iterator<STATE> iterator() {
			return mStates.iterator();
		}
		
		// Returns current size of block.
		public int size() {
			return mStates.size();
		}
		
		// Returns if block contains currently state <state> or not.
		public boolean contains(final STATE state) {
			return mStates.contains(state);
		}
		
		// Returns if block is currently empty or not.
		public boolean isEmpty() {
			return mStates.isEmpty();
		}
		
		public Set<STATE> returnStates() {
			return mStates;
		}
		
		@Override
		public String toString() {
			final StringBuilder b = new StringBuilder();
			b.append('(');
			final Iterator<STATE> it = mStates.iterator();
			while (it.hasNext()) {
				b.append('{');
				b.append(it.next().toString());
				b.append('}');
			}
			b.append(')');
			return b.toString();
		}
	}
	
	/***********************************************************************/
	/**
	 * Method for building the result automaton with reduced states and
	 * transitions.
	 */
	private void buildResult() {
		// Store new states in ArrayList with size = # blocks in partition.
		final HashMap<Block, STATE> blockToNewStates = new HashMap<>(computeHashCap(mPartition.size()));
		
		final Block blockWithinInitialState = mPartition.get(mInitialState);
		// Iterate over blocks in mpartition and build new state out of the
		// states belonging to one block. Therefor first get values of HashMap.
		final Collection<Block> blocksInPartition = mPartition.values();
		Iterator<Block> it = blocksInPartition.iterator();
		final HashSet<Block> alreadyLookedUp = new HashSet<>(blocksInPartition.size());
		startResultConstruction();
		while (it.hasNext()) {
			final Block blockOfPartition = it.next();
			if (alreadyLookedUp.contains(blockOfPartition)) {
				// State for this block was already created.
				continue;
			}
			alreadyLookedUp.add(blockOfPartition);
			// Get states of this block.
			final Collection<STATE> statesOfBlock = blockOfPartition.returnStates();
			// Build the new state by using the minimize-function of
			// StateFactory.
			final STATE newState = mStateFactory.merge(statesOfBlock);
			// Add new state to the new result automaton.
			final STATE firstOfBlock = blockOfPartition.iterator().next();
			blockToNewStates.put(blockOfPartition, newState);
			addState(blockOfPartition == blockWithinInitialState, mOperand.isFinal(firstOfBlock), newState);
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
			final Iterator<OutgoingInternalTransition<LETTER, STATE>> transitionIt = mOperand.internalSuccessors(
					firstOfBlock).iterator();
			// Iterate over all outgoing transitions of each block to create a
			// new transition add it to the new automaton.
			while (transitionIt.hasNext()) {
				// Get next outgoing transition.
				final OutgoingInternalTransition<LETTER, STATE> next = transitionIt.next();
				// Get the successor if the transition.
				final STATE succ = next.getSucc();
				// Get block in mpartition succ belongs to.
				final Block blockOfSucc = mPartition.get(succ);
				// Get new successor out of new states created above.
				final STATE newSucc = blockToNewStates.get(blockOfSucc);
				// Add the new transition to the result automaton.
				addInternalTransition(newPred, next.getLetter(), newSucc);
			}
		}
		finishResultConstruction(null, false);
	}
}
