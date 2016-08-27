/*
 * Copyright (C) 2014-2015 Björn Hagemeister
 * Copyright (C) 2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * @author Björn Hagemeister
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class MinimizeDfaHopcroftArrays<LETTER, STATE>
		extends AbstractMinimizeNwaDd<LETTER, STATE>
		implements IOperation<LETTER, STATE> {
	// ArrayList and HashMap for mapping STATE to int and vice versa.
	private ArrayList<STATE> mInt2state;
	private HashMap<STATE, Integer> mState2int;
	// ArrayList and HashMap for mapping LETTER to int and vice versa.
	private ArrayList<LETTER> mInt2letter;
	private HashMap<LETTER, Integer> mLetter2int;
	
	/**
	 * necessary data elements for the minimization algorithm.
	 */
	// labels of transitions.
	private int[] mLabels;
	// tails of transitions.
	private int[] mLabelTails;
	// heads of transitions.
	private int[] mLabelHeads;
	// # of marked elements in set.
	private int[] mNumberOfMarkedElemInSet;
	// sets with marked elements in it.
	private int[] mSetsWithMarkedElements;
	private int[] mF;
	private int[] mAdjacent;
	private int[] mFinalStates;
	
	// number of transitions.
	private int mNumberOfTransitions;
	// number of states.
	private int mNumberOfStates;
	// number of final states.
	private int mNumberOfFinalStates;
	// initial state.
	private int mInitialState;
	// number of letters in alphabet.
	private int mNumberOfLetters;
	// index for msetsWithMarkedElements.
	private int mW = 0;
	// blocks (consist of states).
	private Partition mBlocks;
	// cords (consist of transitions).
	private Partition mCords;
	
	/**
	 * Constructor.
	 */
	public MinimizeDfaHopcroftArrays(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final IStateFactory<STATE> stateFactory,
			final boolean addMapping) {
		this(services, operand, stateFactory, null, addMapping);
	}
	
	public MinimizeDfaHopcroftArrays(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final IStateFactory<STATE> stateFactory,
			final Collection<Set<STATE>> initialPartition, final boolean addMapping) {
		super(services, stateFactory, "MinimizeDfaHopcroftPaper", operand);
		
		// added by Christian
		if (!isFiniteAutomaton()) {
			throw new UnsupportedOperationException(
					"This class only supports minimization of finite automata.");
		}
		
		if (mOperand.size() > 0) {
			// Start minimization.
			minimizeDfaHopcroft(initialPartition, addMapping);
		} else {
			// Special case: empty automaton.
			directResultConstruction(mOperand);
		}
		mLogger.info(exitMessage());
	}
	
	/**
	 * Constructor without state factory.
	 */
	public MinimizeDfaHopcroftArrays(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> operand) {
		this(services, operand, operand.getStateFactory(), false);
	}
	
	/**
	 * Step by Step implementation of minimizing finite automaton by Hopcroft.
	 */
	private void minimizeDfaHopcroft(final Collection<Set<STATE>> initialPartition,
			final boolean addMapping) {
		// First make preprocessing on given automata.
		mLogger.info("Start preprocessing data ... ");
		preprocessingData();
		// Create Object partition for mblocks and mcords.
		mBlocks = new Partition();
		mCords = new Partition();
		mLogger.info("completed preprocessing data.");
		
		mLogger.info("Start intitializing partitions ... ");
		mBlocks.init(mNumberOfStates);
		
		// Make initial partition.
		makeInitialPartition(initialPartition);
		
		// Make transition partition.
		makeTransitionPartition();
		mLogger.info("completed initialization of partitions.");
		
		mAdjacent = new int[mNumberOfTransitions];
		mF = new int[mNumberOfStates + 1];
		
		// Make adjacent.
		makeAdjacent(mLabelHeads);
		
		/***************************************************************//**
																			 * The core of the Hopcroft - algorithm.
																			 */
		mLogger.info("Start with Hopcroft - algorithm");
		int blockIterator = 1;
		int cordsIterator = 0;
		int i;
		int j;
		// Iterate over blocks of transitions with same labels.
		// --> pick each letter of alphabet (see Hopcroft algorithm).
		while (cordsIterator < mCords.mNumberOfSets) {
			// Iterate over transitions of each block.
			for (i = mCords.mFirst[cordsIterator]; i < mCords.mPast[cordsIterator]; ++i) {
				// Mark all states, which are tails of the transitions with
				// the same letter. --> Getting path to current state.
				mBlocks.mark(mLabelTails[mCords.mElements[i]]);
			}
			// Split all blocks with marked elements into blocks of marked
			// and non-marked states. --> new blocks are created.
			mBlocks.split();
			
			cordsIterator++;
			// Iterate over all blocks of states.
			while (blockIterator < mBlocks.mNumberOfSets) {
				// Iterate over all states of each block.
				for (i = mBlocks.mFirst[blockIterator]; i < mBlocks.mPast[blockIterator]; ++i) {
					// Get all outgoing transitions of each state and mark
					// them in the transition partition.
					for (j = mF[mBlocks.mElements[i]]; j < mF[mBlocks.mElements[i] + 1]; ++j) {
						mCords.mark(mAdjacent[j]);
					}
				}
				// Split all sets of marked transitions into sets of marked
				// and non-marked transitions.
				mCords.split();
				++blockIterator;
			}
		}
		/******************************************************************/
		// New automaton should be ready. Build result automaton.
		buildResult(addMapping);
	}
	
	/**
	 * Get number of states and labels for calling initializeMappings and
	 * initializeLables.
	 */
	private void preprocessingData() {
		mNumberOfFinalStates = mOperand.getFinalStates().size();
		mFinalStates = new int[mNumberOfFinalStates];
		mNumberOfStates = mOperand.size();
		mNumberOfLetters = mOperand.getInternalAlphabet().size();
		
		initializeMappings();
		initializeLables();
		
		mInitialState = mState2int.get(mOperand.getInitialStates().iterator().next());
		final Iterator<STATE> it = mOperand.getFinalStates().iterator();
		int index = -1;
		while (it.hasNext()) {
			mFinalStates[++index] = mState2int.get(it.next());
		}
		
	}
	
	/**
	 * Method for mapping STATE/LETTER to int and vice versa.
	 */
	private void initializeMappings() {
		// Allocate the finite space in ArrayList and HashMap.
		mInt2state = new ArrayList<STATE>(mNumberOfStates);
		mState2int = new HashMap<STATE, Integer>(
				computeHashCap(mNumberOfStates));
		mInt2letter = new ArrayList<LETTER>(mNumberOfLetters);
		mLetter2int = new HashMap<LETTER, Integer>(
				computeHashCap(mNumberOfLetters));
				
		int index = -1;
		for (final STATE state : mOperand.getStates()) {
			mInt2state.add(state);
			mState2int.put(state, ++index);
		}
		index = -1;
		for (final LETTER letter : mOperand.getAlphabet()) {
			mInt2letter.add(letter);
			mLetter2int.put(letter, ++index);
		}
	}
	
	/**
	 * Initialize structure for labels.
	 * Iterate over all states and get their OutgoingInternalTransistion
	 * for storing nOfLabel, headOfLabel and tailOfLabel.
	 */
	private void initializeLables() {
		// TODO: Better size handling.
		final ArrayList<Integer> labels = new ArrayList<Integer>();
		final ArrayList<Integer> heads = new ArrayList<Integer>();
		final ArrayList<Integer> tails = new ArrayList<Integer>();
		
		// Iterate over all states in mint2state.
		int index = 0;
		for (int i = 0; i < mInt2state.size(); ++i) {
			final STATE st = mInt2state.get(i);
			// Get outgoing transition.
			final Iterator<OutgoingInternalTransition<LETTER, STATE>> it =
					mOperand.internalSuccessors(st).iterator();
			// hasNext? --> add to labels.
			while (it.hasNext()) {
				final OutgoingInternalTransition<LETTER, STATE> oit = it.next();
				labels.add(mLetter2int.get(oit.getLetter()));
				tails.add(mState2int.get(st));
				heads.add(mState2int.get(oit.getSucc()));
				index++;
			}
		}
		mNumberOfTransitions = index;
		// resize arrays to used size for saving memory
		// Maybe too much computing time?
		mLabels = new int[mNumberOfTransitions];
		mLabelHeads = new int[mNumberOfTransitions];
		mLabelTails = new int[mNumberOfTransitions];
		
		for (int i = 0; i < mNumberOfTransitions; ++i) {
			mLabels[i] = labels.get(i);
			mLabelHeads[i] = heads.get(i);
			mLabelTails[i] = tails.get(i);
		}
	}
	
	/**
	 * Make initial partition mblocks. Therefor allocate memory for arrays
	 * and set number of final states as marked states.
	 */
	private void makeInitialPartition(final Collection<Set<STATE>> initialPartition) {
		mSetsWithMarkedElements = new int[mNumberOfTransitions + 1];
		mNumberOfMarkedElemInSet = new int[mNumberOfTransitions + 1];
		if (initialPartition == null || initialPartition.isEmpty()) {
			// no initial partition, only separate final states
			
			// Is there any finalState?
			if (mNumberOfFinalStates > 0) {
				// Before splitting mark final state for splitting final states
				// and non - final states.
				for (int i = 0; i < mFinalStates.length; ++i) {
					mBlocks.mark(mFinalStates[i]);
				}
				mBlocks.split();
			}
		} else {
			// consider an initial partition
			for (final Set<STATE> states : initialPartition) {
				for (final STATE state : states) {
					mBlocks.mark(mState2int.get(state));
				}
				mBlocks.split();
			}
		}
	}
	
	/**
	 * Create transition partition mcords.
	 */
	private void makeTransitionPartition() {
		mCords.init(mNumberOfTransitions);
		if (mNumberOfTransitions > 0) {
			final Integer[] test = new Integer[mCords.mElements.length];
			for (int i = 0; i < test.length; ++i) {
				test[i] = mCords.mElements[i];
			}
			Arrays.sort(test, new Comparator<Integer>() {
				
				@Override
				public int compare(final Integer x, final Integer y) {
					return Integer.compare(mLabels[x], mLabels[y]);
				}
			});
			
			for (int i = 0; i < test.length; ++i) {
				mCords.mElements[i] = test[i];
			}
			
			mCords.mNumberOfSets = mNumberOfMarkedElemInSet[0] = 0;
			int a = mLabels[mCords.mElements[0]];
			// Put transitions with same label into same block.
			// --> we get blocks of transitions with same label, which is
			// equivalent for sorting transitions after alphabet.
			// --> possible to iterate over alphabet (see Hopcroft algorithm).
			for (int i = 0; i < mNumberOfTransitions; ++i) {
				final int t = mCords.mElements[i];
				if (mLabels[t] != a) {
					a = mLabels[t];
					mCords.mPast[mCords.mNumberOfSets++] = i;
					mCords.mFirst[mCords.mNumberOfSets] = i;
					mNumberOfMarkedElemInSet[mCords.mNumberOfSets] = 0;
				}
				mCords.mSetElemBelongsTo[t] = mCords.mNumberOfSets;
				mCords.mLocationOfElem[t] = i;
			}
			mCords.mPast[mCords.mNumberOfSets++] = mNumberOfTransitions;
		}
	}
	
	/**
	 * Create adjacent transitions. Computes either the outgoing or incoming
	 * transitions of states.
	 * Using labelHeads[] as K[] --> computes incoming transitions.
	 * Using labelTails[] as K[] --> computes outgoing transitions.
	 * Adjacent transitions of state q are:
	 * madjacent[mF[q]], madjacent[mF[q] + 1], ... , madjacent[mF[q+1] - 1]
	 */
	private void makeAdjacent(final int[] arrayK) {
		int q;
		int t;
		for (q = 0; q <= mNumberOfStates; ++q) {
			mF[q] = 0;
		}
		for (t = 0; t < mNumberOfTransitions; ++t) {
			++mF[arrayK[t]];
		}
		for (q = 0; q < mNumberOfStates; ++q) {
			mF[q + 1] += mF[q];
		}
		for (t = mNumberOfTransitions - 1; t >= 0; t--) {
			mAdjacent[--mF[arrayK[t]]] = t;
		}
	}
	
	/**
	 * Implementation of partition data structure out of paper:
	 * "Fast brief practical DFA minimization".
	 */
	public class Partition {
		private int mNumberOfSets;
		private int[] mElements;
		private int[] mLocationOfElem;
		private int[] mSetElemBelongsTo;
		private int[] mFirst;
		private int[] mPast;
		
		/**
		 * Method for initializing partition.
		 * 
		 * @param numberOfStates
		 *            number of states
		 */
		public void init(final int numberOfStates) {
			// After initialization, partition contains either one
			// or none block of states.
			this.mNumberOfSets = (numberOfStates > 0 ? 1 : 0);
			// all states of the automaton.
			this.mElements = new int[numberOfStates];
			// location in mElements of a state
			this.mLocationOfElem = new int[numberOfStates];
			// # of block an element e belongs to
			this.mSetElemBelongsTo = new int[numberOfStates];
			
			// Elements e of block b are stored in an unspecified order in
			// E[f], E[f + 1], ... , E[p - 1] where f = F[b], p = P[b]
			
			// first element e of block.
			this.mFirst = new int[numberOfStates];
			// first element e of next block
			this.mPast = new int[numberOfStates];
			
			for (int i = 0; i < numberOfStates; ++i) {
				// After initialization elements are sorted.
				this.mElements[i] = this.mLocationOfElem[i] = i;
				// Each element belongs to block number 0.
				this.mSetElemBelongsTo[i] = 0;
			}
			
			if (this.mNumberOfSets == 1) {
				// first element of block 0 = 0.
				this.mFirst[0] = 0;
				// first element of not existing block 1 = nOfStates.
				this.mPast[0] = numberOfStates;
			}
			
			// Now we got an array mElements = [0, 1, 2, ... , #states - 1]
			// consisting of one block          |<-------- block 0 ------->|
			// every element e in mElements belongs to block 0.
		}
		
		/**
		 * Method for marking an element e.
		 * 
		 * @param element
		 *            element
		 */
		public void mark(final int element) {
			// # block, element e belongs to.
			final int set = mSetElemBelongsTo[element];
			// location of element e in mElements.
			final int location = mLocationOfElem[element];
			// first unmarked element of block, the element belongs to.
			final int firstUnmarked = mFirst[set] + mNumberOfMarkedElemInSet[set];
			
			// Switching element e with first unmarked element in melements.
			this.mElements[location] = this.mElements[firstUnmarked];
			this.mLocationOfElem[this.mElements[location]] = location;
			this.mElements[firstUnmarked] = element;
			this.mLocationOfElem[element] = firstUnmarked;
			
			// If no element was marked in this block before, add this block
			// to list of blocks with marked elements.
			if (mNumberOfMarkedElemInSet[set] == 0) {
				mSetsWithMarkedElements[mW++] = set;
			}
			// Increment marked elements in block, element e belongs to.
			mNumberOfMarkedElemInSet[set]++;
			
		}
		
		/**
		 * Method for splitting blocks with marked elements.
		 */
		public void split() {
			while (mW > 0) {
				// set with marked elements.
				final int set = mSetsWithMarkedElements[--mW];
				// first unmarked element of set.
				final int firstUnmarked = this.mFirst[set] + mNumberOfMarkedElemInSet[set];
				
				if (firstUnmarked == this.mPast[set]) {
					mNumberOfMarkedElemInSet[set] = 0;
					continue;
				}
				
				// Split block into two blocks with marked and non-marked
				// elements. Take the smaller one as new block and remain
				// the bigger one as the old block.
				if (mNumberOfMarkedElemInSet[set] <= (mPast[set] - firstUnmarked)) {
					// block with marked elements is smaller --> new block
					this.mFirst[this.mNumberOfSets] = this.mFirst[set];
					this.mPast[this.mNumberOfSets] = this.mFirst[set] = firstUnmarked;
				} else {
					// block with marked elements is bigger --> remain as old block.
					// --> new one consists of non-marked elements.
					
					// TODO: Index out of bounds, why?
					this.mPast[this.mNumberOfSets] = this.mPast[set];
					this.mFirst[this.mNumberOfSets] = this.mPast[set] = firstUnmarked;
				}
				
				// Adapt the number of new block, the elements belong to.
				for (int i = this.mFirst[this.mNumberOfSets]; i < this.mPast[this.mNumberOfSets]; ++i) {
					this.mSetElemBelongsTo[this.mElements[i]] = this.mNumberOfSets;
				}
				// Set changed block and new block as blocks with non-marked elements.
				mNumberOfMarkedElemInSet[set] = mNumberOfMarkedElemInSet[this.mNumberOfSets++] = 0;
			}
			
		}
	}
	
	/**
	 * Method for building the result automaton with reduced states
	 * and transitions.
	 */
	private void buildResult(final boolean addMapping) {
		final ArrayList<STATE> newStates =
				new ArrayList<STATE>(mBlocks.mNumberOfSets);
		final int blockOfInitState = mBlocks.mSetElemBelongsTo[mInitialState];
		final int[] blockOfFinalStates = new int[mNumberOfFinalStates];
		for (int i = 0; i < mNumberOfFinalStates; ++i) {
			blockOfFinalStates[i] = mBlocks.mSetElemBelongsTo[mFinalStates[i]];
		}
		
		final Map<STATE, STATE> mOldState2newState = addMapping
				? new HashMap<STATE, STATE>(computeHashCap(mOperand.size()))
				: null;
				
		startResultConstruction();
		// Iterate over number of blocks for getting every first element.
		for (int i = 0; i < mBlocks.mNumberOfSets; ++i) {
			// Get index in melements of the first element in block.
			final int firstOfBlockIndex = mBlocks.mFirst[i];
			// Get index in melements of the last element in block.
			final int lastOfBlockIndex = mBlocks.mPast[i];
			// For intersecting all STATEs belonging to one block,
			// build collection of all States.
			final Collection<STATE> tmp = new ArrayList<STATE>(
					lastOfBlockIndex - firstOfBlockIndex);
			// Iterate in melements over all States belonging to one block
			// and adding them to the collection created before.
			for (int j = firstOfBlockIndex; j < lastOfBlockIndex; ++j) {
				final int elem = mBlocks.mElements[j];
				tmp.add(mInt2state.get(elem));
			}
			// Build the new state by using the minimize - function of StateFactory.
			final STATE newState = mStateFactory.minimize(tmp);
			
			// update mapping 'old state -> new state'
			if (mOldState2newState != null) {
				for (final STATE oldState : tmp) {
					mOldState2newState.put(oldState, newState);
				}
			}
			
			newStates.add(newState);
			// Add the new state to the new result automaton.
			boolean isFinalState = false;
			for (int k = 0; k < blockOfFinalStates.length; ++k) {
				if (i == blockOfFinalStates[k]) {
					isFinalState = true;
				}
			}
			final boolean isInitialState = (i == blockOfInitState);
			addState(isInitialState, isFinalState, newState);
		}
		
		// Iterate over each block to get the outgoing transitions of every
		// first element of block.
		for (int i = 0; i < mBlocks.mNumberOfSets; ++i) {
			// Get the index in melements of the first element.
			final int firstOfBlockIndex = mBlocks.mFirst[i];
			// Get the belonging STATE - object out of Map.
			final STATE st = mInt2state.get(mBlocks.mElements[firstOfBlockIndex]);
			// Take the before created new State as predecessor
			// for the new transition.
			final STATE newPred = newStates.get(i);
			// Get the outgoing transitions of the STATE st.
			final Iterator<OutgoingInternalTransition<LETTER, STATE>> it =
					mOperand.internalSuccessors(st).iterator();
			// Iterate over outgoing transitions of each block and add the
			// transition to the new automaton.
			while (it.hasNext()) {
				// Get the next outgoing transition.
				final OutgoingInternalTransition<LETTER, STATE> next = it.next();
				// Get the successor of the transition.
				final int succ = mState2int.get(next.getSucc());
				// For finding the equivalent state in the new states,
				// get the number of the block the successor belongs to.
				final int blockOfSucc = mBlocks.mSetElemBelongsTo[succ];
				final STATE newSucc = newStates.get(blockOfSucc);
				// Add the new transition to the result automaton.
				addInternalTransition(newPred, next.getLetter(), newSucc);
			}
			finishResultConstruction(mOldState2newState, true);
		}
	}
}
