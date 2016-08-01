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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;

/**
 * @author Björn Hagemeister
 */
public class MinimizeDfaHopcroft<LETTER, STATE>
		extends AMinimizeNwa<LETTER, STATE>
		implements IOperation<LETTER, STATE> {
	// Result automaton.
	private INestedWordAutomaton<LETTER, STATE> mResult;
	// ArrayList and HashMap for mapping STATE to int and vice versa.
	private ArrayList<STATE> mInt2state;
	private HashMap<STATE, Integer> mState2int;
	// ArrayList and HashMap for mapping LETTER to int and vice versa.
	private ArrayList<LETTER> mInt2letter;
	private HashMap<LETTER, Integer> mLetter2int;
	// Structure for transitions.
	private int[] mLabels;
	private int[] mLabelTails;
	private int[] mLabelHeads;
	private int mNumberOfTransitions;

	// Constructor.
	public MinimizeDfaHopcroft(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> operand) {
		super(services, operand.getStateFactory(), "minimizeDfaHopcroft", operand);
		minimizeDfaHopcroft();
		mLogger.info(exitMessage());
	}

	private void minimizeDfaHopcroft() {
		initializeData();

		// initialize partition.
		createInitialPartition();
	}

	/**
	 * Create and return initial partition for the given automaton.
	 * @return Initialized partition.
	 */
	private Partition createInitialPartition() {
		// create new partition.
		final Partition ret = new Partition();
		ret.init();

		return ret;
	}

	/**
	 * Get number of states and labels for calling initializeMappings and
	 * initializeLables.
	 */
	private void initializeData() {
		final int nOfStates = mOperand.getStates().size();
		final int nOfLables = mOperand.getInternalAlphabet().size();	
		initializeMappings(nOfStates, nOfLables);
		initializeLables();
	}
	
	/**
	 * Method for mapping STATE/LETTER to int and vice versa.
	 */
	private void initializeMappings(final int nOfStates, final int nOfLables) {
		// Allocate the finite space in ArrayList and HashMap.
		mInt2state = new ArrayList<STATE>(nOfStates);
		mState2int = new HashMap<STATE, Integer>(computeHashCap(nOfStates));
		mInt2letter = new ArrayList<LETTER>(nOfLables);
		mLetter2int = new HashMap<LETTER, Integer>(computeHashCap(nOfLables));

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
	 * Initialize structure for lables.
	 * Iterate over all states and get their OutgoingInternalTransistion<LETTER, STATE>
	 * for storing nOfLabel, headOfLabel and tailOfLabel.
	 */
	private void initializeLables() {
		mLabels = new int[Integer.MAX_VALUE];
		mLabelTails = new int[Integer.MAX_VALUE];
		mLabelHeads = new int[Integer.MAX_VALUE];
		
		// Iterate over all states in mint2state.
		int index = 0;
		for (int i = 0; i < mInt2state.size(); ++i) {
			final STATE st = mInt2state.get(i);
			// Get outgoing transition.
			final Iterator<OutgoingInternalTransition<LETTER, STATE>> it = 
					mOperand.internalSuccessors(st).iterator();
			// hasNext? --> add to labels.
			while (it.hasNext()) {
				final OutgoingInternalTransition< LETTER, STATE> oit = it.next();
				mLabels[index] = mLetter2int.get(oit.getLetter());
				mLabelTails[index] = mState2int.get(st);
				mLabelHeads[index] = mState2int.get(oit.getSucc());
				index++;
			}
		}
		mNumberOfTransitions = index;
		// resize arrays to used size for saving memory
		// Maybe too much computing time?
		mLabels = Arrays.copyOf(mLabels, mNumberOfTransitions);
		mLabelTails = Arrays.copyOf(mLabelTails, mNumberOfTransitions);
		mLabelHeads = Arrays.copyOf(mLabelHeads, mNumberOfTransitions);
	}
	
	/**
	 * Returns true, if there exists an incoming transition to <state> labeled
	 * with letter <letter>.
	 * @param state
	 * @param letter
	 * @return if incoming transition labeled with letter exists.
	 */
	private boolean hasIncomingTransitionWithLetter(final int state, final int letter) {
		final STATE st = mInt2state.get(state);
		final LETTER let = mInt2letter.get(letter);
		return mOperand.internalPredecessors(let, st).iterator().hasNext();
	}
	
	/**
	 * Returns true, if an outgoing transition from <state> labeled with
	 * <letter> exists.
	 * @param state
	 * @param letter
	 * @return if outgoing transition labeled with <letter> exists.
	 */
	private boolean hasOutgoingTransitionWithLetter(final int state, final int letter) {
		final STATE st = mInt2state.get(state);
		final LETTER let = mInt2letter.get(letter);
		return mOperand.internalSuccessors(st, let).iterator().hasNext();
	}
	
	/**
	 * Returns number of state, which is predecessor of <state> with transition
	 * labeled with <letter>.
	 * @param state
	 * @param letter
	 * @return Number of predecessor state.
	 */
	private int getPredecessor(final int state, final int letter) {
		final STATE st = mInt2state.get(state);
		final LETTER let = mInt2letter.get(letter);
		final STATE pred = mOperand.internalPredecessors(let, st).iterator().next().getPred();
		return mState2int.get(pred);
	}
	
	/**
	 * Returns number of state, which is successor of <state> with transition
	 * labeled with <letter>.
	 * @param state
	 * @param letter
	 * @return Number of successor state.
	 */
	private int getSuccessor(final int state, final int letter) {
		final STATE st = mInt2state.get(state);
		final LETTER let = mInt2letter.get(letter);
		final STATE succ = mOperand.internalSuccessors(st, let).iterator().next().getSucc();
		return mState2int.get(succ);
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
		private ArrayList<int[]> mSetsOfPartition;
		private int mSize;
		// All final states.
		private int[] mFinalStates;
		// All non - final states.
		private int[] mNonfinalStates;
		// WorkList of partition.
		private Worklist mWorkList;

		/**
		 * Constructor. Initialize arrays finalStates and nonfinalStates.
		 * 
		 * @param nOfStates
		 * @param nOfFinalStates
		 */
		public Partition() {
			mSize = 0;
		}

		/**
		 * Initialize Partition. Transfer collection of finalStates and states
		 * to int[] mfinalStates and int[] mnonfinalStates and create
		 * workList.
		 * 
		 * @param finalStates
		 * @param states
		 */
		public void init() {
			final Collection<STATE> finalStates = mOperand.getFinalStates();
			final Collection<STATE> states = mOperand.getStates();
			
			final int nOfFinalStates = finalStates.size();
			final int nOfStates = states.size();
			
			mFinalStates = new int[nOfFinalStates];
			mNonfinalStates = new int[nOfStates - nOfFinalStates];
			mSetsOfPartition = new ArrayList<int[]>(nOfStates);
			
			int fStatesInd = -1;
			int nfStatesInd = -1;
			final Iterator<STATE> it = states.iterator();
			while (it.hasNext()) {
				final STATE st = it.next();
				if (finalStates.contains(st)) {
					mFinalStates[++fStatesInd] = mState2int.get(st);
				} else {
					mNonfinalStates[++nfStatesInd] = mState2int.get(st);
				}
				mSize++;
			}
			mSetsOfPartition.add(mFinalStates);
			mSetsOfPartition.add(mNonfinalStates);
			// initialize workList with finalStates.
			mWorkList = new Worklist(states.size());
			mWorkList.addToWorklist(mFinalStates);
		}

		/**
		 * Size of partition = number of containing sets.
		 * 
		 * @return number of containing sets.
		 */
		public int size() {
			return mSize;
		}

		/**
		 * Replaces one set by another two sets.
		 */
		public void replaceSetBy2Sets(final int setToReplace, final int[] a, final int[] b) {
			mSetsOfPartition.remove(setToReplace);
			mSetsOfPartition.add(a);
			mSetsOfPartition.add(b);
			mSize++;
		}
	}

	/**
	 * Class for representing worklist.
	 * 
	 * @author bjoern
	 */
	public class Worklist {
		private final ArrayList<int[]> mSetsOfStates;
		private int mSize;

		/**
		 * Constructor. Initialize ArrayList<int[]> with maxSize = nOfStates.
		 */
		public Worklist(final int maxSize) {
			mSetsOfStates = new ArrayList<int[]>(maxSize);
			mSize = mSetsOfStates.size();
		}

		/**
		 * Pop last element of worklist.
		 */
		public int[] popFromWorklist() {
			if (mSetsOfStates.isEmpty()) {
				return null;
			}
			final int[] ret = mSetsOfStates.remove(mSize - 1);
			mSize--;
			return ret;
		}

		/**
		 * Add collection of states to worklist.
		 */
		public void addToWorklist(final int[] set) {
			mSetsOfStates.add(set);
			mSize++;
		}

		/**
		 * Replace specific Set by two other sets.
		 */
		public boolean replaceSetBy2Sets(final int setToReplace, final int[] a, final int[] b) {
			mSetsOfStates.remove(setToReplace);
			final boolean aAdded = mSetsOfStates.add(a);
			final boolean bAdded = mSetsOfStates.add(b);
			mSize++;
			return (aAdded && bAdded);
		}

		/**
		 * Returns true, if and only if worklist is empty.
		 */
		public boolean isEmpty() {
			return mSetsOfStates.isEmpty();
		}
	}

	@Override
	public INestedWordAutomatonSimple<LETTER, STATE> getResult() {
		return mResult;
	}
}
