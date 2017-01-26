/*
 * Copyright (C) 2015 Björn Hagemeister
 * Copyright (C) 2015 Layla Franke
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
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;

/**
 * Class for minimize deterministic finite automaton by the Hopcroft-Algorithm.
 * 
 * @author Layla Franke
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class MinimizeDfaHopcroftWiki<LETTER, STATE> extends AbstractMinimizeNwa<LETTER, STATE> {
	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	// ArrayList and HashMap for mapping STATE to int and vice versa.
	private ArrayList<STATE> mInt2state;
	private HashMap<STATE, Integer> mState2int;
	// ArrayList and HashMap for mapping LETTER to int and vice versa.
	private ArrayList<LETTER> mInt2letter;
	private HashMap<LETTER, Integer> mLetter2int;
	// Partition of sets of states.
	private final Partition mPartition;
	// Structure for transitions.
	private int[] mLabels;
	private int[] mLabelTails;
	private int[] mLabelHeads;
	private int mNumberOfTransitions;
	private ArrayList<int[]> mMapStatesToTransitionTails;
	// map states to their representatives - needed for constructing result.
	private int[] mState2representative;
	
	// Constructor.
	public MinimizeDfaHopcroftWiki(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> operand) {
		super(services, operand.getStateFactory());
		mOperand = operand;
		
		// Start minimization.
		printStartMessage();
		
		initializeData();
		mPartition = createInitialPartition();
		minimizeDfaHopcroft();
		constructResult();
		
		printExitMessage();
	}
	
	@Override
	protected INestedWordAutomaton<LETTER, STATE> getOperand() {
		return mOperand;
	}
	
	/**
	 * Create and return initial partition for the given automaton.
	 * 
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
		final int nOfStates = mOperand.size();
		final int nOfLables = mOperand.getInternalAlphabet().size();
		initializeMappings(nOfStates, nOfLables);
		initializeLables();
	}
	
	/**
	 * Method for mapping STATE/LETTER to int and vice versa.
	 */
	private void initializeMappings(final int numberOfStates, final int numberOfLables) {
		// Allocate the finite space in ArrayList and HashMap.
		mInt2state = new ArrayList<>(numberOfStates);
		mState2int = new HashMap<>(
				computeHashCap(numberOfStates));
		mInt2letter = new ArrayList<>(numberOfLables);
		mLetter2int = new HashMap<>(
				computeHashCap(numberOfLables));
		
		int index = -1;
		for (final STATE state : mOperand.getStates()) {
			mInt2state.add(state);
			mState2int.put(state, ++index);
		}
		index = -1;
		for (final LETTER letter : mOperand.getInternalAlphabet()) {
			mInt2letter.add(letter);
			mLetter2int.put(letter, ++index);
		}
	}
	
	// NOTE: Is this necessary - how could the algorithm even use it??
	/**
	 * Initialize structure for lables. Iterate over all states and get their
	 * OutgoingInternalTransition for storing nOfLabel,
	 * headOfLabel and tailOfLabel.
	 */
	private void initializeLables() {
		final int capacity = (int) Math.min(Integer.MAX_VALUE,
				(double) mOperand.size() * mOperand.size()
						* mOperand.getInternalAlphabet().size());
		mLabels = new int[capacity];
		mLabelTails = new int[capacity];
		mLabelHeads = new int[capacity];
		// Contains arrays of [state_int, firstIndex, numOfIndexes]
		mMapStatesToTransitionTails = new ArrayList<>();
		
		// Iterate over all states in mint2state.
		int index = 0;
		for (int i = 0; i < mInt2state.size(); ++i) {
			final STATE st = mInt2state.get(i);
			// Get outgoing transition.
			final Iterator<OutgoingInternalTransition<LETTER, STATE>> it = mOperand
					.internalSuccessors(st).iterator();
			// hasNext? --> add to labels.
			int count = 0;
			while (it.hasNext()) {
				final OutgoingInternalTransition<LETTER, STATE> oit = it.next();
				mLabels[index] = mLetter2int.get(oit.getLetter());
				mLabelTails[index] = mState2int.get(st);
				mLabelHeads[index] = mState2int.get(oit.getSucc());
				index++;
				count++;
			}
			final int[] map = new int[] { i, index - count, count };
			mMapStatesToTransitionTails.add(map);
		}
		mNumberOfTransitions = index;
		// resize arrays to used size for saving memory
		// Maybe too much computing time?
		mLabels = Arrays.copyOf(mLabels, mNumberOfTransitions);
		mLabelTails = Arrays.copyOf(mLabelTails, mNumberOfTransitions);
		mLabelHeads = Arrays.copyOf(mLabelHeads, mNumberOfTransitions);
	}
	
	private void minimizeDfaHopcroft() {
		final Worklist worklist = mPartition.getWorklist();
		while (!worklist.isEmpty()) {
			final int[] elem = worklist.popFromWorklist();
			for (final LETTER letter : mOperand.getInternalAlphabet()) {
				// This is far from optimal (hopefully): Find X, set of all
				// states for which a transition on letter leads to a state in
				// elem.
				final ArrayList<Integer> x = new ArrayList<>();
				final int letterInt = mLetter2int.get(letter);
				for (int i = 0; i < mNumberOfTransitions; i++) {
					if (mLabels[i] == letterInt) {
						for (final int stateInt : elem) {
							if (stateInt == mLabelHeads[i]) {
								x.add(mLabelTails[i]);
							}
						}
						// Doesn't work (always evaluates to false): &&
						// Arrays.asList(elem).contains(mlabelHeads[i]))
					}
				}
				// end initialization of X.
				for (int j = 0; j < mPartition.getPartitions().size(); j++) {
					final int[] set = mPartition.getPartitions().get(j);
					// set intersects X != emptyset and set \ X != emptyset
					// Iterate set. Increment counter if element in X is found,
					// and increment if element not in X is found.
					final ArrayList<Integer> intersection = new ArrayList<>();
					final ArrayList<Integer> complement = new ArrayList<>();
					for (int i = 0; i < set.length; i++) {
						if (x.contains(set[i])) {
							intersection.add(set[i]);
						} else {
							complement.add(set[i]);
						}
					}
					final int[] intersect = toIntArray(intersection);
					final int[] comp = toIntArray(complement);
					if (!intersection.isEmpty() && !complement.isEmpty()) {
						mPartition.replaceSetBy2Sets(j, intersect, comp);
						// set in W
						final int position = findSet(set, worklist);
						if (position >= 0) {
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
	 * @return Natural number (position of set in worklist) if worklist contains
	 *         set, -1 otherwise.
	 */
	private int findSet(final int[] set, final Worklist worklist) {
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
	 *            first array
	 * @param b
	 *            second array
	 * @return True if arrays contain the same numbers, false otherwise.
	 */
	private static boolean arrayEquals(final int[] a, final int[] b) {
		if (b.length != a.length) {
			return false;
		}
		for (final int numberA : a) {
			boolean found = false;
			for (final int numberB : b) {
				if (numberA == numberB) {
					found = true;
					break;
				}
			}
			if (!found) {
				return false;
			}
		}
		return true;
	}
	
	private static int[] toIntArray(final List<Integer> list) {
		final int[] ret = new int[list.size()];
		int i = 0;
		for (final Integer e : list) {
			ret[i++] = e.intValue();
		}
		return ret;
	}
	
	/**
	 * This method constructs the resulting automaton from the set of equivalent
	 * states.
	 */
	private void constructResult() {
		// mapping from states to their representative
		final HashMap<Integer, ? extends Collection<STATE>> state2equivStates = computeMapState2Equiv();
		
		// mapping from old state to new state
		final HashMap<Integer, STATE> oldState2newState = new HashMap<>(
				computeHashCap(state2equivStates.size()));
		
		// add states
		assert mOperand.getInitialStates().iterator().hasNext() : "There is no initial state in the automaton.";
		
		final int initRepresentative = mState2representative[mState2int
				.get(mOperand.getInitialStates().iterator().next())];
		startResultConstruction();
		for (final Entry<Integer, ? extends Collection<STATE>> entry : state2equivStates
				.entrySet()) {
			final int representative = entry.getKey();
			final Collection<STATE> equivStates = entry.getValue();
			final boolean isInitial = representative == initRepresentative;
			assert equivStates.iterator().hasNext() : "There is no equivalent state in the collection.";
			final boolean isFinal = mOperand.isFinal(equivStates.iterator().next());
			final STATE newSTate = addState(isInitial, isFinal, equivStates);
			oldState2newState.put(representative, newSTate);
		}
		
		/*
		 * add transitions
		 * 
		 * NOTE: This exploits the fact that the input is deterministic.
		 */
		for (final Integer oldStateInt : state2equivStates.keySet()) {
			for (final OutgoingInternalTransition<LETTER, STATE> out : mOperand
					.internalSuccessors(mInt2state.get(oldStateInt))) {
				addInternalTransition(
						oldState2newState.get(oldStateInt), out.getLetter(),
						oldState2newState
								.get(mState2representative[mState2int.get(out
										.getSucc())]));
			}
		}
		finishResultConstruction(null, false);
	}
	
	/**
	 * This method computes a mapping from old states to new representatives.
	 * 
	 * @return map old state -> new state
	 */
	private HashMap<Integer, ? extends Collection<STATE>> computeMapState2Equiv() {
		// Initialize mapping of states to their representatives.
		mState2representative = new int[mOperand.size()];
		final HashMap<Integer, LinkedList<STATE>> state2equivStates = new HashMap<>(
				computeHashCap(mOperand.size()));
		for (int i = 0; i < mPartition.getPartitions().size(); i++) {
			final int[] partitionI = mPartition.getPartitions().get(i);
			if (partitionI.length > 0) {
				final int representative = partitionI[0];
				final LinkedList<STATE> equivStates = new LinkedList<>();
				for (final int j : partitionI) {
					equivStates.add(mInt2state.get(j));
					mState2representative[j] = representative;
				}
				state2equivStates.put(representative, equivStates);
			}
		}
		return state2equivStates;
	}
	
	// ---------- Unused methods.---------- //
	/**
	 * Returns true if there exists an incoming transition to the state labeled
	 * with the letter.
	 * 
	 * @param state
	 *            state
	 * @param letter
	 *            letter
	 * @return if incoming transition labeled with letter exists.
	 */
	private boolean hasIncomingTransitionWithLetter(final int state, final int letter) {
		final STATE st = mInt2state.get(state);
		final LETTER let = mInt2letter.get(letter);
		return mOperand.internalPredecessors(st, let).iterator().hasNext();
	}
	
	/**
	 * Returns true, if an outgoing transition from the state labeled with
	 * the letter exists.
	 * 
	 * @param state
	 *            state
	 * @param letter
	 *            letter
	 * @return if outgoing transition labeled with the letter exists.
	 */
	private boolean hasOutgoingTransitionWithLetter(final int state, final int letter) {
		final STATE st = mInt2state.get(state);
		final LETTER let = mInt2letter.get(letter);
		return mOperand.internalSuccessors(st, let).iterator().hasNext();
	}
	
	// NOTE: There can be several such states in a DFA!!
	/**
	 * Returns number of state, which is predecessor of the state with transition
	 * labeled with the letter.
	 * 
	 * @param state
	 *            state
	 * @param letter
	 *            letter
	 * @return Number of predecessor state.
	 */
	private int getPredecessor(final int state, final int letter) {
		final STATE st = mInt2state.get(state);
		final LETTER let = mInt2letter.get(letter);
		final STATE pred = mOperand.internalPredecessors(st, let).iterator().next()
				.getPred();
		return mState2int.get(pred);
	}
	
	/**
	 * Returns number of state, which is successor of the state with transition
	 * labeled with the letter.
	 * 
	 * @param state
	 *            state
	 * @param letter
	 *            letter
	 * @return Number of successor state.
	 */
	private int getSuccessor(final int state, final int letter) {
		final STATE st = mInt2state.get(state);
		final LETTER let = mInt2letter.get(letter);
		final STATE succ = mOperand.internalSuccessors(st, let).iterator().next()
				.getSucc();
		return mState2int.get(succ);
	}
	
	// ---------------------------------------------------------------------------------------------//
	/**
	 * Class for representing a partition. A partition P contains blocks of
	 * states Y_1 ... Y_n. As initial blocks a partition P should contain P =
	 * {Y_1, Y_2} with Y_1 = {F} and Y_2 = {Q\F}.
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
		 */
		public Partition() {
			mSize = 0;
		}
		
		/**
		 * Initialize Partition. Transfer collection of finalStates and states
		 * to int[] mfinalStates and int[] mnonfinalStates and create
		 * workList.
		 */
		public void init() {
			final Collection<STATE> finalStates = mOperand.getFinalStates();
			final Collection<STATE> states = mOperand.getStates();
			
			final int nOfFinalStates = finalStates.size();
			final int nOfStates = states.size();
			
			mFinalStates = new int[nOfFinalStates];
			mNonfinalStates = new int[nOfStates - nOfFinalStates];
			mSetsOfPartition = new ArrayList<>(nOfStates);
			
			int finalStatesInd = -1;
			int nonfinalStatesInd = -1;
			final Iterator<STATE> it = states.iterator();
			while (it.hasNext()) {
				final STATE st = it.next();
				if (finalStates.contains(st)) {
					mFinalStates[++finalStatesInd] = mState2int.get(st);
				} else {
					mNonfinalStates[++nonfinalStatesInd] = mState2int.get(st);
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
		
		public ArrayList<int[]> getPartitions() {
			return mSetsOfPartition;
		}
		
		/**
		 * The algorithm needs to operate on the worklist of partition.
		 * 
		 * @return current worklist.
		 */
		public Worklist getWorklist() {
			return mWorkList;
		}
	}
	
	/**
	 * Class for representing worklist.
	 * 
	 * @author bjoern
	 */
	private static class Worklist {
		private final ArrayList<int[]> mSetsOfStates;
		private int mSize;
		
		/**
		 * Constructor. Initialize ArrayList with maxSize = nOfStates.
		 */
		public Worklist(final int maxSize) {
			mSetsOfStates = new ArrayList<>(maxSize);
			mSize = mSetsOfStates.size();
		}
		
		/**
		 * Pop last element of worklist.
		 */
		public int[] popFromWorklist() {
			assert !mSetsOfStates.isEmpty();
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
			return aAdded && bAdded;
		}
		
		/**
		 * Returns true, if and only if worklist is empty.
		 */
		public boolean isEmpty() {
			return mSetsOfStates.isEmpty();
		}
		
		/**
		 * Get number of arrays currently in the list.
		 */
		public int getSize() {
			return mSize;
		}
		
		public int[] get(final int i) {
			return mSetsOfStates.get(i);
		}
	}
}
