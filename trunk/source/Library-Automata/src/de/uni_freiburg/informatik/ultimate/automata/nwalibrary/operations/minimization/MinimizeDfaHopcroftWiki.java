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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.parallel.IMinimize;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

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
	// ILogger for debug - information.
	private final ILogger mLogger;
	// Service provider
	private final AutomataLibraryServices mservices;
	// Result automaton.
	private final INestedWordAutomaton<LETTER, STATE> mresult;
	// Input automaton.
	private final INestedWordAutomaton<LETTER, STATE> moperand;
	// ArrayList and HashMap for mapping STATE to int and vice versa.
	private ArrayList<STATE> mint2state;
	private HashMap<STATE, Integer> mstate2int;
	// ArrayList and HashMap for mapping LETTER to int and vice versa.
	private ArrayList<LETTER> mint2letter;
	private HashMap<LETTER, Integer> mletter2int;
	// Partition of sets of states.
	private final Partition mpartition;
	// Structure for transitions.
	private int[] mlabels;
	private int[] mlabelTails;
	private int[] mlabelHeads;
	private int mnOfTransitions;
	private ArrayList<int[]> mmapStatesToTransitionTails;
	private ArrayList<Integer>[] mmapStatesToTransitionHeads;
	// map states to their representatives - needed for constructing result.
	private int[] mstate2representative;

	// Constructor.
	public MinimizeDfaHopcroftWiki(AutomataLibraryServices services, INestedWordAutomaton<LETTER, STATE> operand) {
		this.mservices = services;
		this.mLogger = mservices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		this.moperand = operand;

		// Start minimization.
		System.out.println(startMessage());
		initializeData();
		// Initialize partition.
		mpartition = createInitialPartition();
		minimizeDfaHopcroft();
		mresult = constructResult();
		System.out.println(exitMessage());
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
		final int nOfStates = moperand.getStates().size();
		final int nOfLables = moperand.getInternalAlphabet().size();
		initializeMappings(nOfStates, nOfLables);
		initializeLables();
	}

	/**
	 * Method for mapping STATE/LETTER to int and vice versa.
	 */
	private void initializeMappings(int nOfStates, int nOfLables) {
		// Allocate the finite space in ArrayList and HashMap.
		mint2state = new ArrayList<STATE>(nOfStates);
		mstate2int = new HashMap<STATE, Integer>(
				computeHashMapCapacity(nOfStates));
		mint2letter = new ArrayList<LETTER>(nOfLables);
		mletter2int = new HashMap<LETTER, Integer>(
				computeHashMapCapacity(nOfLables));

		int index = -1;
		for (final STATE state : moperand.getStates()) {
			mint2state.add(state);
			mstate2int.put(state, ++index);
		}
		index = -1;
		for (final LETTER letter : moperand.getAlphabet()) {
			mint2letter.add(letter);
			mletter2int.put(letter, ++index);
		}
	}

	// NOTE: Is this necessary - how could the algorithm even use it??
	/**
	 * Initialize structure for lables. Iterate over all states and get their
	 * OutgoingInternalTransition<LETTER, STATE> for storing nOfLabel,
	 * headOfLabel and tailOfLabel.
	 */
	private void initializeLables() {
		final int capacity = (int) Math.min(Integer.MAX_VALUE,
				(double) moperand.size() * moperand.size()
						* moperand.getAlphabet().size());
		mlabels = new int[capacity];
		mlabelTails = new int[capacity];
		mlabelHeads = new int[capacity];
		// Contains arrays of [state_int, firstIndex, numOfIndexes]
		mmapStatesToTransitionTails = new ArrayList<int[]>();

		// Iterate over all states in mint2state.
		int index = 0;
		for (int i = 0; i < mint2state.size(); ++i) {
			final STATE st = mint2state.get(i);
			// Get outgoing transition.
			final Iterator<OutgoingInternalTransition<LETTER, STATE>> it = moperand
					.internalSuccessors(st).iterator();
			// hasNext? --> add to labels.
			int count = 0;
			while (it.hasNext()) {
				final OutgoingInternalTransition<LETTER, STATE> oit = it.next();
				mlabels[index] = mletter2int.get(oit.getLetter());
				mlabelTails[index] = mstate2int.get(st);
				mlabelHeads[index] = mstate2int.get(oit.getSucc());
				index++;
				count++;
			}
			final int[] map = new int[] { i, index - count, count };
			mmapStatesToTransitionTails.add(map);
		}
		mnOfTransitions = index;
		// resize arrays to used size for saving memory
		// Maybe too much computing time?
		mlabels = Arrays.copyOf(mlabels, mnOfTransitions);
		mlabelTails = Arrays.copyOf(mlabelTails, mnOfTransitions);
		mlabelHeads = Arrays.copyOf(mlabelHeads, mnOfTransitions);
	}

	private void minimizeDfaHopcroft() {
		final Worklist worklist = mpartition.getWorklist();
		while (!worklist.isEmpty()) {
			final int[] elem = worklist.popFromWorklist();
			for (final LETTER letter : moperand.getAlphabet()) {
				// This is far from optimal (hopefully): Find X, set of all
				// states for which a transition on letter leads to a state in
				// elem.
				final ArrayList<Integer> x = new ArrayList<Integer>();
				final int letterInt = mletter2int.get(letter);
				for (int i = 0; i < mnOfTransitions; i++) {
					if (mlabels[i] == letterInt) {
						for (final int stateInt : elem) {
							if (stateInt == mlabelHeads[i]) {
								x.add(mlabelTails[i]);
							}
						}
						// Doesn't work (always evaluates to false): &&
						// Arrays.asList(elem).contains(mlabelHeads[i]))
					}
				}
				// end initialization of X.
				for (int j = 0; j < mpartition.getPartitions().size(); j++) {
					final int[] set = mpartition.getPartitions().get(j);
					// set intersects X != emptyset and set \ X != emptyset
					// Iterate set. Increment counter if element in X is found,
					// and increment if element not in X is found.
					final ArrayList<Integer> intersection = new ArrayList<Integer>();
					final ArrayList<Integer> complement = new ArrayList<Integer>();
					for (int i = 0; i < set.length; i++) {
						if (x.contains(set[i])) {
							intersection.add(set[i]);
						} else {
							complement.add(set[i]);
						}
					}
					final int[] intersect = toIntArray(intersection);
					final int[] comp = toIntArray(complement);
					if (intersection.size() > 0 && complement.size() > 0) {
						mpartition.replaceSetBy2Sets(j, intersect, comp);
						// set in W
						final int position = findSet(set, worklist);
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
		for (final int number : b) {
			if (!Arrays.asList(a).contains(number)) {
				return false;
			}
		}
		return true;
	}

	private int[] toIntArray(List<Integer> list) {
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
	 * 
	 * @return resulting automaton where equivalent states are merged
	 */
	private INestedWordAutomaton<LETTER, STATE> constructResult() {
		// mapping from states to their representative
		final HashMap<Integer, ? extends Collection<STATE>> state2equivStates = computeMapState2Equiv();

		// construct result
		final StateFactory<STATE> stateFactory = moperand.getStateFactory();
		final NestedWordAutomaton<LETTER, STATE> result = new NestedWordAutomaton<LETTER, STATE>(mservices,
				moperand.getInternalAlphabet(), moperand.getCallAlphabet(),
				moperand.getReturnAlphabet(), stateFactory);

		// mapping from old state to new state
		final HashMap<Integer, STATE> oldState2newState = new HashMap<Integer, STATE>(
				computeHashCap(state2equivStates.size()));

		// add states
		assert (moperand.getInitialStates().iterator().hasNext()) : "There is no initial state in the automaton.";

		final int initRepresentative = mstate2representative[mstate2int
				.get(moperand.getInitialStates().iterator().next())];
		for (final Entry<Integer, ? extends Collection<STATE>> entry : state2equivStates
				.entrySet()) {
			final int representative = entry.getKey();
			final Collection<STATE> equivStates = entry.getValue();

			final STATE newSTate = stateFactory.minimize(equivStates);
			oldState2newState.put(representative, newSTate);

			assert (equivStates.iterator().hasNext()) : "There is no equivalent state in the collection.";
			result.addState((representative == initRepresentative),
					moperand.isFinal(equivStates.iterator().next()), newSTate);
		}

		/*
		 * add transitions
		 * 
		 * NOTE: This exploits the fact that the input is deterministic.
		 */
		for (final Integer oldStateInt : state2equivStates.keySet()) {
			for (final OutgoingInternalTransition<LETTER, STATE> out : moperand
					.internalSuccessors(mint2state.get(oldStateInt))) {
				result.addInternalTransition(
						oldState2newState.get(oldStateInt), out.getLetter(),
						oldState2newState
								.get(mstate2representative[mstate2int.get(out
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
		mstate2representative = new int[moperand.size()];
		final HashMap<Integer, LinkedList<STATE>> state2equivStates = new HashMap<Integer, LinkedList<STATE>>(
				computeHashCap(moperand.size()));
		for (int i = 0; i < mpartition.getPartitions().size(); i++) {
			if (mpartition.getPartitions().get(i).length > 0) {
				final int representative = mpartition.getPartitions().get(i)[0];
				final LinkedList<STATE> equivStates = new LinkedList<STATE>();
				for (final int j : mpartition.getPartitions().get(i)) {
					equivStates.add(mint2state.get(j));
					mstate2representative[j] = representative;
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
		final STATE st = mint2state.get(state);
		final LETTER let = mint2letter.get(letter);
		return moperand.internalPredecessors(let, st).iterator().hasNext();
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
		final STATE st = mint2state.get(state);
		final LETTER let = mint2letter.get(letter);
		return moperand.internalSuccessors(st, let).iterator().hasNext();
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
		final STATE st = mint2state.get(state);
		final LETTER let = mint2letter.get(letter);
		final STATE pred = moperand.internalPredecessors(let, st).iterator().next()
				.getPred();
		return mstate2int.get(pred);
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
		final STATE st = mint2state.get(state);
		final LETTER let = mint2letter.get(letter);
		final STATE succ = moperand.internalSuccessors(st, let).iterator().next()
				.getSucc();
		return mstate2int.get(succ);
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
		private ArrayList<int[]> msetsOfPartition;
		private int msize;
		// All final states.
		private int[] mfinalStates;
		// All non - final states.
		private int[] mnonfinalStates;
		// WorkList of partition.
		private Worklist mworkList;

		/**
		 * Constructor. Initialize arrays finalStates and nonfinalStates.
		 * 
		 * @param nOfStates
		 * @param nOfFinalStates
		 */
		public Partition() {
			msize = 0;
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
			final Collection<STATE> finalStates = moperand.getFinalStates();
			final Collection<STATE> states = moperand.getStates();

			final int nOfFinalStates = finalStates.size();
			final int nOfStates = states.size();

			mfinalStates = new int[nOfFinalStates];
			mnonfinalStates = new int[nOfStates - nOfFinalStates];
			msetsOfPartition = new ArrayList<int[]>(nOfStates);

			int fStatesInd = -1;
			int nfStatesInd = -1;
			final Iterator<STATE> it = states.iterator();
			while (it.hasNext()) {
				final STATE st = it.next();
				if (finalStates.contains(st)) {
					mfinalStates[++fStatesInd] = mstate2int.get(st);
				} else {
					mnonfinalStates[++nfStatesInd] = mstate2int.get(st);
				}
				msize++;
			}
			msetsOfPartition.add(mfinalStates);
			msetsOfPartition.add(mnonfinalStates);
			// initialize workList with finalStates.
			mworkList = new Worklist(states.size());
			mworkList.addToWorklist(mfinalStates);
		}

		/**
		 * Size of partition = number of containing sets.
		 * 
		 * @return number of containing sets.
		 */
		public int size() {
			return msize;
		}

		/**
		 * Replaces one set by another two sets.
		 */
		public void replaceSetBy2Sets(int setToReplace, int[] a, int[] b) {
			msetsOfPartition.remove(setToReplace);
			msetsOfPartition.add(a);
			msetsOfPartition.add(b);
			msize++;
		}

		public ArrayList<int[]> getPartitions() {
			return msetsOfPartition;
		}

		/**
		 * The algorithm needs to operate on the worklist of partition.
		 * 
		 * @return current worklist.
		 */
		public Worklist getWorklist() {
			return mworkList;
		}
	}

	/**
	 * Class for representing worklist.
	 * 
	 * @author bjoern
	 */
	public class Worklist {
		private final ArrayList<int[]> msetsOfStates;
		private int msize;

		/**
		 * Constructor. Initialize ArrayList<int[]> with maxSize = nOfStates.
		 */
		public Worklist(int maxSize) {
			msetsOfStates = new ArrayList<int[]>(maxSize);
			msize = msetsOfStates.size();
		}

		/**
		 * Pop last element of worklist.
		 */
		public int[] popFromWorklist() {
			if (msetsOfStates.isEmpty()) {
				return null;
			}
			final int[] ret = msetsOfStates.remove(msize - 1);
			msize--;
			return ret;
		}

		/**
		 * Add collection of states to worklist.
		 */
		public void addToWorklist(int[] set) {
			msetsOfStates.add(set);
			msize++;
		}

		/**
		 * Replace specific Set by two other sets.
		 */
		public boolean replaceSetBy2Sets(int setToReplace, int[] a, int[] b) {
			msetsOfStates.remove(setToReplace);
			final boolean a_added = msetsOfStates.add(a);
			final boolean b_added = msetsOfStates.add(b);
			msize++;
			return (a_added && b_added);
		}

		/**
		 * Returns true, if and only if worklist is empty.
		 */
		public boolean isEmpty() {
			return msetsOfStates.isEmpty();
		}

		/**
		 * Get number of arrays currently in the list.
		 * 
		 * @return
		 */
		public int getSize() {
			return msize;
		}

		public int[] get(int i) {
			return msetsOfStates.get(i);
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
		return mresult;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		// TODO Rewrite and test correctness.
		/*
		 * mLogger.info("Start testing correctness of " + operationName());
		 * boolean correct = true; correct &=
		 * (ResultChecker.nwaLanguageInclusion(moperand, mresult,
		 * stateFactory) == null); correct &=
		 * (ResultChecker.nwaLanguageInclusion(mresult, moperand,
		 * stateFactory) == null); if (!correct) {
		 * ResultChecker.writeToFileIfPreferred(operationName() + "Failed", "",
		 * moperand); } mLogger.info("Finished testing correctness of " +
		 * operationName());
		 */
		return true;
	}
}
