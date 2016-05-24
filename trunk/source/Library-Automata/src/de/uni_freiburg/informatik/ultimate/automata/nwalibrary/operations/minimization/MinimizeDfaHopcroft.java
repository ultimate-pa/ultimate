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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * @author Björn Hagemeister
 */
public class MinimizeDfaHopcroft<LETTER, STATE> implements
		IOperation<LETTER, STATE> {
	private final AutomataLibraryServices mServices;
	// ILogger for debug - information.
	private final ILogger mLogger;
	// Result automaton.
	private INestedWordAutomatonOldApi<LETTER, STATE> mResult;
	// Input automaton.
	private INestedWordAutomatonOldApi<LETTER, STATE> moperand;
	// ArrayList and HashMap for mapping STATE to int and vice versa.
	private ArrayList<STATE> mint2state;
	private HashMap<STATE, Integer> mstate2int;
	// ArrayList and HashMap for mapping LETTER to int and vice versa.
	private ArrayList<LETTER> mint2letter;
	private HashMap<LETTER, Integer> mletter2int;
	// Structure for transitions.
	private int[] mlabels;
	private int[] mlabelTails;
	private int[] mlabelHeads;
	private int mnOfTransitions;

	// Constructor.
	public MinimizeDfaHopcroft(AutomataLibraryServices services,
			INestedWordAutomatonOldApi<LETTER, STATE> operand) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		this.moperand = operand;

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
		int nOfStates = moperand.getStates().size();
		int nOfLables = moperand.getInternalAlphabet().size();	
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

	/**
	 * Initialize structure for lables.
	 * Iterate over all states and get their OutgoingInternalTransistion<LETTER, STATE>
	 * for storing nOfLabel, headOfLabel and tailOfLabel.
	 */
	private void initializeLables() {
		mlabels = new int[Integer.MAX_VALUE];
		mlabelTails = new int[Integer.MAX_VALUE];
		mlabelHeads = new int[Integer.MAX_VALUE];
		
		// Iterate over all states in mint2state.
		int index = 0;
		for (int i = 0; i < mint2state.size(); ++i) {
			STATE st = mint2state.get(i);
			// Get outgoing transition.
			Iterator<OutgoingInternalTransition<LETTER, STATE>> it = 
					moperand.internalSuccessors(st).iterator();
			// hasNext? --> add to labels.
			while (it.hasNext()) {
				OutgoingInternalTransition< LETTER, STATE> oit = it.next();
				mlabels[index] = mletter2int.get(oit.getLetter());
				mlabelTails[index] = mstate2int.get(st);
				mlabelHeads[index] = mstate2int.get(oit.getSucc());
				index++;
			}
		}
		mnOfTransitions = index;
		// resize arrays to used size for saving memory
		// Maybe too much computing time?
		mlabels = Arrays.copyOf(mlabels, mnOfTransitions);
		mlabelTails = Arrays.copyOf(mlabelTails, mnOfTransitions);
		mlabelHeads = Arrays.copyOf(mlabelHeads, mnOfTransitions);
	}
	
	/**
	 * Returns true, if there exists an incoming transition to <state> labeled
	 * with letter <letter>.
	 * @param state
	 * @param letter
	 * @return if incoming transition labeled with letter exists.
	 */
	private boolean hasIncomingTransitionWithLetter(int state, int letter) {
		STATE st = mint2state.get(state);
		LETTER let = mint2letter.get(letter);
		return moperand.internalPredecessors(let, st).iterator().hasNext();
	}
	
	/**
	 * Returns true, if an outgoing transition from <state> labeled with
	 * <letter> exists.
	 * @param state
	 * @param letter
	 * @return if outgoing transition labeled with <letter> exists.
	 */
	private boolean hasOutgoingTransitionWithLetter(int state, int letter) {
		STATE st = mint2state.get(state);
		LETTER let = mint2letter.get(letter);
		return moperand.internalSuccessors(st, let).iterator().hasNext();
	}
	
	/**
	 * Returns number of state, which is predecessor of <state> with transition
	 * labeled with <letter>.
	 * @param state
	 * @param letter
	 * @return Number of predecessor state.
	 */
	private int getPredecessor(int state, int letter) {
		STATE st = mint2state.get(state);
		LETTER let = mint2letter.get(letter);
		STATE pred = moperand.internalPredecessors(let, st).iterator().next().getPred();
		return mstate2int.get(pred);
	}
	
	/**
	 * Returns number of state, which is successor of <state> with transition
	 * labeled with <letter>.
	 * @param state
	 * @param letter
	 * @return Number of successor state.
	 */
	private int getSuccessor(int state, int letter) {
		STATE st = mint2state.get(state);
		LETTER let = mint2letter.get(letter);
		STATE succ = moperand.internalSuccessors(st, let).iterator().next().getSucc();
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
			Collection<STATE> finalStates = moperand.getFinalStates();
			Collection<STATE> states = moperand.getStates();
			
			int nOfFinalStates = finalStates.size();
			int nOfStates = states.size();
			
			mfinalStates = new int[nOfFinalStates];
			mnonfinalStates = new int[nOfStates - nOfFinalStates];
			msetsOfPartition = new ArrayList<int[]>(nOfStates);
			
			int fStatesInd = -1;
			int nfStatesInd = -1;
			Iterator<STATE> it = states.iterator();
			while (it.hasNext()) {
				STATE st = it.next();
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
	}

	/**
	 * Class for representing worklist.
	 * 
	 * @author bjoern
	 */
	public class Worklist {
		private ArrayList<int[]> msetsOfStates;
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
			if (msetsOfStates.isEmpty())
				return null;
			int[] ret = msetsOfStates.remove(msize - 1);
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
			boolean a_added = msetsOfStates.add(a);
			boolean b_added = msetsOfStates.add(b);
			msize++;
			return (a_added && b_added);
		}

		/**
		 * Returns true, if and only if worklist is empty.
		 */
		public boolean isEmpty() {
			return msetsOfStates.isEmpty();
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
	public Object getResult() throws AutomataLibraryException {
		return mResult;
	}

	@SuppressWarnings("deprecation")
	@Override
	public final boolean checkResult(final StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		mLogger.info("Start testing correctness of " + operationName());
		boolean correct = true;
		correct &= (ResultChecker.nwaLanguageInclusion(mServices, moperand, mResult, stateFactory) == null);
		correct &= (ResultChecker.nwaLanguageInclusion(mServices, mResult, moperand, stateFactory) == null);
		if (!correct) {
			ResultChecker.writeToFileIfPreferred(mServices, operationName() + "Failed", "", moperand);
		}
		mLogger.info("Finished testing correctness of " + operationName());
		return correct;
	}
}
