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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * @author Björn Hagemeister
 */
public class MinimizeDfaHopcroftPaper<LETTER, STATE> implements IOperation<LETTER, STATE> {
	private final AutomataLibraryServices mServices;
	// ILogger for debug - information.
	private final ILogger mLogger;
	// Result automaton.
	private NestedWordAutomaton<LETTER, STATE> mResult;
	// Input automaton.
	private INestedWordAutomaton<LETTER, STATE> moperand;
	// state factory
	private StateFactory<STATE> mstateFactory;
	// ArrayList and HashMap for mapping STATE to int and vice versa.
	private ArrayList<STATE> mint2state;
	private HashMap<STATE, Integer> mstate2int;
	// ArrayList and HashMap for mapping LETTER to int and vice versa.
	private ArrayList<LETTER> mint2letter;
	private HashMap<LETTER, Integer> mletter2int;
	
	private HashMap<STATE, STATE> moldState2newState;
	
	/*******************************************************************//**
	 * necessary data elements for the minimization algorithm.
	 */
	private int[] 
			mlabels,			// labels of transitions.
			mlabelTails,		// tails of transitions.
			mlabelHeads,		// heads of transitions.
			mnOfMarkedElemInSet,		// # of marked elements in set.
			msetsWithMarkedElements,	// sets with marked elements in it.
			mF,
			madjacent,
			mfinalStates;
	
	private int 
			mnOfTransitions,	// number of transitions.
			mnOfStates,		// number of states.
			mnOfFinalStates,	// number of final states.
			minitialState,     // initial state.
			mnOfLetters,		// number of letters in alphabet.
			mw = 0;			// index for msetsWithMarkedElements.
	private Partition 
			mblocks,			// blocks (consist of states).
			mcords;			// cords (consist of transitions).
	/**********************************************************************/	

	/*******************************************************************//**
	 * Constructor.
	 */
	public MinimizeDfaHopcroftPaper(AutomataLibraryServices services, 
			INestedWordAutomaton<LETTER, STATE> operand,
			StateFactory<STATE> stateFactoryConstruction,
			boolean addMapping) {
		this(services, operand, stateFactoryConstruction, null, addMapping);
	}
	
	public MinimizeDfaHopcroftPaper(AutomataLibraryServices services, 
			INestedWordAutomaton<LETTER, STATE> operand,
			StateFactory<STATE> stateFactoryConstruction,
			Collection<Set<STATE>> initialPartition, boolean addMapping) {
		
		// added by Christian
		if ((operand.getCallAlphabet().size() > 0) ||
				(operand.getReturnAlphabet().size() > 0)) {
			throw new UnsupportedOperationException(
				"This class only supports minimization of finite automata.");
		}
		
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		this.moperand = operand;
		this.mstateFactory = stateFactoryConstruction;
		if (addMapping) {
			this.moldState2newState = null;
		} else {
			moldState2newState = new HashMap<STATE, STATE>(
					computeHashMapCapacity(moperand.size()));
		}

		mLogger.info(startMessage());
		if (moperand.size() > 0) {
			// Start minimization.
			minimizeDfaHopcroft(initialPartition);
		} else {
			// Special case: empty automaton.
			mResult = new NestedWordAutomaton<LETTER, STATE>(
					mServices, 
					moperand.getInternalAlphabet(), null,
					null, mstateFactory);
		}
		mLogger.info(exitMessage());
	}
	
	/**
	 * Constructor without state factory.
	 */
	public MinimizeDfaHopcroftPaper(AutomataLibraryServices services, 
			INestedWordAutomaton<LETTER, STATE> operand) {
		this(services, operand, operand.getStateFactory(), false);
	}
	
	/*******************************************************************//**
	 * Step by Step implementation of minimizing finite automaton by Hopcroft.
	 * @param initialPartition 
	 */
	private void minimizeDfaHopcroft(final Collection<Set<STATE>> initialPartition) {
		// First make preprocessing on given automata.
		mLogger.info("Start preprocessing data ... ");
		preprocessingData();
		// Create Object partition for mblocks and mcords.
		mblocks = new Partition();
		mcords = new Partition();
		mLogger.info("completed preprocessing data.");
		
		mLogger.info("Start intitializing partitions ... ");
		mblocks.init(mnOfStates);
		
		// Make initial partition.
		makeInitialPartition(initialPartition);
		
		// Make transition partition.
		makeTransitionPartition();
		mLogger.info("completed initialization of partitions.");
		
		madjacent = new int[mnOfTransitions];
		mF = new int[mnOfStates + 1];
		
		// Make adjacent.
		makeAdjacent(mlabelHeads);
		
		/***************************************************************//**
		 * The core of the Hopcroft - algorithm.
		 */
		mLogger.info("Start with Hopcroft - algorithm");
		int blockIterator = 1, cordsIterator = 0;
		int i, j;
		// Iterate over blocks of transitions with same labels.
		// --> pick each letter of alphabet (see Hopcroft algorithm).
		while (cordsIterator < mcords.mnOfSets) {
			// Iterate over transitions of each block.
			for (i = mcords.mfirst[cordsIterator];
					i < mcords.mpast[cordsIterator];
					++i) {
				// Mark all states, which are tails of the transitions with
				// the same letter. --> Getting path to current state.
				mblocks.mark(mlabelTails[mcords.mElements[i]]);
			}
			// Split all blocks with marked elements into blocks of marked
			// and non-marked states. --> new blocks are created.
			mblocks.split();

			cordsIterator++;
			// Iterate over all blocks of states.
			while (blockIterator < mblocks.mnOfSets) {
				// Iterate over all states of each block.
				for (i = mblocks.mfirst[blockIterator];
						i < mblocks.mpast[blockIterator];
						++i) {
					// Get all outgoing transitions of each state and mark
					// them in the transition partition.
					for (j = mF[mblocks.mElements[i]];
							j < mF[mblocks.mElements[i] + 1];
							++j) {
						mcords.mark(madjacent[j]);
					}
				}
				// Split all sets of marked transitions into sets of marked
				// and non-marked transitions.
				mcords.split();
				++blockIterator;
			}
		}
		/******************************************************************/
		// New automaton should be ready. Build result automaton.
		buildResult();
	}

	/*******************************************************************//**
	 * Get number of states and labels for calling initializeMappings and
	 * initializeLables.
	 */
	private void preprocessingData() {
		mnOfFinalStates = moperand.getFinalStates().size();
		mfinalStates = new int[mnOfFinalStates];
		mnOfStates = moperand.getStates().size();
		mnOfLetters = moperand.getInternalAlphabet().size();			
		
		initializeMappings();
		initializeLables();
		
		minitialState = mstate2int.get(moperand.getInitialStates().iterator().next());
		Iterator<STATE> it = moperand.getFinalStates().iterator();
		int index = -1;
		while (it.hasNext()) {
			mfinalStates[++index] = mstate2int.get(it.next());
		}

	}
	
	/*******************************************************************//**
	 * Method for mapping STATE/LETTER to int and vice versa.
	 */
	private void initializeMappings() {
		// Allocate the finite space in ArrayList and HashMap.
		mint2state = new ArrayList<STATE>(mnOfStates);
		mstate2int = new HashMap<STATE, Integer>(
				computeHashMapCapacity(mnOfStates));
		mint2letter = new ArrayList<LETTER>(mnOfLetters);
		mletter2int = new HashMap<LETTER, Integer>(
				computeHashMapCapacity(mnOfLetters));

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

	/*******************************************************************//**
	 * Initialize structure for labels.
	 * Iterate over all states and get their OutgoingInternalTransistion<LETTER, STATE>
	 * for storing nOfLabel, headOfLabel and tailOfLabel.
	 */
	private void initializeLables() {
		// TODO: Better size handling.
		ArrayList<Integer> labels = new ArrayList<Integer>();
		ArrayList<Integer> heads = new ArrayList<Integer>();
		ArrayList<Integer> tails = new ArrayList<Integer>();
		
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
				labels.add(mletter2int.get(oit.getLetter()));
				tails.add(mstate2int.get(st));
				heads.add(mstate2int.get(oit.getSucc()));
				index++;
			}
		}
		mnOfTransitions = index;
		// resize arrays to used size for saving memory
		// Maybe too much computing time?
		mlabels = new int[mnOfTransitions];
		mlabelHeads = new int[mnOfTransitions];
		mlabelTails = new int[mnOfTransitions];
		
		for (int i = 0; i < mnOfTransitions; ++i) {
			mlabels[i] = labels.get(i);
			mlabelHeads[i] = heads.get(i);
			mlabelTails[i] = tails.get(i);
		}
	}

	/*******************************************************************//**
	 * Make initial partition mblocks. Therefor allocate memory for arrays
	 * and set number of final states as marked states.
	 */
	private void makeInitialPartition(final Collection<Set<STATE>> initialPartition) {
		msetsWithMarkedElements = new int[mnOfTransitions + 1];
		mnOfMarkedElemInSet = new int[mnOfTransitions + 1];
		if (initialPartition == null || initialPartition.isEmpty()) {
			// no initial partition, only separate final states
			
			// Is there any finalState?
			if (mnOfFinalStates > 0) {
				// Before splitting mark final state for splitting final states 
				// and non - final states.
				for (int i = 0; i < mfinalStates.length; ++i) {
					mblocks.mark(mfinalStates[i]);
				}
				mblocks.split();
			}
		} else {
			// consider an initial partition
			for (final Set<STATE> states : initialPartition) {
				for (final STATE state : states) {
					mblocks.mark(mstate2int.get(state));
				}
				mblocks.split();
			}
		}
	}
	
	/*******************************************************************//**
	 * Create transition partition mcords.
	 */
	private void makeTransitionPartition() {
		mcords.init(mnOfTransitions);
		if (mnOfTransitions > 0) {
			Integer[] test = new Integer[mcords.mElements.length];
			for (int i = 0; i < test.length; ++i) {
				test[i] = mcords.mElements[i];
			}
			Arrays.sort(test, new Comparator<Integer>() {
				
				@Override
				public int compare(Integer x, Integer y) {
					return Integer.compare(mlabels[x], mlabels[y]);
				}
			});
			
			for (int i = 0; i < test.length; ++i) {
				mcords.mElements[i] = test[i];
			}
			
			mcords.mnOfSets = mnOfMarkedElemInSet[0] = 0;
			int a = mlabels[mcords.mElements[0]];
			// Put transitions with same label into same block.
			// --> we get blocks of transitions with same label, which is
			// equivalent for sorting transitions after alphabet.
			// --> possible to iterate over alphabet (see Hopcroft algorithm).
			for (int i = 0; i < mnOfTransitions; ++i) {
				int t = mcords.mElements[i];
				if (mlabels[t] != a) {
					a = mlabels[t];
					mcords.mpast[mcords.mnOfSets++] = i;
					mcords.mfirst[mcords.mnOfSets] = i;
					mnOfMarkedElemInSet[mcords.mnOfSets] = 0;
				}
				mcords.msetElemBelongsTo[t] = mcords.mnOfSets;
				mcords.mLocationOfElem[t] = i;
			}
			mcords.mpast[mcords.mnOfSets++] = mnOfTransitions;
		}
	}
	
	/*******************************************************************//**
	 * Create adjacent transitions. Computes either the outgoing or incoming
	 * transitions of states.
	 * Using labelHeads[] as K[] --> computes incoming transitions.
	 * Using labelTails[] as K[] --> computes outgoing transitions.
	 * Adjacent transitions of state q are:
	 * madjacent[mF[q]], madjacent[mF[q] + 1], ... , madjacent[mF[q+1] - 1]
	 * @param K
	 */
	private void makeAdjacent(int K[]) {
		int q, t;
		for (q = 0; q <= mnOfStates; ++q) { mF[q] = 0; }
		for (t = 0; t < mnOfTransitions; ++t) { ++mF[K[t]]; }
		for (q = 0; q < mnOfStates; ++q) { mF[q + 1] += mF[q]; }
		for (t = mnOfTransitions - 1; t >= 0; t--) {
			madjacent[--mF[K[t]]] = t;
		}
	}
	
	/*******************************************************************//**
	 * Implementation of partition data structure out of paper:
	 * "Fast brief practical DFA minimization".
	 */
	public class Partition {
		private int mnOfSets;
		private int[] mElements, mLocationOfElem, msetElemBelongsTo,
					mfirst, mpast;
		/***************************************************************//**
		 * Method for initializing partition.
		 * @param nOfStates
		 */
		public void init(int nOfStates) {
			// After initialization, partition contains either one
			// or none block of states.
			this.mnOfSets = (nOfStates > 0 ? 1 : 0);
			// all states of the automaton.
			this.mElements = new int[nOfStates];
			// location in mElements of a state
			this.mLocationOfElem = new int[nOfStates];
			// # of block an element e belongs to
			this.msetElemBelongsTo = new int[nOfStates];
			
			// Elements e of block b are stored in an unspecified order in
			// E[f], E[f + 1], ... , E[p - 1] where f = F[b], p = P[b]
			this.mfirst = new int[nOfStates]; // first element e of block.
			this.mpast = new int[nOfStates];  // first element e of next block
			
			for (int i = 0; i < nOfStates; ++i) {
				// After initialization elements are sorted.
				this.mElements[i] = this.mLocationOfElem[i] = i;
				// Each element belongs to block number 0.
				this.msetElemBelongsTo[i] = 0;
			}
			
			if (this.mnOfSets == 1) {
				this.mfirst[0] = 0;			// first element of block 0 = 0.
				this.mpast[0] = nOfStates;	// first element of not existing block 1 = nOfStates.
			}
			
			// Now we got an array mElements = [0, 1, 2, ... , #states - 1]
			// consisting of one block          |<-------- block 0 ------->|
			// every element e in mElements belongs to block 0.
		}
		
		/***************************************************************//**
		 * Method for marking an element e.
		 * @param element
		 */
		public void mark(int element) {
			// # block, element e belongs to.
			int set = msetElemBelongsTo[element];
			// location of element e in mElements.
			int location = mLocationOfElem[element];
			// first unmarked element of block, the element belongs to.
			int firstUnmarked = mfirst[set] + mnOfMarkedElemInSet[set];
			
			// Switching element e with first unmarked element in melements.
			this.mElements[location] = this.mElements[firstUnmarked];
			this.mLocationOfElem[this.mElements[location]] = location;
			this.mElements[firstUnmarked] = element;
			this.mLocationOfElem[element] = firstUnmarked;
			
			// If no element was marked in this block before, add this block
			// to list of blocks with marked elements.
			if (mnOfMarkedElemInSet[set] == 0) {
				msetsWithMarkedElements[mw++] = set;
			}
			// Increment marked elements in block, element e belongs to.
			mnOfMarkedElemInSet[set]++;
			
		}
		
		/***************************************************************//**
		 * Method for splitting blocks with marked elements.
		 */
		public void split() {
			while (mw > 0) {
				// set with marked elements.
				int set = msetsWithMarkedElements[--mw];
				// first unmarked element of set.
				int firstUnmarked = this.mfirst[set] + mnOfMarkedElemInSet[set];
				
				if (firstUnmarked == this.mpast[set]) {
					mnOfMarkedElemInSet[set] = 0;
					continue;
				}
				
				// Split block into two blocks with marked and non-marked
				// elements. Take the smaller one as new block and remain
				// the bigger one as the old block.
				if (mnOfMarkedElemInSet[set] <= (mpast[set] - firstUnmarked)) {
					// block with marked elements is smaller --> new block
					this.mfirst[this.mnOfSets] = this.mfirst[set];
					this.mpast[this.mnOfSets ] = this.mfirst[set] = firstUnmarked;
				} else {
					// block with marked elements is bigger --> remain as old block.
					// --> new one consists of non-marked elements.
					this.mpast[this.mnOfSets] = this.mpast[set];	// TODO: Index out of bounds, why?
					this.mfirst[this.mnOfSets] = this.mpast[set] = firstUnmarked;
				}
				
				// Adapt the number of new block, the elements belong to.
				for (int i = this.mfirst[this.mnOfSets]; i < this.mpast[this.mnOfSets]; ++i) {
					this.msetElemBelongsTo[this.mElements[i]] = this.mnOfSets;
				}
				// Set changed block and new block as blocks with non-marked elements.
				mnOfMarkedElemInSet[set] = mnOfMarkedElemInSet[this.mnOfSets++] = 0;
			}

		}
	}
	
	/*******************************************************************//**
	 * Method for building the result automaton with reduced states
	 * and transitions.
	 */
	private void buildResult() {
		mResult = new NestedWordAutomaton<LETTER, STATE>(
				mServices, 
				moperand.getInternalAlphabet(), null,
				null, mstateFactory);
		
		ArrayList<STATE> newStates =
				new ArrayList<STATE>(mblocks.mnOfSets);
		int blockOfInitState = mblocks.msetElemBelongsTo[minitialState];
		int[] blockOfFinalStates = new int[mnOfFinalStates];
		for (int i = 0; i < mnOfFinalStates; ++i) {
			blockOfFinalStates[i] = mblocks.msetElemBelongsTo[mfinalStates[i]];
		}
		// Iterate over number of blocks for getting every first element.
		for (int i = 0; i < mblocks.mnOfSets; ++i) {
			// Get index in melements of the first element in block.
			int firstOfBlockIndex = mblocks.mfirst[i];
			// Get index in melements of the last element in block.
			int lastOfBlockIndex = mblocks.mpast[i];
			// For intersecting all STATEs belonging to one block,
			// build collection of all States.
			Collection<STATE> tmp = new ArrayList<STATE>(
					lastOfBlockIndex - firstOfBlockIndex);
			// Iterate in melements over all States belonging to one block
			// and adding them to the collection created before.
			for (int j = firstOfBlockIndex; j < lastOfBlockIndex; ++j) {
				int elem = mblocks.mElements[j];
				tmp.add(mint2state.get(elem));
			}
			// Build the new state by using the minimize - function of StateFactory.
			STATE newState = mstateFactory.minimize(tmp);
			
			// update mapping 'old state -> new state'
			if (moldState2newState != null) {
				for (final STATE oldState : tmp) {
					moldState2newState.put(oldState, newState);
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
			mResult.addState(
					(i == blockOfInitState), // is initial state?
					isFinalState, // is final state?
					newState);
		}
		
		// Iterate over each block to get the outgoing transitions of every
		// first element of block.
		for (int i = 0; i < mblocks.mnOfSets; ++i) {
			// Get the index in melements of the first element.
			int firstOfBlockIndex = mblocks.mfirst[i];
			// Get the belonging STATE - object out of Map.
			STATE st = mint2state.get(mblocks.mElements[firstOfBlockIndex]);
			// Take the before created new State as predecessor
			// for the new transition.
			STATE newPred = newStates.get(i);
			// Get the outgoing transitions of the STATE st.
			Iterator<OutgoingInternalTransition<LETTER, STATE>> it = 
					moperand.internalSuccessors(st).iterator();
			// Iterate over outgoing transitions of each block and add the
			// transition to the new automaton.
			while (it.hasNext()) {
				// Get the next outgoing transition.
				OutgoingInternalTransition<LETTER, STATE> next = it.next();
				// Get the successor of the transition.
				int succ = mstate2int.get(next.getSucc());
				// For finding the equivalent state in the new states,
				// get the number of the block the successor belongs to.
				int blockOfSucc = mblocks.msetElemBelongsTo[succ];
				STATE newSucc = newStates.get(blockOfSucc);
				// Add the new transition to the result automaton.
				mResult.addInternalTransition(newPred, next.getLetter(), newSucc);
			}
		}	
	}
	
	/*******************************************************************//**
	 * computes the size of a hash Map to avoid rehashing this is only 
	 * sensible if the maximum size is already known Java standard sets
	 * the load factor to 0.75.
	 * 
	 * @param size
	 * @return hash map size
	 */
	private int computeHashMapCapacity(int size) {
		return (int) (size / 0.75 + 1);
	}
	
	@Override
	public String operationName() {
		return "minimizeDfaHopcroft";
	}

	@Override
	public String startMessage() {
		return "Starting MinimizeDfaHopcroftPaper";
	}

	@Override
	public String exitMessage() {
		return "Finished MinimizeDfaHopcroftPaper";
	}

	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult()
			throws AutomataLibraryException {
		return mResult;
	}

	@SuppressWarnings("deprecation")
	@Override
	public final boolean checkResult(final StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		mLogger.info("Start testing correctness of " + operationName());
		final String message;
		
		if (checkInclusion(moperand, getResult(), stateFactory)) {
			if (checkInclusion(getResult(), moperand, stateFactory)) {
				mLogger.info("Finished testing correctness of " +
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
		
		ResultChecker.writeToFileIfPreferred(mServices,
				operationName() + " failed",
				message,
				moperand);
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
		return ResultChecker.nwaLanguageInclusion(mServices,
				ResultChecker.getOldApiNwa(mServices,subset),
				ResultChecker.getOldApiNwa(mServices,superset),
				stateFactory) == null;
	}
	
	/**
	 * Returns a Map from states of the input automaton to states of the output
	 * automaton. The image of a state oldState is the representative of 
	 * oldStates equivalence class.
	 * This method can only be used if the minimization is finished.
	 */
	public Map<STATE,STATE> getOldState2newState() {
		return moldState2newState;
	}
}
