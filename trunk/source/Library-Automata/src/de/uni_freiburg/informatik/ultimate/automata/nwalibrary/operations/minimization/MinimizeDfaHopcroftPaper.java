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

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;

/**
 * @author Björn Hagemeister
 */
public class MinimizeDfaHopcroftPaper<LETTER, STATE> implements IOperation<LETTER, STATE> {
	private final IUltimateServiceProvider m_Services;
	// Logger for debug - information.
	private final Logger m_Logger;
	// Result automaton.
	private NestedWordAutomaton<LETTER, STATE> m_Result;
	// Input automaton.
	private INestedWordAutomaton<LETTER, STATE> m_operand;
	// state factory
	private StateFactory<STATE> m_stateFactory;
	// ArrayList and HashMap for mapping STATE to int and vice versa.
	private ArrayList<STATE> m_int2state;
	private HashMap<STATE, Integer> m_state2int;
	// ArrayList and HashMap for mapping LETTER to int and vice versa.
	private ArrayList<LETTER> m_int2letter;
	private HashMap<LETTER, Integer> m_letter2int;
	
	private HashMap<STATE, STATE> m_oldState2newState;
	
	/*******************************************************************//**
	 * necessary data elements for the minimization algorithm.
	 */
	private int[] 
			m_labels,			// labels of transitions.
			m_labelTails,		// tails of transitions.
			m_labelHeads,		// heads of transitions.
			m_nOfMarkedElemInSet,		// # of marked elements in set.
			m_setsWithMarkedElements,	// sets with marked elements in it.
			m_F,
			m_adjacent,
			m_finalStates;
	
	private int 
			m_nOfTransitions,	// number of transitions.
			m_nOfStates,		// number of states.
			m_nOfFinalStates,	// number of final states.
			m_initialState,     // initial state.
			m_nOfLetters,		// number of letters in alphabet.
			m_w = 0;			// index for m_setsWithMarkedElements.
	private Partition 
			m_blocks,			// blocks (consist of states).
			m_cords;			// cords (consist of transitions).
	/**********************************************************************/	

	/*******************************************************************//**
	 * Constructor.
	 */
	public MinimizeDfaHopcroftPaper(IUltimateServiceProvider services, 
			INestedWordAutomaton<LETTER, STATE> operand,
			StateFactory<STATE> stateFactoryConstruction,
			boolean addMapping) {
		this(services, operand, stateFactoryConstruction, null, addMapping);
	}
	
	public MinimizeDfaHopcroftPaper(IUltimateServiceProvider services, 
			INestedWordAutomaton<LETTER, STATE> operand,
			StateFactory<STATE> stateFactoryConstruction,
			Collection<Set<STATE>> initialPartition, boolean addMapping) {
		
		// added by Christian
		if ((operand.getCallAlphabet().size() > 0) ||
				(operand.getReturnAlphabet().size() > 0)) {
			throw new UnsupportedOperationException(
				"This class only supports minimization of finite automata.");
		}
		
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		this.m_operand = operand;
		this.m_stateFactory = stateFactoryConstruction;
		if (addMapping) {
			this.m_oldState2newState = null;
		} else {
			m_oldState2newState = new HashMap<STATE, STATE>(
					computeHashMapCapacity(m_operand.size()));
		}

		m_Logger.info(startMessage());
		if (m_operand.size() > 0) {
			// Start minimization.
			minimizeDfaHopcroft(initialPartition);
		} else {
			// Special case: empty automaton.
			m_Result = new NestedWordAutomaton<LETTER, STATE>(
					m_Services, 
					m_operand.getInternalAlphabet(), null,
					null, m_stateFactory);
		}
		m_Logger.info(exitMessage());
	}
	
	/**
	 * Constructor without state factory.
	 */
	public MinimizeDfaHopcroftPaper(IUltimateServiceProvider services, 
			INestedWordAutomaton<LETTER, STATE> operand) {
		this(services, operand, operand.getStateFactory(), false);
	}
	
	/*******************************************************************//**
	 * Step by Step implementation of minimizing finite automaton by Hopcroft.
	 * @param initialPartition 
	 */
	private void minimizeDfaHopcroft(final Collection<Set<STATE>> initialPartition) {
		// First make preprocessing on given automata.
		m_Logger.info("Start preprocessing data ... ");
		preprocessingData();
		// Create Object partition for m_blocks and m_cords.
		m_blocks = new Partition();
		m_cords = new Partition();
		m_Logger.info("completed preprocessing data.");
		
		m_Logger.info("Start intitializing partitions ... ");
		m_blocks.init(m_nOfStates);
		
		// Make initial partition.
		makeInitialPartition(initialPartition);
		
		// Make transition partition.
		makeTransitionPartition();
		m_Logger.info("completed initialization of partitions.");
		
		m_adjacent = new int[m_nOfTransitions];
		m_F = new int[m_nOfStates + 1];
		
		// Make adjacent.
		makeAdjacent(m_labelHeads);
		
		/***************************************************************//**
		 * The core of the Hopcroft - algorithm.
		 */
		m_Logger.info("Start with Hopcroft - algorithm");
		int blockIterator = 1, cordsIterator = 0;
		int i, j;
		// Iterate over blocks of transitions with same labels.
		// --> pick each letter of alphabet (see Hopcroft algorithm).
		while (cordsIterator < m_cords.m_nOfSets) {
			// Iterate over transitions of each block.
			for (i = m_cords.m_first[cordsIterator];
					i < m_cords.m_past[cordsIterator];
					++i) {
				// Mark all states, which are tails of the transitions with
				// the same letter. --> Getting path to current state.
				m_blocks.mark(m_labelTails[m_cords.m_Elements[i]]);
			}
			// Split all blocks with marked elements into blocks of marked
			// and non-marked states. --> new blocks are created.
			m_blocks.split();

			cordsIterator++;
			// Iterate over all blocks of states.
			while (blockIterator < m_blocks.m_nOfSets) {
				// Iterate over all states of each block.
				for (i = m_blocks.m_first[blockIterator];
						i < m_blocks.m_past[blockIterator];
						++i) {
					// Get all outgoing transitions of each state and mark
					// them in the transition partition.
					for (j = m_F[m_blocks.m_Elements[i]];
							j < m_F[m_blocks.m_Elements[i] + 1];
							++j) {
						m_cords.mark(m_adjacent[j]);
					}
				}
				// Split all sets of marked transitions into sets of marked
				// and non-marked transitions.
				m_cords.split();
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
		m_nOfFinalStates = m_operand.getFinalStates().size();
		m_finalStates = new int[m_nOfFinalStates];
		m_nOfStates = m_operand.getStates().size();
		m_nOfLetters = m_operand.getInternalAlphabet().size();			
		
		initializeMappings();
		initializeLables();
		
		m_initialState = m_state2int.get(m_operand.getInitialStates().iterator().next());
		Iterator<STATE> it = m_operand.getFinalStates().iterator();
		int index = -1;
		while (it.hasNext()) {
			m_finalStates[++index] = m_state2int.get(it.next());
		}

	}
	
	/*******************************************************************//**
	 * Method for mapping STATE/LETTER to int and vice versa.
	 */
	private void initializeMappings() {
		// Allocate the finite space in ArrayList and HashMap.
		m_int2state = new ArrayList<STATE>(m_nOfStates);
		m_state2int = new HashMap<STATE, Integer>(
				computeHashMapCapacity(m_nOfStates));
		m_int2letter = new ArrayList<LETTER>(m_nOfLetters);
		m_letter2int = new HashMap<LETTER, Integer>(
				computeHashMapCapacity(m_nOfLetters));

		int index = -1;
		for (final STATE state : m_operand.getStates()) {
			m_int2state.add(state);
			m_state2int.put(state, ++index);
		}
		index = -1;
		for (final LETTER letter : m_operand.getAlphabet()) {
			m_int2letter.add(letter);
			m_letter2int.put(letter, ++index);
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
		
		// Iterate over all states in m_int2state.
		int index = 0;
		for (int i = 0; i < m_int2state.size(); ++i) {
			STATE st = m_int2state.get(i);
			// Get outgoing transition.
			Iterator<OutgoingInternalTransition<LETTER, STATE>> it = 
					m_operand.internalSuccessors(st).iterator();
			// hasNext? --> add to labels.
			while (it.hasNext()) {
				OutgoingInternalTransition< LETTER, STATE> oit = it.next();
				labels.add(m_letter2int.get(oit.getLetter()));
				tails.add(m_state2int.get(st));
				heads.add(m_state2int.get(oit.getSucc()));
				index++;
			}
		}
		m_nOfTransitions = index;
		// resize arrays to used size for saving memory
		// Maybe too much computing time?
		m_labels = new int[m_nOfTransitions];
		m_labelHeads = new int[m_nOfTransitions];
		m_labelTails = new int[m_nOfTransitions];
		
		for (int i = 0; i < m_nOfTransitions; ++i) {
			m_labels[i] = labels.get(i);
			m_labelHeads[i] = heads.get(i);
			m_labelTails[i] = tails.get(i);
		}
	}

	/*******************************************************************//**
	 * Make initial partition m_blocks. Therefor allocate memory for arrays
	 * and set number of final states as marked states.
	 */
	private void makeInitialPartition(final Collection<Set<STATE>> initialPartition) {
		m_setsWithMarkedElements = new int[m_nOfTransitions + 1];
		m_nOfMarkedElemInSet = new int[m_nOfTransitions + 1];
		if (initialPartition == null || initialPartition.isEmpty()) {
			// no initial partition, only separate final states
			
			// Is there any finalState?
			if (m_nOfFinalStates > 0) {
				// Before splitting mark final state for splitting final states 
				// and non - final states.
				for (int i = 0; i < m_finalStates.length; ++i) {
					m_blocks.mark(m_finalStates[i]);
				}
				m_blocks.split();
			}
		} else {
			// consider an initial partition
			for (final Set<STATE> states : initialPartition) {
				for (final STATE state : states) {
					m_blocks.mark(m_state2int.get(state));
				}
				m_blocks.split();
			}
		}
	}
	
	/*******************************************************************//**
	 * Create transition partition m_cords.
	 */
	private void makeTransitionPartition() {
		m_cords.init(m_nOfTransitions);
		if (m_nOfTransitions > 0) {
			Integer[] test = new Integer[m_cords.m_Elements.length];
			for (int i = 0; i < test.length; ++i) {
				test[i] = m_cords.m_Elements[i];
			}
			Arrays.sort(test, new Comparator<Integer>() {
				
				@Override
				public int compare(Integer x, Integer y) {
					// TODO Auto-generated method stub
					return Integer.compare(m_labels[x], m_labels[y]);
				}
			});
			
			for (int i = 0; i < test.length; ++i) {
				m_cords.m_Elements[i] = test[i];
			}
			
			m_cords.m_nOfSets = m_nOfMarkedElemInSet[0] = 0;
			int a = m_labels[m_cords.m_Elements[0]];
			// Put transitions with same label into same block.
			// --> we get blocks of transitions with same label, which is
			// equivalent for sorting transitions after alphabet.
			// --> possible to iterate over alphabet (see Hopcroft algorithm).
			for (int i = 0; i < m_nOfTransitions; ++i) {
				int t = m_cords.m_Elements[i];
				if (m_labels[t] != a) {
					a = m_labels[t];
					m_cords.m_past[m_cords.m_nOfSets++] = i;
					m_cords.m_first[m_cords.m_nOfSets] = i;
					m_nOfMarkedElemInSet[m_cords.m_nOfSets] = 0;
				}
				m_cords.m_setElemBelongsTo[t] = m_cords.m_nOfSets;
				m_cords.m_LocationOfElem[t] = i;
			}
			m_cords.m_past[m_cords.m_nOfSets++] = m_nOfTransitions;
		}
	}
	
	/*******************************************************************//**
	 * Create adjacent transitions. Computes either the outgoing or incoming
	 * transitions of states.
	 * Using labelHeads[] as K[] --> computes incoming transitions.
	 * Using labelTails[] as K[] --> computes outgoing transitions.
	 * Adjacent transitions of state q are:
	 * m_adjacent[m_F[q]], m_adjacent[m_F[q] + 1], ... , m_adjacent[m_F[q+1] - 1]
	 * @param K
	 */
	private void makeAdjacent(int K[]) {
		int q, t;
		for (q = 0; q <= m_nOfStates; ++q) { m_F[q] = 0; }
		for (t = 0; t < m_nOfTransitions; ++t) { ++m_F[K[t]]; }
		for (q = 0; q < m_nOfStates; ++q) { m_F[q + 1] += m_F[q]; }
		for (t = m_nOfTransitions - 1; t >= 0; t--) {
			m_adjacent[--m_F[K[t]]] = t;
		}
	}
	
	/*******************************************************************//**
	 * Implementation of partition data structure out of paper:
	 * "Fast brief practical DFA minimization".
	 */
	public class Partition {
		private int m_nOfSets;
		private int[] m_Elements, m_LocationOfElem, m_setElemBelongsTo,
					m_first, m_past;
		/***************************************************************//**
		 * Method for initializing partition.
		 * @param nOfStates
		 */
		public void init(int nOfStates) {
			// After initialization, partition contains either one
			// or none block of states.
			this.m_nOfSets = (nOfStates > 0 ? 1 : 0);
			// all states of the automaton.
			this.m_Elements = new int[nOfStates];
			// location in m_Elements of a state
			this.m_LocationOfElem = new int[nOfStates];
			// # of block an element e belongs to
			this.m_setElemBelongsTo = new int[nOfStates];
			
			// Elements e of block b are stored in an unspecified order in
			// E[f], E[f + 1], ... , E[p - 1] where f = F[b], p = P[b]
			this.m_first = new int[nOfStates]; // first element e of block.
			this.m_past = new int[nOfStates];  // first element e of next block
			
			for (int i = 0; i < nOfStates; ++i) {
				// After initialization elements are sorted.
				this.m_Elements[i] = this.m_LocationOfElem[i] = i;
				// Each element belongs to block number 0.
				this.m_setElemBelongsTo[i] = 0;
			}
			
			if (this.m_nOfSets == 1) {
				this.m_first[0] = 0;			// first element of block 0 = 0.
				this.m_past[0] = nOfStates;	// first element of not existing block 1 = nOfStates.
			}
			
			// Now we got an array m_Elements = [0, 1, 2, ... , #states - 1]
			// consisting of one block          |<-------- block 0 ------->|
			// every element e in m_Elements belongs to block 0.
		}
		
		/***************************************************************//**
		 * Method for marking an element e.
		 * @param element
		 */
		public void mark(int element) {
			// # block, element e belongs to.
			int set = m_setElemBelongsTo[element];
			// location of element e in m_Elements.
			int location = m_LocationOfElem[element];
			// first unmarked element of block, the element belongs to.
			int firstUnmarked = m_first[set] + m_nOfMarkedElemInSet[set];
			
			// Switching element e with first unmarked element in m_elements.
			this.m_Elements[location] = this.m_Elements[firstUnmarked];
			this.m_LocationOfElem[this.m_Elements[location]] = location;
			this.m_Elements[firstUnmarked] = element;
			this.m_LocationOfElem[element] = firstUnmarked;
			
			// If no element was marked in this block before, add this block
			// to list of blocks with marked elements.
			if (m_nOfMarkedElemInSet[set] == 0) {
				m_setsWithMarkedElements[m_w++] = set;
			}
			// Increment marked elements in block, element e belongs to.
			m_nOfMarkedElemInSet[set]++;
			
		}
		
		/***************************************************************//**
		 * Method for splitting blocks with marked elements.
		 */
		public void split() {
			while (m_w > 0) {
				// set with marked elements.
				int set = m_setsWithMarkedElements[--m_w];
				// first unmarked element of set.
				int firstUnmarked = this.m_first[set] + m_nOfMarkedElemInSet[set];
				
				if (firstUnmarked == this.m_past[set]) {
					m_nOfMarkedElemInSet[set] = 0;
					continue;
				}
				
				// Split block into two blocks with marked and non-marked
				// elements. Take the smaller one as new block and remain
				// the bigger one as the old block.
				if (m_nOfMarkedElemInSet[set] <= (m_past[set] - firstUnmarked)) {
					// block with marked elements is smaller --> new block
					this.m_first[this.m_nOfSets] = this.m_first[set];
					this.m_past[this.m_nOfSets ] = this.m_first[set] = firstUnmarked;
				} else {
					// block with marked elements is bigger --> remain as old block.
					// --> new one consists of non-marked elements.
					this.m_past[this.m_nOfSets] = this.m_past[set];	// TODO: Index out of bounds, why?
					this.m_first[this.m_nOfSets] = this.m_past[set] = firstUnmarked;
				}
				
				// Adapt the number of new block, the elements belong to.
				for (int i = this.m_first[this.m_nOfSets]; i < this.m_past[this.m_nOfSets]; ++i) {
					this.m_setElemBelongsTo[this.m_Elements[i]] = this.m_nOfSets;
				}
				// Set changed block and new block as blocks with non-marked elements.
				m_nOfMarkedElemInSet[set] = m_nOfMarkedElemInSet[this.m_nOfSets++] = 0;
			}

		}
	}
	
	/*******************************************************************//**
	 * Method for building the result automaton with reduced states
	 * and transitions.
	 */
	private void buildResult() {
		m_Result = new NestedWordAutomaton<LETTER, STATE>(
				m_Services, 
				m_operand.getInternalAlphabet(), null,
				null, m_stateFactory);
		
		ArrayList<STATE> newStates =
				new ArrayList<STATE>(m_blocks.m_nOfSets);
		int blockOfInitState = m_blocks.m_setElemBelongsTo[m_initialState];
		int[] blockOfFinalStates = new int[m_nOfFinalStates];
		for (int i = 0; i < m_nOfFinalStates; ++i) {
			blockOfFinalStates[i] = m_blocks.m_setElemBelongsTo[m_finalStates[i]];
		}
		// Iterate over number of blocks for getting every first element.
		for (int i = 0; i < m_blocks.m_nOfSets; ++i) {
			// Get index in m_elements of the first element in block.
			int firstOfBlockIndex = m_blocks.m_first[i];
			// Get index in m_elements of the last element in block.
			int lastOfBlockIndex = m_blocks.m_past[i];
			// For intersecting all STATEs belonging to one block,
			// build collection of all States.
			Collection<STATE> tmp = new ArrayList<STATE>(
					lastOfBlockIndex - firstOfBlockIndex);
			// Iterate in m_elements over all States belonging to one block
			// and adding them to the collection created before.
			for (int j = firstOfBlockIndex; j < lastOfBlockIndex; ++j) {
				int elem = m_blocks.m_Elements[j];
				tmp.add(m_int2state.get(elem));
			}
			// Build the new state by using the minimize - function of StateFactory.
			STATE newState = m_stateFactory.minimize(tmp);
			
			// update mapping 'old state -> new state'
			if (m_oldState2newState != null) {
				for (final STATE oldState : tmp) {
					m_oldState2newState.put(oldState, newState);
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
			m_Result.addState(
					(i == blockOfInitState), // is initial state?
					isFinalState, // is final state?
					newState);
		}
		
		// Iterate over each block to get the outgoing transitions of every
		// first element of block.
		for (int i = 0; i < m_blocks.m_nOfSets; ++i) {
			// Get the index in m_elements of the first element.
			int firstOfBlockIndex = m_blocks.m_first[i];
			// Get the belonging STATE - object out of Map.
			STATE st = m_int2state.get(m_blocks.m_Elements[firstOfBlockIndex]);
			// Take the before created new State as predecessor
			// for the new transition.
			STATE newPred = newStates.get(i);
			// Get the outgoing transitions of the STATE st.
			Iterator<OutgoingInternalTransition<LETTER, STATE>> it = 
					m_operand.internalSuccessors(st).iterator();
			// Iterate over outgoing transitions of each block and add the
			// transition to the new automaton.
			while (it.hasNext()) {
				// Get the next outgoing transition.
				OutgoingInternalTransition<LETTER, STATE> next = it.next();
				// Get the successor of the transition.
				int succ = m_state2int.get(next.getSucc());
				// For finding the equivalent state in the new states,
				// get the number of the block the successor belongs to.
				int blockOfSucc = m_blocks.m_setElemBelongsTo[succ];
				STATE newSucc = newStates.get(blockOfSucc);
				// Add the new transition to the result automaton.
				m_Result.addInternalTransition(newPred, next.getLetter(), newSucc);
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
		return m_Result;
	}

	@SuppressWarnings("deprecation")
	@Override
	public final boolean checkResult(final StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		m_Logger.info("Start testing correctness of " + operationName());
		final String message;
		
		if (checkInclusion(m_operand, getResult(), stateFactory)) {
			if (checkInclusion(getResult(), m_operand, stateFactory)) {
				m_Logger.info("Finished testing correctness of " +
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
		
		ResultChecker.writeToFileIfPreferred(m_Services,
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
		return ResultChecker.nwaLanguageInclusion(m_Services,
				ResultChecker.getOldApiNwa(m_Services,subset),
				ResultChecker.getOldApiNwa(m_Services,superset),
				stateFactory) == null;
	}
	
	/**
	 * Returns a Map from states of the input automaton to states of the output
	 * automaton. The image of a state oldState is the representative of 
	 * oldStates equivalence class.
	 * This method can only be used if the minimization is finished.
	 */
	public Map<STATE,STATE> getOldState2newState() {
		return m_oldState2newState;
	}
}
