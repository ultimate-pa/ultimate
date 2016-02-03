/*
 * Copyright (C) 2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Daniel Tischner
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
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;

/**
 * Utility class for minimizing incomplete DFAs (Deterministic Finite
 * Automaton). Uses a modification of the Hopcroft algorithm.<br/>
 * Runtime is in:<br/>
 * <b>O(m * log(n))</b> with usage of<br/>
 * <b>O(k + n + m)</b> space<br/>
 * where 'n' is the number of states, 'm' the number of edges and 'k' the size
 * of the alphabet.
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 *            Class of the letters from the automata
 * @param <STATE>
 *            Class of the states from the automata
 */
public final class MinimizeIncompleteDfa<LETTER, STATE> extends
		AMinimizeNwa<LETTER, STATE> implements IOperation<LETTER, STATE> {
	/**
	 * Initial amount of blocks.
	 */
	private static final int INITIAL_BLOCK_AMOUNT = 2;
	/**
	 * Next usable unique id for a block.
	 */
	private int blockId = 0;
	/**
	 * List of all blocks the automata currently has. (Also known as "Q").
	 */
	private final LinkedList<LinkedHashSet<Integer>> blocks =
			new LinkedList<LinkedHashSet<Integer>>();
	/**
	 * Mapping for block to a unique id.
	 */
	private final HashMap<LinkedHashSet<Integer>, Integer> blockToId;
	/**
	 * Mapping for a unique id to block.
	 */
	private final HashMap<Integer, LinkedHashSet<Integer>> idToBlock;
	/**
	 * Mapping for a unique id to state.
	 */
	private final HashMap<Integer, STATE> idToState;
	/**
	 * Mapping for a letter to unique id.
	 */
	private final HashMap<LETTER, Integer> letterToId;
	/**
	 * Input automaton that should be minimized.
	 */
	private final INestedWordAutomaton<LETTER, STATE> m_operand;
	/**
	 * Resulting minimized automaton.
	 */
	private final NestedWordAutomaton<LETTER, STATE> m_result;
	/**
	 * Service provider.
	 */
	private final AutomataLibraryServices m_services;
	/**
	 * Mapping for state to the block number where it is contained.
	 */
	private final HashMap<Integer, Integer> stateToBlockId;
	/**
	 * Mapping for a state to unique id.
	 */
	private final HashMap<STATE, Integer> stateToId;
	/**
	 * Mapping for state to incoming edges.
	 */
	private final HashMap<Integer, Iterable<
		IncomingInternalTransition<LETTER, STATE>>> stateToIncomingEdges;
//	/**
//	 * Mapping for state to outgoing edges.
//	 * Christian: not used anymore
//	 */
//	private final HashMap<Integer, Iterable<
//		OutgoingInternalTransition<LETTER, STATE>>> stateToOutgoingEdges;
	
	// added by Christian
	private final StateFactory<STATE> m_stateFactory;
	private HashMap<STATE, STATE> m_oldState2newState;
	
	/**
	 * Minimizes a given incomplete DFAs (Deterministic Finite Automaton).<br/>
	 * Runtime is in:<br/>
	 * <b>O(m * log(n))</b> with usage of<br/>
	 * <b>O(k + n + m)</b> space<br/>
	 * where 'n' is the number of states, 'm' the number of edges and 'k' the
	 * size of the alphabet.
	 */
	public MinimizeIncompleteDfa(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final StateFactory<STATE> stateFactoryConstruction,
			final Collection<Set<STATE>> initialPartition,
			final boolean addMapping) {
		super(services, operand.getStateFactory(), "minimizeIncompleteDFA",
				operand);
		
		// added by Christian
		if ((operand.getCallAlphabet().size() > 0) ||
				(operand.getReturnAlphabet().size() > 0)) {
			throw new UnsupportedOperationException(
				"This class only supports minimization of finite automata.");
		}
		m_stateFactory = stateFactoryConstruction;
		if (addMapping) {
			this.m_oldState2newState = null;
		} else {
			m_oldState2newState = new HashMap<STATE, STATE>();
		}
		
		m_services = services;
		m_operand = operand;
		blockToId = new HashMap<LinkedHashSet<Integer>, Integer>(
				INITIAL_BLOCK_AMOUNT);
		idToBlock = new HashMap<Integer, LinkedHashSet<Integer>>(
				INITIAL_BLOCK_AMOUNT);
		int stateAmount = operand.getStates().size();
		idToState = new HashMap<Integer, STATE>(stateAmount);
		stateToId = new HashMap<STATE, Integer>(stateAmount);
		stateToBlockId = new HashMap<Integer, Integer>(stateAmount);
		stateToIncomingEdges =
				new HashMap<Integer,
				Iterable<IncomingInternalTransition<LETTER, STATE>>>(
				stateAmount);
		// Christian: not used anymore
//		stateToOutgoingEdges = new HashMap<Integer,
//				Iterable<OutgoingInternalTransition<LETTER, STATE>>>(
//				stateAmount);
		int letterAmount = operand.getInternalAlphabet().size();
		letterToId = new HashMap<LETTER, Integer>(letterAmount);

		init(stateAmount, letterAmount);
		
		m_result = minimizeICDFA(m_operand, initialPartition);
		Logger logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		logger.info(exitMessage());
	}

	/**
	 * Minimizes a given incomplete DFAs (Deterministic Finite Automaton).<br/>
	 * Runtime is in:<br/>
	 * <b>O(m * log(n))</b> with usage of<br/>
	 * <b>O(k + n + m)</b> space<br/>
	 * where 'n' is the number of states, 'm' the number of edges and 'k' the
	 * size of the alphabet.
	 * 
	 * @param services
	 *            Service provider
	 * @param operand
	 *            Automaton to minimize
	 */
	public MinimizeIncompleteDfa(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> operand) {
		this(services, operand, operand.getStateFactory(), null, false);
	}

	/**
	 * Builds the minimized automaton using the block
	 * representation of all nodes.
	 * 
	 * @return The minimized automaton
	 */
	private NestedWordAutomaton<LETTER, STATE> buildMinimizedAutomaton() {
		NestedWordAutomaton<LETTER, STATE> result =
				new NestedWordAutomaton<LETTER, STATE>(m_services,
						m_operand.getInternalAlphabet(),
						m_operand.getCallAlphabet(),
						m_operand.getReturnAlphabet(),
						m_operand.getStateFactory());
		
		// Select a representative state for every block
		LinkedList<STATE> representatives = new LinkedList<STATE>();
		HashMap<Integer, STATE> blockToNewState =
				new HashMap<Integer, STATE>();
//		HashMap<Integer, STATE> representativeIdToNewState =
//				new HashMap<Integer, STATE>();
		
		// Christian: edited for proper state factory usage
		HashSet<Integer> initialBlocks = new HashSet<Integer>();
		for (STATE initialState : m_operand.getInitialStates()) {
			initialBlocks.add(stateToBlockId.get(stateToId.get(initialState)));
		}
		for (LinkedHashSet<Integer> block : blocks) {
			if (block == null || block.isEmpty()) {
				continue;
			}
			
			ArrayList<STATE> allStates = new ArrayList<STATE>(block.size());
			Iterator<Integer> blockIt = block.iterator();
			int representativeId = blockIt.next();
			int blockId = blockToId.get(block);
			STATE representative = idToState.get(representativeId);
			representatives.add(representative);
			allStates.add(representative);
			
			while (blockIt.hasNext()) {
				allStates.add(idToState.get(blockIt.next()));
			}
			
			STATE newState = m_stateFactory.minimize(allStates);
			blockToNewState.put(blockId, newState);
			result.addState(initialBlocks.contains(blockId),
					m_operand.isFinal(representative), newState);
			
			// update mapping 'old state -> new state'
			if (m_oldState2newState != null) {
				for (final STATE oldState : allStates) {
					m_oldState2newState.put(oldState, newState);
				}
			}
		}
		//Add adjusted outgoing transitions of every representative
		for (STATE oldSrcState : representatives) {
			for (OutgoingInternalTransition<LETTER, STATE> trans :
				m_operand.internalSuccessors(oldSrcState)) {
				//Redirect the destination to the representative of the block
				int oldSrc = stateToId.get(oldSrcState);
				int oldDest = stateToId.get(trans.getSucc());
				
				STATE predState = blockToNewState.get(
						stateToBlockId.get(oldSrc));
				LETTER letter = trans.getLetter();
				STATE succState = blockToNewState.get(
						stateToBlockId.get(oldDest));
				result.addInternalTransition(predState, letter, succState);
			}
		}
		
//		for (LinkedHashSet<Integer> block : blocks) {
//			if (block == null || block.isEmpty()) {
//				continue;
//			}
//			int stateId = block.iterator().next();
//			STATE state = idToState.get(stateId);
//			representatives.add(stateId);
//			blockToRepresentatives.put(stateToBlockId.get(stateId), stateId);
//			
//			// Determine if the block contains an initial state
//			// If yes, the block also must be initial
//			Collection<STATE> initialStates = m_operand.getInitialStates();
//			boolean isBlockInitial = m_operand.isInitial(state);
//			// If representative is not initial, check if there are
//			// other states that are
//			if (!isBlockInitial) {
//				for (STATE initialState : initialStates) {
//					if (block.contains(stateToId.get(initialState))) {
//						isBlockInitial = true;
//						break;
//					}
//				}
//			}
//			
//			result.addState(isBlockInitial, m_operand.isFinal(state), state);
//		}
//		//Add adjusted outgoing transitions of every representative
//        for (int state : representatives) {
//            for (OutgoingInternalTransition<LETTER, STATE> trans :
//                    stateToOutgoingEdges.get(state)) {
//                //Redirect the destination to the representative of the block
//                int oldDest = stateToId.get(trans.getSucc());
//                int destRepresentative = blockToRepresentatives.get(
//                                stateToBlockId.get(oldDest));
//                
//                STATE predState = idToState.get(state);
//                LETTER letter = trans.getLetter();
//                STATE succState = idToState.get(destRepresentative);
//                result.addInternalTransition(predState, letter, succState);
//            }
//        }
		
		return result;
	}

	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return m_result;
	}

	/**
	 * Gets a usable unique id for a block.
	 * 
	 * @return Usable unique id for a block
	 */
	private int getUniqueBlocKId() {
		int curId = blockId;
		blockId++;
		return curId;
	}

	/**
	 * Maps state and letter to id and state to edge structures.
	 * 
	 * @param stateAmount
	 *            amount of states
	 * @param letterAmount
	 *            amount of letters
	 * 
	 */
	private void init(final int stateAmount, final int letterAmount) {
		int maxAmount = stateAmount;
		if (stateAmount < letterAmount) {
			maxAmount = letterAmount;
		}
		Iterator<STATE> states = m_operand.getStates().iterator();
		Iterator<LETTER> letters = m_operand.getInternalAlphabet().iterator();
		
		for (int i = 0; i < maxAmount; i++) {
			if (states.hasNext()) {
				STATE state = states.next();
				
				idToState.put(i, state);
				stateToId.put(state, i);
				stateToIncomingEdges.put(i,
						m_operand.internalPredecessors(state));
				// Christian: not needed anymore
//				stateToOutgoingEdges
//						.put(i, m_operand.internalSuccessors(state));
			}
			if (letters.hasNext()) {
				LETTER letter = letters.next();
				
				letterToId.put(letter, i);
			}
		}
	}
	
	/**
	 * Minimizes a given incomplete DFAs (Deterministic Finite Automaton).<br/>
	 * Runtime is in:<br/>
	 * <b>O(m * log(n))</b> with usage of<br/>
	 * <b>O(k + n + m)</b> space<br/>
	 * where 'n' is the number of states, 'm' the number of edges and 'k' the
	 * size of the alphabet.
	 * 
	 * @param incdfa
	 *            Automaton to minimize
	 * @param initialPartition
	 *            Initial partition of states 
	 * @return Minimized automaton
	 */
	private NestedWordAutomaton<LETTER, STATE> minimizeICDFA(
			final INestedWordAutomaton<LETTER, STATE> incdfa,
			final Collection<Set<STATE>> initialPartition) {
		// Initial blocks
		LinkedList<Integer> finalStates = new LinkedList<Integer>();
		LinkedList<Integer> otherStates = new LinkedList<Integer>();
		Set<STATE> allStates = stateToId.keySet();
		
		// List also known as "L"
		LinkedHashSet<LinkedHashSet<Integer>> splitCandidates =
				new LinkedHashSet<LinkedHashSet<Integer>>();
		
		if (initialPartition == null) {
			for (STATE state : allStates) {
				if (incdfa.isFinal(state)) {
					finalStates.add(stateToId.get(state));
				} else {
					otherStates.add(stateToId.get(state));
				}
			}
			//Add block only if there are final states
			int finalStatesBlockId = -1;
			boolean existsFinal = finalStates != null && !finalStates.isEmpty();
			LinkedHashSet<Integer> finalStatesBlock = null;
			if (existsFinal) {
				finalStatesBlockId = getUniqueBlocKId();
				finalStatesBlock = new LinkedHashSet<Integer>(
						finalStates);
				blockToId.put(finalStatesBlock, finalStatesBlockId);
				idToBlock.put(finalStatesBlockId, finalStatesBlock);
			}
			//Add block only if there are remaining states
			int otherStatesBlockId = -1;
			boolean existsOther = otherStates != null && !otherStates.isEmpty();
			LinkedHashSet<Integer> otherStatesBlock = null;
			if (existsOther) {
				otherStatesBlockId = getUniqueBlocKId();
				otherStatesBlock = new LinkedHashSet<Integer>(
						otherStates);
				blockToId.put(otherStatesBlock, otherStatesBlockId);
				idToBlock.put(otherStatesBlockId, otherStatesBlock);
			}
	
			for (STATE state : allStates) {
				if (incdfa.isFinal(state)) {
					stateToBlockId.put(stateToId.get(state), finalStatesBlockId);
				} else {
					stateToBlockId.put(stateToId.get(state), otherStatesBlockId);
				}
			}
			if (existsFinal) {
				blocks.add(finalStatesBlock);
			}
			if (existsOther) {
				blocks.add(otherStatesBlock);
			}

			// Initial split candidates
			if (existsFinal) {
				splitCandidates.add(finalStatesBlock);
			}
			if (existsOther) {
				splitCandidates.add(otherStatesBlock);
			}
		} else {
			// Christian: added this case
			for (Set<STATE> block : initialPartition) {
				LinkedList<Integer> newBlockStates = new LinkedList<Integer>();
				int blockId = getUniqueBlocKId();
				for (STATE state : block) {
					int stateId = stateToId.get(state);
					newBlockStates.add(stateId);
					stateToBlockId.put(stateId, blockId);
				}
				LinkedHashSet<Integer> newBlock = new LinkedHashSet<Integer>(
						newBlockStates);
				blockToId.put(newBlock, blockId);
				idToBlock.put(blockId, newBlock);
				splitCandidates.add(newBlock);
			}
		}
		
		// Split blocks until there is no candidate left
		while (!splitCandidates.isEmpty()) {
			Iterator<LinkedHashSet<Integer>> splitCandidatesIter =
					splitCandidates.iterator();
			LinkedHashSet<Integer> splitter = splitCandidatesIter.next();

			// If splitter block was deleted during a previous split, skip it
			boolean noElementWithContentLeft = false;
			while (splitter == null || blockToId.get(splitter) == null) {
				if (splitCandidatesIter.hasNext()) {
					splitCandidates.remove(splitter);
					splitCandidatesIter = splitCandidates.iterator();
					splitter = splitCandidatesIter.next();
				} else {
					noElementWithContentLeft = true;
					break;
				}
			}
			// If there is no element left that has content, break out
			if (noElementWithContentLeft) {
				break;
			}

			splitCandidates.remove(splitter);
			
			LinkedList<LinkedHashSet<Integer>> splitCandidatesToAppend =
					split(splitter, incdfa.getInternalAlphabet().size());
			
			splitCandidates.addAll(splitCandidatesToAppend);
		}
		
		return buildMinimizedAutomaton();
	}

	/**
	 * Splits blocks in order to find blocks that can be left out for
	 * minimizing.
	 * 
	 * @param splitter
	 *            Splitter block
	 * @param letterAmount
	 *            Amount of letters the automaton has,
	 *            i.e. the size of the alphabet
	 * @return List of blocks to append to list of split candidates
	 */
	private LinkedList<LinkedHashSet<Integer>> split(
			final LinkedHashSet<Integer> splitter,
			final int letterAmount) {
		// Initialize needed structures

		// Represents the set of letters that belong to edges incoming in the
		// splitter block. (Also known as "l").
		LinkedList<Integer> letterList = new LinkedList<Integer>();
		// Represents a set of sets that contain all the, splitter block,
		// incoming states, accessible by the letter of the incoming edge.
		// (Also known as "l(a)").
		HashMap<Integer, LinkedList<Integer>> stateListByLetter =
				new HashMap<Integer, LinkedList<Integer>>();
		// Signatures of the states.
		HashMap<Integer, LinkedList<Integer>> signatures =
				new HashMap<Integer, LinkedList<Integer>>();
		// Contains states that are used in splitting procedure.
		// (Also known as "s").
		LinkedList<Integer> splitStates = new LinkedList<Integer>();
		// Numbers of blocks that are used in splitting procedure.
		// (Also known as "l1").
		LinkedList<Integer> splitBlockNumbers = new LinkedList<Integer>();
		// Maps block numbers with respective states. (Also known as "t_b[i]").
		HashMap<Integer, LinkedList<Integer>> blockStateMap =
				new HashMap<Integer, LinkedList<Integer>>();
		// Contains letters that are used in splitting procedure.
		// (Also known as "l2").
		LinkedList<Integer> splitLetters = new LinkedList<Integer>();
		// Maps letters with respective states that are used in splitting
		// procedure.
		// (Also known as "t" or "t[a]").
		HashMap<Integer, LinkedList<Integer>> splitStatesOfLetter =
				new HashMap<Integer, LinkedList<Integer>>();
		
		// Step 1
		// Iterate over all states in the splitter block
		// and setup some data structures
		for (int stateInSplitter : splitter) {
			Iterator<IncomingInternalTransition<LETTER, STATE>> incomingTransitions =
					stateToIncomingEdges.get(stateInSplitter).iterator();

			while (incomingTransitions.hasNext()) {
				IncomingInternalTransition<LETTER, STATE> incomingTrans =
						incomingTransitions.next();
				int incomingState = stateToId.get(incomingTrans.getPred());
				int incomingLetter = letterToId.get(incomingTrans.getLetter());

				// Incoming edges, accessible by incoming letter
				if (!stateListByLetter.containsKey(incomingLetter)) {
					stateListByLetter.put(incomingLetter,
							new LinkedList<Integer>());
					// List of incoming letters (add letters only once)
					letterList.add(incomingLetter);
				}
				// Add incoming state to its letter list
				LinkedList<Integer> statesOfLetter = stateListByLetter
						.get(incomingLetter);
				statesOfLetter.add(incomingState);
				stateListByLetter.put(incomingLetter, statesOfLetter);
			}
		}
		
		// Step 2
		// Scan the letterList and update signatures
		int maxSignatureSize = 0;
		for (Integer letter : letterList) {
			for (Integer state : stateListByLetter.get(letter)) {
				if (!signatures.containsKey(state)) {
					signatures.put(state, new LinkedList<Integer>());
					// Remember states that have a signature
					splitStates.add(state);
				}
				// Add letter to states signature
				LinkedList<Integer> signature = signatures.get(state);
				signature.add(letter);
				signatures.put(state, signature);

				// Track maximal signature size
				if (signature.size() > maxSignatureSize) {
					maxSignatureSize = signature.size();
				}
			}
		}
		stateListByLetter.clear();
		letterList.clear();
		
		// Step 3
		// Discriminate the states
		for (Integer state : splitStates) {
			int blockNumber = stateToBlockId.get(state);
			if (!blockStateMap.containsKey(blockNumber)) {
				blockStateMap.put(blockNumber, new LinkedList<Integer>());
				// Remember blocks that are used
				splitBlockNumbers.add(blockNumber);
			}
			LinkedList<Integer> statesOfBlock = blockStateMap.get(blockNumber);
			statesOfBlock.add(state);
			blockStateMap.put(blockNumber, statesOfBlock);
		}
		
		splitStates.clear();
		for (int blockNumber : splitBlockNumbers) {
			splitStates.addAll(blockStateMap.get(blockNumber));
		}
		
		blockStateMap.clear();
		//Keep references to iterator alive.
		HashMap<Integer, Iterator<Integer>> signaturesIter =
				new HashMap<Integer, Iterator<Integer>>();
		// Iterate over all signature elements
		for (int j = 0; j < maxSignatureSize; j++) {
			for (Integer state : splitStates) {
				
				LinkedList<Integer> curSignature = signatures.get(state);
				//Use iterator for fast sequential access
				Iterator<Integer> curSignatureIter = null;
				if (!signaturesIter.containsKey(state)) {
					curSignatureIter = curSignature.iterator();
					signaturesIter.put(state, curSignatureIter);
				} else {
					curSignatureIter = signaturesIter.get(state);
				}

				// Skip this position for the letter because it
				// is not that long
				if (!curSignatureIter.hasNext()) {
					continue;
				}
				
				Integer curSigLetter = curSignatureIter.next();

				// Add state to the state list of this letter
				if (!splitStatesOfLetter.containsKey(curSigLetter)) {
					splitStatesOfLetter.put(curSigLetter,
							new LinkedList<Integer>());
					// Remember letters that are used
					splitLetters.add(curSigLetter);
				}
				LinkedList<Integer> statesOfLetter = splitStatesOfLetter
						.get(curSigLetter);
				statesOfLetter.add(state);
				splitStatesOfLetter.put(curSigLetter, statesOfLetter);
			}

			// Clear and update the split states list
			splitStates.clear();
			for (Integer letter : splitLetters) {
				splitStates.addAll(splitStatesOfLetter.get(letter));
			}
		}
		splitLetters.clear();
		
		// Step 4
		// Split the blocks

		// Change the format of the split information into a better usable
		// where the content is separated by blocks.
		// Also remove duplicate content by using a set.
		LinkedHashMap<Integer, LinkedHashSet<Integer>> splitStatesBlockWrapper =
				new LinkedHashMap<Integer, LinkedHashSet<Integer>>(blocks.size());
		LinkedHashSet<Integer> curBlockContent = new LinkedHashSet<Integer>();
		int lastBlockNumber = -1;
		int curBlockNumber = -1;
		for (int state : splitStates) {
			curBlockNumber = stateToBlockId.get(state);
			// If next block begins save old content and create a new list
			if (curBlockNumber != lastBlockNumber) {
				if (!curBlockContent.isEmpty()) {
					// If block was not used before put the list in as new
					if (splitStatesBlockWrapper.get(lastBlockNumber) == null) {
						splitStatesBlockWrapper.put(lastBlockNumber,
								curBlockContent);
					} else {
						// If the block was used before update the
						// old block and put it back in
						LinkedHashSet<Integer> oldBlockContent =
								splitStatesBlockWrapper.get(lastBlockNumber);
						oldBlockContent.addAll(curBlockContent);
						splitStatesBlockWrapper.put(lastBlockNumber,
								oldBlockContent);
					}
				}
				curBlockContent = new LinkedHashSet<Integer>();
			}
			curBlockContent.add(state);
			lastBlockNumber = curBlockNumber;
		}
		//Handle last remaining element and put the content also in
		if (!curBlockContent.isEmpty()) {
			if (splitStatesBlockWrapper.get(curBlockNumber) == null) {
				splitStatesBlockWrapper.put(curBlockNumber,
						curBlockContent);
			} else {
				// If the block was used before update the
				// old block and put it back in
				LinkedHashSet<Integer> oldBlockContent =
						splitStatesBlockWrapper.get(curBlockNumber);
				oldBlockContent.addAll(curBlockContent);
				splitStatesBlockWrapper.put(curBlockNumber,
						oldBlockContent);
			}
		}
		curBlockContent = null;
		// splitStatesBlockWrapper now contains split
		// information once per block

		// Save blockNumber of current splitter (before it gets removed)
		int splitterBlockNumber = blockToId.get(splitter);
		LinkedList<LinkedHashSet<Integer>> splitCandidatesToAppend =
				new LinkedList<LinkedHashSet<Integer>>();

		// Iterate over block content and determine splittings
		for (LinkedHashSet<Integer> blockContent
				: splitStatesBlockWrapper.values()) {
			// Setup splittings
			LinkedList<LinkedHashSet<Integer>> splittings =
					new LinkedList<LinkedHashSet<Integer>>();
			LinkedHashSet<Integer> curSplit = new LinkedHashSet<Integer>();
			LinkedList<Integer> lastSignature = null;
			for (int state : blockContent) {
				LinkedList<Integer> curSignature = signatures.get(state);
				// If next state has a different signature
				// save old content and create a new splitting.
				if (!curSignature.equals(lastSignature)) {
					if (!curSplit.isEmpty()) {
						splittings.add(curSplit);
					}
					curSplit = new LinkedHashSet<Integer>();
				}
				curSplit.add(state);
				lastSignature = curSignature;
			}
			splittings.add(curSplit);
			curSplit = null;

			// If there are missing states also add them as separate split
			LinkedHashSet<Integer> originalBlock = idToBlock.get(stateToBlockId
					.get(blockContent.iterator().next()));
			if (!blockContent.equals(originalBlock)) {
				HashSet<Integer> missingStates = new HashSet<Integer>();
				for (int state : originalBlock) {
					if (!blockContent.contains(state)) {
						missingStates.add(state);
					}
				}
				if (!missingStates.isEmpty()) {
					splittings.add(new LinkedHashSet<Integer>(missingStates));
				}
			}

			// If there are more than one set a splits must be done
			if (splittings.size() > 1) {
				
				// Remove old block
				int oldBlockId = blockToId.get(originalBlock);
				idToBlock.remove(oldBlockId);
				blockToId.remove(originalBlock);
				blocks.remove(originalBlock);
				originalBlock = null;

				// Track maximal size of split parts to not add the
				// biggest part as split candidate
				int maxSplitPartSize = -1;
				LinkedHashSet<Integer> biggestSplitPart = null;

				// Create new blocks
				for (LinkedHashSet<Integer> splitBlockPart : splittings) {
					int nextBlockId = getUniqueBlocKId();
					idToBlock.put(nextBlockId, splitBlockPart);
					blockToId.put(splitBlockPart, nextBlockId);
					blocks.add(splitBlockPart);
					for (int state : splitBlockPart) {
						stateToBlockId.put(state, nextBlockId);
					}

					// Append block to candidate list
					splitCandidatesToAppend.add(splitBlockPart);
					// Update maximal split part size
					if (splitBlockPart.size() > maxSplitPartSize) {
						biggestSplitPart = splitBlockPart;
					}
				}

				// Remove biggest split part if splitter got split
				if (oldBlockId == splitterBlockNumber) {
					splitCandidatesToAppend.remove(biggestSplitPart);
				}
			}
		}
		return splitCandidatesToAppend;
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
