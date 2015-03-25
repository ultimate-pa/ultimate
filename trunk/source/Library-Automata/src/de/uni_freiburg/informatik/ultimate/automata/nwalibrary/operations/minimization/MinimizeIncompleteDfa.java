package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StringFactory;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

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
	 * Class for a block that contains states.
	 * 
	 * @author Daniel Tischner
	 *
	 */
	private final class Block implements Comparable<Block> {
		/**
		 * Elements of the block.
		 */
		private final DoublyLinkedList<STATE> m_elements;
		/**
		 * Size of the block.
		 */
		private final int m_size;

		/**
		 * Creates a new block with given elements.
		 * 
		 * @param elements
		 *            Elements of the block
		 */
		public Block(final Collection<STATE> elements) {
			m_size = elements.size();
			m_elements = new DoublyLinkedList<STATE>();
			for (STATE state : elements) {
				m_elements.add(state);
			}
		}

		@Override
		public int compareTo(Block o) {
			return Integer.compare(getSize(), o.getSize());
		}

		/**
		 * Gets the elements.
		 * 
		 * @return the elements to get
		 */
		public DoublyLinkedList<STATE> getElements() {
			return m_elements;
		}

		/**
		 * Gets the size.
		 * 
		 * @return the size to get
		 */
		public int getSize() {
			return m_size;
		}
	}

	/**
	 * Compares states by the number of the block they belong to.
	 * 
	 * @author Daniel Tischner
	 *
	 */
	private final class StateComparator implements Comparator<STATE> {
		@Override
		public int compare(STATE o1, STATE o2) {
			Block block1 = stateToBlock.get(o1);
			Block block2 = stateToBlock.get(o2);
			return Integer
					.compare(blockToId.get(block1), blockToId.get(block2));
		}
	}

	/**
	 * Main for testing purpose.
	 * 
	 * @param args
	 *            Not supported
	 */
	public static void main(String[] args) {
		// TODO Remove method after testing

		// Create non minimal dfa
		int size = 3;
		List<String> num2State = new ArrayList<String>(3);
		for (int i = 0; i < size; ++i) {
			num2State.add("s" + i);
		}

		List<String> num2Letter = new ArrayList<String>(1);
		for (int i = 0; i < 1; ++i) {
			num2Letter.add("a" + i);
		}

		StateFactory<String> stateFactory = new StringFactory();
		NestedWordAutomaton<String, String> inputAutomata;
		inputAutomata = new NestedWordAutomaton<String, String>(null,
				new HashSet<String>(num2Letter), null, null, stateFactory);

		// Create states
		for (int i = 0; i < size; ++i) {
			String state = num2State.get(i);
			boolean isAccepting = i == (size - 1);
			boolean isInitial = i == 0;
			inputAutomata.addState(isInitial, isAccepting, state);
		}

		// Create transitions
		for (int i = 1; i < size; i++) {
			int predStateIndex = 0;
			int letterIndex = 0;
			int succStateIndex = i;

			String predState = num2State.get(predStateIndex);
			String letter = num2Letter.get(letterIndex);
			String succState = num2State.get(succStateIndex);

			inputAutomata.addInternalTransition(predState, letter, succState);
		}

		System.out.println("+++++++++Before minimization:+++++++++");
		System.out.println();
		System.out.println(inputAutomata);

		// Measure time of algo
		long beforeStamp = System.currentTimeMillis();
		// Test minimization (all states except of
		// 0 and the last should get removed)
		MinimizeIncompleteDfa<String, String> incdfa = new MinimizeIncompleteDfa<String, String>(
				null, inputAutomata);
		INestedWordAutomatonSimple<String, String> result = incdfa.getResult();
		long afterStamp = System.currentTimeMillis();
		long timeDiffSec = (afterStamp - beforeStamp) / 1000;

		System.out.println("+++++++++After minimization:+++++++++");
		System.out.println();
		System.out.println("Performance: " + timeDiffSec + " sec");
		System.out.println();
		System.out.println(result);
	}

	/**
	 * Maps block numbers with respective states. (Also known as "t_b[i]").
	 */
	private final HashMap<Integer, LinkedList<STATE>> blockStateMap = new HashMap<Integer, LinkedList<STATE>>();
	/**
	 * Mapping for block to a unique id.
	 */
	private final HashMap<Block, Integer> blockToId = new HashMap<Block, Integer>();
	/**
	 * Mapping for a unique id to block.
	 */
	private final HashMap<Integer, Block> idToBlock = new HashMap<Integer, Block>();
	/**
	 * Represents the set of letters that belong to edges incoming in the
	 * splitter block. (Also known as "l").
	 */
	private final HashSet<LETTER> letterList = new HashSet<LETTER>();
	/**
	 * Input automaton that should be minimized.
	 */
	private final INestedWordAutomaton<LETTER, STATE> m_operand;
	/**
	 * Resulting minimized automaton.
	 */
	private final NestedWordAutomaton<LETTER, STATE> m_result;
	/**
	 * Maps states, that have an edge pointing to the splitter block with their
	 * respective letters, ordered by the block numbers the states belongs to.
	 */
	private TreeMap<STATE, LinkedList<LETTER>> setPPlus = new TreeMap<STATE, LinkedList<LETTER>>(
			new StateComparator());
	/**
	 * Signatures of the states.
	 */
	private final HashMap<STATE, LinkedList<LETTER>> signatures = new HashMap<STATE, LinkedList<LETTER>>();
	/**
	 * Numbers of blocks that are used in splitting procedure. (Also known as
	 * "l1").
	 */
	private final LinkedList<Integer> splitBlockNumbers = new LinkedList<Integer>();
	/**
	 * Contains letters that are used in splitting procedure. (Also known as
	 * "l2").
	 */
	private final LinkedList<LETTER> splitLetters = new LinkedList<LETTER>();
	/**
	 * Contains states that are used in splitting procedure. (Also known as
	 * "s").
	 */
	private final LinkedList<STATE> splitStates = new LinkedList<STATE>();
	/**
	 * Maps letters with respective states that are used in splitting procedure.
	 * (Also known as "t" or "t[a]").
	 */
	private final HashMap<LETTER, LinkedList<STATE>> splitStatesOfLetter = new HashMap<LETTER, LinkedList<STATE>>();
	/**
	 * Represents an set of sets that contain all the, splitter block, incoming
	 * states, accessible by the letter of the incoming edge. (Also known as
	 * "l(a)").
	 */
	private final HashMap<LETTER, HashSet<STATE>> stateListByLetter = new HashMap<LETTER, HashSet<STATE>>();

	/**
	 * Mapping for state to the block where it is contained
	 */
	private final HashMap<STATE, Block> stateToBlock = new HashMap<STATE, Block>();

	/**
	 * Mapping for state to incoming edges
	 */
	private final HashMap<STATE, Iterable<IncomingInternalTransition<LETTER, STATE>>> stateToIncomingEdges = new HashMap<STATE, Iterable<IncomingInternalTransition<LETTER, STATE>>>();

	/**
	 * Mapping for state to outgoing edges.
	 */
	private final HashMap<STATE, Iterable<OutgoingInternalTransition<LETTER, STATE>>> stateToOutgoingEdges = new HashMap<STATE, Iterable<OutgoingInternalTransition<LETTER, STATE>>>();

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
	public MinimizeIncompleteDfa(final IUltimateServiceProvider services,
			final INestedWordAutomaton<LETTER, STATE> operand) {
		super(services, operand.getStateFactory(), "minimizeICDFA", operand);
		m_operand = operand;
		m_result = minimizeICDFA(m_operand);
	}

	@Override
	public INestedWordAutomatonSimple<LETTER, STATE> getResult() {
		return m_result;
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
	 * @return Minimized automaton
	 */
	private NestedWordAutomaton<LETTER, STATE> minimizeICDFA(
			final INestedWordAutomaton<LETTER, STATE> incdfa) {

		// TODO Remove all structures that are not needed
		Collection<STATE> finalStatesColl = incdfa.getFinalStates();
		Collection<STATE> allStates = incdfa.getStates();
		HashSet<STATE> otherStatesColl = new HashSet<STATE>(allStates);
		otherStatesColl.removeAll(finalStatesColl);

		Block finalStatesBlock = new Block(finalStatesColl);
		Block otherStatesBlock = new Block(otherStatesColl);

		// Initial blocks
		DoublyLinkedList<Block> blocks = new DoublyLinkedList<Block>();
		blocks.add(finalStatesBlock);
		blocks.add(otherStatesBlock);

		// Initialize mappings
		int blockKey = 0;
		for (Block b : blocks) {
			blockToId.put(b, blockKey);
			idToBlock.put(blockKey, b);
			blockKey++;
		}
		for (STATE state : allStates) {
			stateToOutgoingEdges.put(state, incdfa.internalSuccessors(state));
			stateToIncomingEdges.put(state, incdfa.internalPredecessors(state));
			if (incdfa.isFinal(state)) {
				stateToBlock.put(state, finalStatesBlock);
			} else {
				stateToBlock.put(state, otherStatesBlock);
			}
		}

		LinkedList<Block> splitCandidates = new LinkedList<Block>();
		// Initial split candidates
		splitCandidates.add(finalStatesBlock);
		splitCandidates.add(otherStatesBlock);

		// Split blocks until there is no candidate left
		while (!splitCandidates.isEmpty()) {
			Block splitter = splitCandidates.poll();
			blocks = split(splitter, blocks);

			// TODO Code after split
			// splitCandidates.addAll(blocks.);
		}

		return null;
	}

	/**
	 * Splits blocks in order to find blocks that can be left out for
	 * minimizing.
	 * 
	 * @param splitter
	 *            Splitter block
	 * @param blocks
	 *            List of all blocks
	 * @return New list of all blocks
	 */
	private DoublyLinkedList<Block> split(final Block splitter,
			final DoublyLinkedList<Block> blocks) {
		// Step 1
		// Iterate over all states in the splitter block
		// and setup some data structures
		for (STATE stateInSplitter : splitter.getElements()) {
			Iterator<IncomingInternalTransition<LETTER, STATE>> incomingIter = stateToIncomingEdges
					.get(stateInSplitter).iterator();

			while (incomingIter.hasNext()) {
				// TODO Is it correct to use all "incoming" edges,
				// even from states that are already in the splitter block?
				IncomingInternalTransition<LETTER, STATE> incomingTrans = incomingIter
						.next();
				STATE incomingState = incomingTrans.getPred();
				LETTER incomingLetter = incomingTrans.getLetter();

				// Incoming letter list
				letterList.add(incomingLetter);

				// Incoming edges, accessible by incoming letter
				if (!stateListByLetter.containsKey(incomingLetter)) {
					stateListByLetter.put(incomingLetter, new HashSet<STATE>());
				}
				HashSet<STATE> statesOfLetter = stateListByLetter
						.get(incomingLetter);
				statesOfLetter.add(incomingState);
				stateListByLetter.put(incomingLetter, statesOfLetter);

				// Incoming edges, accessible by incoming state
				if (!setPPlus.containsKey(incomingState)) {
					setPPlus.put(incomingState, new LinkedList<LETTER>());
				}
				LinkedList<LETTER> lettersOfState = setPPlus.get(incomingState);
				lettersOfState.add(incomingLetter);
				setPPlus.put(incomingState, lettersOfState);
			}
		}

		int maxSignatureSize = 0;
		// Step 2
		// Scan the letterList and update signatures
		for (LETTER letter : letterList) {
			for (STATE state : stateListByLetter.get(letter)) {
				// TODO Is it important that signature is sorted by letterLists
				// order?
				// If yes letterList needs to be sorted accordingly.
				LinkedList<LETTER> signature = setPPlus.get(state);
				if (signature != null) {
					// List 's' is not needed because 'signatures' only
					// contains states with content
					// (instead iterate over signatures key set).
					signatures.put(state, signature);
					// Track maximal signature size
					if (signature.size() > maxSignatureSize) {
						maxSignatureSize = signature.size();
					}
				}
			}
			stateListByLetter.clear();
		}
		letterList.clear();

		// Step 3
		// Discriminate the states
		for (STATE state : signatures.keySet()) {
			int blockNumber = blockToId.get(stateToBlock.get(state));
			// TODO Is it important to only add the block number once?
			// Paper does not cover this.
			// Add block to list
			splitBlockNumbers.add(blockNumber);

			// Add state to the block list
			if (!blockStateMap.containsKey(blockNumber)) {
				blockStateMap.put(blockNumber, new LinkedList<STATE>());
			}
			LinkedList<STATE> statesOfBlock = blockStateMap.get(blockNumber);
			statesOfBlock.add(state);
			blockStateMap.put(blockNumber, statesOfBlock);
		}

		// Now we need the list "s" as state list.
		splitStates.clear();
		for (Integer blockNumber : splitBlockNumbers) {
			splitStates.addAll(blockStateMap.get(blockNumber));
		}

		// TODO Is this statement really correct? Paper does not mention it.
		blockStateMap.clear();
		// Iterate over all signature elements
		for (int j = 0; j < maxSignatureSize; j++) {
			for (STATE state : splitStates) {
				LinkedList<LETTER> statesSigLetters = signatures.get(state);

				// Skip this position for the letter because it is not that long
				if (j >= statesSigLetters.size()) {
					continue;
				}

				// TODO Expensive get-access because data structure
				// is linked list, maybe find a better
				LETTER statesSigLetter = statesSigLetters.get(j);

				// Add state to the state list of this letter
				if (!splitStatesOfLetter.containsKey(statesSigLetter)) {
					splitStatesOfLetter.put(statesSigLetter,
							new LinkedList<STATE>());
				}
				LinkedList<STATE> statesOfLetter = splitStatesOfLetter
						.get(statesSigLetter);
				statesOfLetter.add(state);
				splitStatesOfLetter.put(statesSigLetter, statesOfLetter);

				// Add letter to letter list
				splitLetters.add(statesSigLetter);
			}
		}
		splitStates.clear();
		for (LETTER letter : splitLetters) {
			splitStates.addAll(splitStatesOfLetter.get(letter));
		}

		// Step 4
		// Split the blocks
		// TODO I did not get that step...

		// Clear all data structures that where
		// used in the splitting procedure
		letterList.clear();
		stateListByLetter.clear();
		setPPlus.clear();
		signatures.clear();
		splitBlockNumbers.clear();
		blockStateMap.clear();
		splitStates.clear();
		splitStatesOfLetter.clear();
		splitLetters.clear();

		return null;
	}
}