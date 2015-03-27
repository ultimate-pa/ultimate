package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
	 * Initial amount of blocks.
	 */
	private static final int INITIAL_BLOCK_AMOUNT = 2;

	/**
	 * Main for testing purpose.
	 * 
	 * @param args
	 *            Not supported
	 */
	public static void main(String[] args) {
		// TODO Remove method after testing

		// Create non minimal dfa
		int size = 4;
		List<String> num2State = new ArrayList<String>(3);
		for (int i = 0; i < size; ++i) {
			num2State.add("s" + i);
		}

		List<String> num2Letter = new ArrayList<String>(1);
		for (int i = 0; i < 2; ++i) {
			num2Letter.add("a" + i);
		}

		StateFactory<String> stateFactory = new StringFactory();
		NestedWordAutomaton<String, String> inputAutomata;
		inputAutomata = new NestedWordAutomaton<String, String>(null,
				new HashSet<String>(num2Letter), null, null, stateFactory);

		// Create states
		for (int i = 0; i < size; ++i) {
			String state = num2State.get(i);
			boolean isAccepting = (i == (size - 1)) || (i == (size - 2));
			boolean isInitial = i == 0;
			inputAutomata.addState(isInitial, isAccepting, state);
		}

		// Create transitions
		String predState = num2State.get(0);
		String letter = num2Letter.get(0);
		String succState = num2State.get(2);
		inputAutomata.addInternalTransition(predState, letter, succState);
		letter = num2Letter.get(1);
		succState = num2State.get(1);
		inputAutomata.addInternalTransition(predState, letter, succState);

		predState = num2State.get(1);
		letter = num2Letter.get(0);
		succState = num2State.get(3);
		inputAutomata.addInternalTransition(predState, letter, succState);
		letter = num2Letter.get(1);
		succState = num2State.get(3);
		inputAutomata.addInternalTransition(predState, letter, succState);

		predState = num2State.get(2);
		letter = num2Letter.get(0);
		succState = num2State.get(3);
		inputAutomata.addInternalTransition(predState, letter, succState);
		letter = num2Letter.get(1);
		succState = num2State.get(2);
		inputAutomata.addInternalTransition(predState, letter, succState);

		predState = num2State.get(3);
		letter = num2Letter.get(0);
		succState = num2State.get(2);
		inputAutomata.addInternalTransition(predState, letter, succState);
		letter = num2Letter.get(1);
		succState = num2State.get(3);
		inputAutomata.addInternalTransition(predState, letter, succState);

		// XXX Remove debugging print
		System.out.println("+++++++++Before minimization:+++++++++");
		System.out.println();
		System.out.println(inputAutomata);

		// Measure time of algorithm
		long beforeStamp = System.currentTimeMillis();
		// Test minimization (state 3 and 4 should get merged)
		MinimizeIncompleteDfa<String, String> incdfa =
				new MinimizeIncompleteDfa<String, String>(
				null, inputAutomata);
		INestedWordAutomatonSimple<String, String> result = incdfa.getResult();
		long afterStamp = System.currentTimeMillis();
		long timeDiffSec = (afterStamp - beforeStamp);

		// XXX Remove debugging print
		System.out.println();
		System.out.println("+++++++++After minimization:+++++++++");
		System.out.println();
		System.out.println("Performance: " + timeDiffSec + " ms");
		System.out.println();
		System.out.println(result);
	}

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
	private final LinkedHashMap<LinkedHashSet<Integer>, Integer> blockToId;
	/**
	 * Mapping for a unique id to block.
	 */
	private final LinkedHashMap<Integer, LinkedHashSet<Integer>> idToBlock;
	/**
	 * Mapping for a unique id to letter.
	 */
	private final LinkedHashMap<Integer, LETTER> idToLetter;
	/**
	 * Mapping for a unique id to state.
	 */
	private final LinkedHashMap<Integer, STATE> idToState;
	/**
	 * Mapping for a letter to unique id.
	 */
	private final LinkedHashMap<LETTER, Integer> letterToId;
	/**
	 * Input automaton that should be minimized.
	 */
	private final INestedWordAutomaton<LETTER, STATE> m_operand;
	/**
	 * Resulting minimized automaton.
	 */
	private final NestedWordAutomaton<LETTER, STATE> m_result;
	/**
	 * Mapping for state to the block number where it is contained.
	 */
	private final HashMap<Integer, Integer> stateToBlockId;
	/**
	 * Mapping for a state to unique id.
	 */
	private final LinkedHashMap<STATE, Integer> stateToId;
	/**
	 * Mapping for state to incoming edges.
	 */
	private final HashMap<Integer, Iterable<
		IncomingInternalTransition<LETTER, STATE>>> stateToIncomingEdges;
	/**
	 * Mapping for state to outgoing edges.
	 */
	private final HashMap<Integer, Iterable<
		OutgoingInternalTransition<LETTER, STATE>>> stateToOutgoingEdges;

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
		blockToId = new LinkedHashMap<LinkedHashSet<Integer>, Integer>(
				INITIAL_BLOCK_AMOUNT);
		idToBlock = new LinkedHashMap<Integer, LinkedHashSet<Integer>>(
				INITIAL_BLOCK_AMOUNT);
		int stateAmount = operand.getStates().size();
		idToState = new LinkedHashMap<Integer, STATE>(stateAmount);
		stateToId = new LinkedHashMap<STATE, Integer>(stateAmount);
		stateToBlockId = new HashMap<Integer, Integer>(stateAmount);
		stateToIncomingEdges =
				new HashMap<Integer,
				Iterable<IncomingInternalTransition<LETTER, STATE>>>(
				stateAmount);
		stateToOutgoingEdges = new HashMap<Integer,
				Iterable<OutgoingInternalTransition<LETTER, STATE>>>(
				stateAmount);
		int letterAmount = operand.getInternalAlphabet().size();
		idToLetter = new LinkedHashMap<Integer, LETTER>(letterAmount);
		letterToId = new LinkedHashMap<LETTER, Integer>(letterAmount);

		init(stateAmount, letterAmount);

		m_result = minimizeICDFA(m_operand);
	}

	@Override
	public INestedWordAutomatonSimple<LETTER, STATE> getResult() {
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

		// XXX Remove debugging print
		System.out.println("+++++++++Minimization:+++++++++");

		for (int i = 0; i < maxAmount; i++) {
			if (states.hasNext()) {
				STATE state = states.next();

				// XXX Remove debugging print
				System.out.println("Put state: " + state + ", id: " + i);

				idToState.put(i, state);
				stateToId.put(state, i);
				stateToIncomingEdges.put(i,
						m_operand.internalPredecessors(state));
				stateToOutgoingEdges
						.put(i, m_operand.internalSuccessors(state));
			}
			if (letters.hasNext()) {
				LETTER letter = letters.next();

				// XXX Remove debugging print
				System.out.println("Put letter: " + letter + ", id: " + i);

				idToLetter.put(i, letter);
				letterToId.put(letter, i);
			}
		}

		// XXX Remove debugging print
		System.out.println();
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
		// Initial blocks
		LinkedList<Integer> finalStates = new LinkedList<Integer>();
		LinkedList<Integer> otherStates = new LinkedList<Integer>();
		Set<STATE> allStates = stateToId.keySet();

		for (STATE state : allStates) {
			if (incdfa.isFinal(state)) {
				finalStates.add(stateToId.get(state));
			} else {
				otherStates.add(stateToId.get(state));
			}
		}

		int finalStatesBlockId = getUniqueBlocKId();
		LinkedHashSet<Integer> finalStatesBlock = new LinkedHashSet<Integer>(
				finalStates);
		blockToId.put(finalStatesBlock, finalStatesBlockId);
		idToBlock.put(finalStatesBlockId, finalStatesBlock);
		int otherStatesBlockId = getUniqueBlocKId();
		LinkedHashSet<Integer> otherStatesBlock = new LinkedHashSet<Integer>(
				otherStates);
		blockToId.put(otherStatesBlock, otherStatesBlockId);
		idToBlock.put(otherStatesBlockId, otherStatesBlock);

		for (STATE state : allStates) {
			if (incdfa.isFinal(state)) {
				stateToBlockId.put(stateToId.get(state), finalStatesBlockId);
			} else {
				stateToBlockId.put(stateToId.get(state), otherStatesBlockId);
			}
		}

		blocks.add(finalStatesBlock);
		blocks.add(otherStatesBlock);

		// XXX Remove debugging print
		System.out.println("Initial Setup:");
		System.out.println("Q: " + blocks);

		// List also known as "L"
		LinkedHashSet<LinkedHashSet<Integer>> splitCandidates =
				new LinkedHashSet<LinkedHashSet<Integer>>();
		// Initial split candidates

		splitCandidates.add(finalStatesBlock);
		splitCandidates.add(otherStatesBlock);

		// XXX Remove debugging print
		System.out.println("L: " + splitCandidates);
		int splitRuns = 1;

		// Split blocks until there is no candidate left
		while (!splitCandidates.isEmpty()) {
			Iterator<LinkedHashSet<Integer>> splitCandidatesIter = splitCandidates
					.iterator();
			LinkedHashSet<Integer> splitter = splitCandidatesIter.next();

			// If splitter block was deleted during a previous split, skip it
			boolean noElementWithContentLeft = false;
			while (splitter == null || blockToId.get(splitter) == null) {
				if (splitCandidatesIter.hasNext()) {
					LinkedHashSet<Integer> nextSplitter = splitCandidatesIter
							.next();
					splitCandidates.remove(splitter);
					splitter = nextSplitter;
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

			// XXX Remove debugging print
			System.out.println();
			System.out.println("Split run " + splitRuns + ":");
			System.out.println("Q: " + blocks);
			System.out.println("S: " + splitter);
			System.out.println("L: " + splitCandidates);

			LinkedList<LinkedHashSet<Integer>> splitCandidatesToAppend =
					split(splitter, incdfa.getInternalAlphabet().size());

			splitCandidates.addAll(splitCandidatesToAppend);

			// XXX Remove debugging print information
			splitRuns++;
		}
		
		// XXX Remove debugging print
		System.out.println();
		System.out.println("Minimzation finished. Result:");
		System.out.println("Q: " + blocks);
		
		
		// TODO Build new automaton
		return null;
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
		HashMap<Integer, ArrayList<Integer>> signatures =
				new HashMap<Integer, ArrayList<Integer>>();
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

		// XXX Remove debugging print
		System.out.println();
		System.out.println("Step 1:");
		String letterListText = letterList.toString().replaceAll("0", "a")
				.replaceAll("1", "b");
		System.out.println("l: " + letterListText);
		for (Map.Entry<Integer, LinkedList<Integer>> entry : stateListByLetter
				.entrySet()) {
			System.out.println("l(" + ((char) ('a' + entry.getKey())) + "): "
					+ entry.getValue());
		}

		// Step 2
		// Scan the letterList and update signatures
		int maxSignatureSize = 0;
		for (Integer letter : letterList) {
			for (Integer state : stateListByLetter.get(letter)) {
				if (!signatures.containsKey(state)) {
					signatures.put(state, new ArrayList<Integer>(letterAmount));
					// Remember states that have a signature
					splitStates.add(state);
				}
				// Add letter to states signature
				ArrayList<Integer> signature = signatures.get(state);
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

		// XXX Remove debugging print
		System.out.println();
		System.out.println("Step 2:");
		for (Map.Entry<Integer, ArrayList<Integer>> entry : signatures
				.entrySet()) {
			String signatureText = entry.getValue().toString()
					.replaceAll("0", "a").replaceAll("1", "b");
			System.out.println("sig(" + entry.getKey() + "): "
					+ signatureText);
		}
		System.out.println("s: " + splitStates);

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

		// XXX Remove debugging print
		System.out.println();
		System.out.println("Step 3:");
		String splitBlockNumbersText = splitBlockNumbers.toString()
				.replaceAll("0", "I").replaceAll("1", "II")
				.replaceAll("2", "III").replaceAll("3", "IV")
				.replaceAll("4", "V").replaceAll("5", "VI")
				.replaceAll("6", "VII").replaceAll("7", "IIX");
		System.out.println("l1: " + splitBlockNumbersText);
		for (Map.Entry<Integer, LinkedList<Integer>> entry : blockStateMap
				.entrySet()) {
			String blockStateMapText = entry.getKey().toString()
					.replaceAll("0", "I").replaceAll("1", "II")
					.replaceAll("2", "III").replaceAll("3", "IV")
					.replaceAll("4", "V").replaceAll("5", "VI")
					.replaceAll("6", "VII").replaceAll("7", "IIX");
			System.out.println("tb[" + blockStateMapText + "]: "
					+ entry.getValue());
		}

		blockStateMap.clear();
		// Iterate over all signature elements
		for (int j = 0; j < maxSignatureSize; j++) {
			for (Integer state : splitStates) {
				ArrayList<Integer> stateSignature = signatures.get(state);

				// Skip this position for the letter because it
				// is not that long
				if (j >= stateSignature.size()) {
					continue;
				}

				Integer stateSigLetter = stateSignature.get(j);

				// Add state to the state list of this letter
				if (!splitStatesOfLetter.containsKey(stateSigLetter)) {
					splitStatesOfLetter.put(stateSigLetter,
							new LinkedList<Integer>());
					// Remember letters that are used
					splitLetters.add(stateSigLetter);
				}
				LinkedList<Integer> statesOfLetter = splitStatesOfLetter
						.get(stateSigLetter);
				statesOfLetter.add(state);
				splitStatesOfLetter.put(stateSigLetter, statesOfLetter);

				// XXX Remove debugging print
				System.out.println();
				System.out.println("t[" + ((char) ('a' + stateSigLetter))
						+ "]: " + statesOfLetter);
			}

			// Clear and update the split states list
			splitStates.clear();
			for (Integer letter : splitLetters) {
				splitStates.addAll(splitStatesOfLetter.get(letter));
			}

			// XXX Remove debugging print
			System.out.println();
			String splitLettersText = splitLetters.toString()
					.replaceAll("0", "a").replaceAll("1", "b");
			System.out.println("l2: " + splitLettersText);
			System.out.println("s: " + splitStates);
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

		// XXX Remove debugging print
		System.out.println();
		System.out.println("Step 4:");
		System.out.print("s: [");

		// XXX Remove debugging print
		for (LinkedHashSet<Integer> blockContent
				: splitStatesBlockWrapper.values()) {
			for (int state : blockContent) {
				System.out.print(state + ", ");
			}
			System.out.print("| ");
		}
		System.out.println("]");

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
			ArrayList<Integer> lastSignature = null;
			for (int state : blockContent) {
				ArrayList<Integer> curSignature = signatures.get(state);
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

				// XXX Remove debugging print
				System.out.println("Splitting for block: " + splittings);
				System.out.println("Removed block: " + originalBlock);

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

					// XXX Remove debugging print
					System.out.println("Created block: " + splitBlockPart);
				}

				// Remove biggest split part if splitter got split
				if (oldBlockId == splitterBlockNumber) {
					splitCandidatesToAppend.remove(biggestSplitPart);
				}
			}
		}

		// XXX Remove debugging print
		System.out.println("Split candidates to append: "
				+ splitCandidatesToAppend);

		return splitCandidatesToAppend;
	}
}