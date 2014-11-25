/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.math.BigInteger;
import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Random;

import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StringFactory;

/**
 * Utility class that provides a method {@link #generatePackedRandomDFA(int, int, int, boolean, boolean)
 * generatePackedRandomDFA(...)} to generate
 * uniform or not-uniform distributed random connected or not connected total or not-total DFAs
 * (Deterministic finite automaton) in a specific packed int[] array format. This format can be
 * unpacked by {@link #extractPackedDFA(int[], int, int, int, Random) extractPackedDFA(...)}<br/><br/>
 * Runtime is in:<br/>
 * <b>O(n^3 * k) * O(random)</b> if result should be uniform and caching is not enabled<br/>
 * <b>O(n * k) * O(random)</b> if result should not be uniform<br/>
 * <b>O(n^2 * k) * O(random)</b> if result should be uniform, caching is enabled and there
 * is a valid cache (n must be equals)<br/>
 * where 'n' is the amount of nodes, 'k'
 * the size of the alphabet and 'random' methods of {@link java.util.Random}.
 * 
 * @author Daniel Tischner
 *
 */
public final class GetRandomDfa implements IOperation<String, String> {

	/**
	 * Extracts a DFA that is packed into the int[] array format specified by
	 * {@link #generatePackedRandomDFA(int, int, int, boolean, boolean)
	 * generatePackedRandomDFA(...)} and returns it as
	 * {@link NestedWordAutomaton}.<br />
	 * Runtime is in <b>O(size * alphabetSize)</b>.
	 * 
	 * @param dfa
	 *            The DFA to extract in the int[] array format specified by
	 *            {@link #generatePackedRandomDFA(int, int, int, boolean, boolean)
	 *            generatePackedRandomDFA(...)}
	 * @param size
	 *            Amount of nodes also the size of the automaton
	 * @param alphabetSize
	 *            Size of the alphabet
	 * @param numOfAccStates
	 *            Amount of accepting states
	 * @param isTotal
	 *            If transition function of DFA was set to be total or not.
	 *            A wrong assignment will lead to a false number of nodes.
	 * @param rnd
	 *            Random generator
	 * @return As {@link NestedWordAutomaton} extracted DFA
	 */
	public static NestedWordAutomaton<String, String> extractPackedDFA(
			int[] dfa, int size, int alphabetSize, int numOfAccStates, boolean isTotal,
			Random rnd) {
		List<String> num2State = new ArrayList<String>(size);
		for (int i = 0; i < size; ++i) {
			num2State.add(PREFIX_NODE + i);
		}
		String initialState = num2State.get(0);

		List<String> num2Letter = new ArrayList<String>(alphabetSize);
		for (int i = 0; i < alphabetSize; ++i) {
			num2Letter.add(PREFIX_TRANSITION + i);
		}

		StateFactory<String> stateFactory = new StringFactory();
		NestedWordAutomaton<String, String> result;
		result = new NestedWordAutomaton<String, String>(new HashSet<String>(
				num2Letter), null, null, stateFactory);

		List<String> shuffledStateList = new ArrayList<String>(num2State);
		Collections.shuffle(shuffledStateList, rnd);
		// Accepting states
		for (int i = 0; i < numOfAccStates; ++i) {
			String state = shuffledStateList.get(i);
			if (state.equals(initialState)) {
				result.addState(true, true, state);
			} else {
				result.addState(false, true, state);
			}
		}
		// Non-accepting states
		for (int i = numOfAccStates; i < size; ++i) {
			String state = shuffledStateList.get(i);
			if (state.equals(initialState)) {
				result.addState(true, false, state);
			} else {
				result.addState(false, false, state);
			}
		}

		// Transitions
		int lengthOfUsableSequence = dfa.length;
		//Skip transitions of the sink state for non-total DFAs.
		//This simulates non-total DFAs because the generator only returns total DFAs.
		if (!isTotal) {
			lengthOfUsableSequence -= alphabetSize;
		}
		for (int i = 0; i < lengthOfUsableSequence; i++) {
			int predStateIndex = (int) Math.floor((i + 0.0) / alphabetSize);
			int letterIndex = i % alphabetSize;
			int succStateIndex = dfa[i];
			//Skip transition if it points to a node out of the wished size.
			//This node is the sink node for non-total DFAs.
			if(dfa[i] < size) {
				String predState = num2State.get(predStateIndex);
				String letter = num2Letter.get(letterIndex);
				String succState = num2State.get(succStateIndex);

				result.addInternalTransition(predState, letter, succState);
			}
		}

		return result;
	}

	/**
	 * Generates a uniform or non-uniform distributed random connected total
	 * DFA with a given amount of nodes and size of alphabet.<br />
	 * Finally returns the DFA in a specific int[] array format.<br /><br />
	 * The int[] array format is a sequence of numbers that represents a breadth-first
	 * search where each state and edge is ordered by '<'.<br /><br />
	 * Example:<br />
	 * [0,1,0,0,1,2] with 3 nodes and an alphabet of size 2.<br />
	 * [0,1|0,0|1,2] each of the 3 nodes has 2 outgoing edges where the number denotes
	 * the destination.<br />
	 * e.g. 2nd edge of first node points to the second node.
	 * @param size Amount of nodes also the size of the automaton
	 * @param alphabetSize Size of the alphabet
	 * @param numOfAccStates Amount of accepting states
	 * @param ensureIsUniform If true ensures a uniform distribution of the connected
	 * DFAs at high cost of performance for big 'size'.
	 * If false random classes of DFAs get favored over other random classes but the
	 * generation is very fast.
	 * @param enableCaching If true enables caching of pre-calculated results for future
	 * similar requests. If false caching will not be done.
	 * Best results can be achieved by executing requests with same 'size' and similar
	 * 'alphabetSize' behind one another.
	 * @return Uniform or non-uniform distributed random connected total
	 * DFA in a specific int[] array format
	 */
	public static int[] generatePackedRandomDFA(int size, int alphabetSize,
			int numOfAccStates, boolean ensureIsUniform, boolean enableCaching)
			throws IllegalArgumentException {
		if (size < 1 || alphabetSize < 1) {
			throw new IllegalArgumentException(
					"Neither 'size' nor 'alphabetSize' must be less than one.");
		}
		if (numOfAccStates < 0 || numOfAccStates > size) {
			throw new IllegalArgumentException(
					"'numOfAccStates' must not exceed 'size' or be less than zero.");
		}
		final int SEQUENCE_LENGTH = size * alphabetSize;

		int[] sequence = new int[SEQUENCE_LENGTH];
		int curSequenceIndex = 0;

		// Special case where size == 1
		if (size == 1) {
			for (int i = 0; i < alphabetSize; i++) {
				sequence[curSequenceIndex] = 0;
				curSequenceIndex++;
			}
			return sequence;
		}

		// Case where size >= 2
		final Random rnd = new Random();

		if (ensureIsUniform) {
			preCalcPermutationsTable(size, alphabetSize, SEQUENCE_LENGTH,
					enableCaching);
		}

		int lastFlag = -1;
		// Calculate the flags for each node and generate the sequence from left
		// to right until all nodes are reached by an edge.
		for (int i = 1; i <= size - 1; i++) {
			int curFlag = generateFlag(i, lastFlag + 1, alphabetSize,
					permutationsTable, rnd, ensureIsUniform);
			for (int j = lastFlag + 1; j <= curFlag - 1; j++) {
				// Only use nodes that were already reached
				sequence[curSequenceIndex] = rnd.nextInt(i);
				curSequenceIndex++;
			}
			sequence[curSequenceIndex] = i;
			curSequenceIndex++;
			lastFlag = curFlag;
		}
		// Now all nodes are reached by an edge and the rest of the sequence can
		// be filled up by using all nodes as edge destinations.
		for (int i = lastFlag + 1; i <= SEQUENCE_LENGTH - 1; i++) {
			sequence[curSequenceIndex] = rnd.nextInt(size);
			curSequenceIndex++;
		}

		if (!enableCaching) {
			permutationsTable = null;
		}

		return sequence;
	}

	/**
	 * Generates a flag for a given node using the first possible position at
	 * where it is allowed to appear.<br />
	 * The flag represents the first edge in the DFA that points to the given
	 * node, as index in the string format sequence (specified by
	 * {@link #generatePackedRandomDFA(int, int, int, boolean, boolean)
	 * generatePackedRandomDFA(...)}).<br />
	 * It takes the correct probability of each flag, by calculation of the
	 * number of all possible DFAs with this setting, into account.<br/>
	 * <br/>
	 * This method is used by random DFA generation to ensure that some rules
	 * like <i>'every node must get accessed before it is reached in the
	 * sequence'</i> are satisfied.<br/><br/>
	 * Runtime is in:<br/>
	 * <b>O(n * k) * O(random)</b><br/>
	 * where 'n' is the amount of nodes, 'k'
	 * the size of the alphabet and 'random' methods of {@link java.util.Random}.
	 * 
	 * @param node
	 *            Node to calculate flag for
	 * @param firstPossiblePos
	 *            First possible position in the sequence at where the flag is
	 *            allowed to appear
	 * @param alphabetSize
	 *            Size of the alphabet
	 * @param permutationsTable
	 *            2D Table where permutationsTable[m][j] is the number of DFAs
	 *            that have the first occurrence of node 'm' at position 'j' in
	 *            the sequence. Therefore it has size [size][size *
	 *            alphabetSize].
	 * @param rnd
	 *            Random generator
	 * @param ensureIsUniform
	 *            If true ensures correct flags for a uniform distribution of
	 *            the DFAs at high cost of performance for big 'size'. If false
	 *            random classes of DFAs get favored over other random classes
	 *            but the generation of the flags is very fast.
	 * @return Flag for the given node
	 */
	private static int generateFlag(int node, int firstPossiblePos,
			int alphabetSize, BigInteger[][] permutationsTable, Random rnd,
			boolean ensureIsUniform) {
		/*
		 * The length of the sequence before 'node's edges are reached. Flag
		 * must appear before this to satisfy all rules.
		 */
		final int PRE_SEQUENCE_LENGTH = node * alphabetSize;

		// If a uniform distribution must not be ensured randomly select a
		// possible position for the flag.
		if (!ensureIsUniform) {
			return rnd.nextInt(PRE_SEQUENCE_LENGTH - firstPossiblePos)
					+ firstPossiblePos;
		}

		BigInteger permutations = BigInteger.ZERO;

		// Contains the numbers of DFAs including a probability of it where the
		// first occurrence of 'node' is at position 'index'.
		BigInteger[] permutationsPerStep = new BigInteger[PRE_SEQUENCE_LENGTH
				- firstPossiblePos];

		int counter = 0;
		// Calculate the number of DFAs including a probability of it where the
		// first occurrence of 'node' is between 'firstPossiblePos' and
		// 'PRE_SEQUENCE_LENGTH - 1'.
		for (int i = firstPossiblePos; i <= PRE_SEQUENCE_LENGTH - 1; i++) {
			permutationsPerStep[counter] = permutationsTable[node][i]
					.multiply(BigInteger.valueOf((int) Math.pow(node, i
							- firstPossiblePos)));
			permutations = permutations.add(permutationsPerStep[counter]);
			counter++;
		}
		// Randomly select one of all possible permutations including its
		// probability
		BigInteger permutation = nextRandomBigInteger(
				permutations.add(BigInteger.ONE), rnd);

		counter = 0;
		// Calculate the flag using the probability of each DFA setting and the
		// selected permutation
		for (int i = firstPossiblePos; i <= PRE_SEQUENCE_LENGTH - 1; i++) {
			if (permutation.compareTo(permutationsPerStep[counter]) < 0) {
				return i;
			} else {
				permutation = permutation
						.subtract(permutationsPerStep[counter]);
			}
			counter++;
		}
		return PRE_SEQUENCE_LENGTH - 1;
	}

	/**
	 * Generates a uniform distributed random {@link BigInteger} between 0
	 * (inclusive) and 'upperBound' (exclusive) using a given random generator.<br/><br/>
	 * Runtime is in:<br/>
	 * <b>O(2 * random)</b><br/>
	 * where 'random' are methods of {@link java.util.Random}.
	 * 
	 * @param upperBound
	 *            Upper bound for the generated number (exclusive)
	 * @param rnd
	 *            Random generator
	 * @return Uniform distributed random {@link BigInteger} between 0
	 *         (inclusive) and 'upperBound' (exclusive)
	 */
	private static BigInteger nextRandomBigInteger(BigInteger upperBound,
			Random rnd) {
		BigInteger result = new BigInteger(upperBound.bitLength(), rnd);

		// Converges to one iteration because chance decreases by 0.5 every
		// step.
		while (result.compareTo(upperBound) >= 0) {
			result = new BigInteger(upperBound.bitLength(), rnd);
		}
		return result;
	}

	/**
	 * Pre-calculates the permutations table where permutationsTable[m][j] is
	 * the number of DFAs that have the first occurrence of node 'm' at position
	 * 'j' in the sequence.<br/><br/>
	 * Runtime is in:<br/>
	 * <b>O(n * k)</b> if caching is not enabled<br/>
	 * <b>O(1)</b> if caching is enabled and n, k are equal to cached version<br/>
	 * <b>O(k)</b> if caching is enabled and n is equal to cached version<br/>
	 * where 'n' is the amount of nodes, 'k' the size of the alphabet.
	 * 
	 * @param size
	 *            Amount of nodes
	 * @param alphabetSize
	 *            Size of alphabet
	 * @param sequenceLength
	 *            Length of sequence that must be size * alphabetSize
	 * @param enableCaching
	 *            If true enables caching of pre-calculated results for future
	 *            similar requests. If false caching will not be done.
	 */
	private static void preCalcPermutationsTable(int size, int alphabetSize,
			int sequenceLength, boolean enableCaching) {
		boolean hasUsableCache = enableCaching && permutationsTable != null
				&& permutationsTable[0] != null
				&& permutationsTable.length == size;
		if (hasUsableCache && permutationsTable[0].length == sequenceLength) {
			return;
		}

		BigInteger[][] nextPermutationsTable = new BigInteger[size][sequenceLength];

		// Calculate the bottom row of the table.
		for (int i = (size - 1) * alphabetSize - 1; i >= size - 2; i--) {

			// If there is a usable cache, the second index is in range and
			// there is a value then copy it because this row is independent of
			// changes in alphabetSize.
			if (hasUsableCache && i < permutationsTable[0].length
					&& permutationsTable[size - 1] != null
					&& permutationsTable[size - 1][i] != null) {
				nextPermutationsTable[size - 1][i] = permutationsTable[size - 1][i];
			} else {
				nextPermutationsTable[size - 1][i] = BigInteger.valueOf(size)
						.pow(sequenceLength - 1 - i);
			}
		}
		// Calculate the other rows from bottom to top and right to left using
		// the other entries.
		// Caching is not possible because all entries here are dependent on
		// changes in size and alphabetSize.
		for (int curNode = size - 2; curNode >= 1; curNode--) {
			// Length of the sequence before 'curNode's edges are reached.
			int preSequenceLength = curNode * alphabetSize;

			// Calculate the rightest entry of the current row using the
			// diagonal right entry of the bottom row.
			BigInteger permutations = BigInteger.ZERO;

			for (int i = 0; i <= alphabetSize - 1; i++) {
				permutations = permutations
						.add(nextPermutationsTable[curNode + 1][preSequenceLength
								+ i].multiply(BigInteger.valueOf((int) Math
								.pow(curNode + 1, i))));
			}
			nextPermutationsTable[curNode][preSequenceLength - 1] = permutations;

			// Calculate the other entries of the current row from right to left
			// using the righter entry of this row and the diagonal right entry
			// of the bottom row.
			for (int i = preSequenceLength - 2; i >= curNode - 1; i--) {
				nextPermutationsTable[curNode][i] = BigInteger
						.valueOf(curNode + 1)
						.multiply(nextPermutationsTable[curNode][i + 1])
						.add(nextPermutationsTable[curNode + 1][i + 1]);
			}
		}

		permutationsTable = nextPermutationsTable.clone();
	}

	/**
	 * Prefix for nodes. A node then is called 'prefix + index' where index is
	 * the index to a node in the node list.
	 */
	public static final String PREFIX_NODE = "q";
	/**
	 * Prefix for transitions. A transition then is called 'prefix + index'
	 * where index is the index to a transition in the transition list.
	 */
	public static final String PREFIX_TRANSITION = "a";
	/**
	 * Table that contains the amount of all permutations of different DFA
	 * classes. Dimensions are [size][size * alphabetSize]. Also used for
	 * caching purpose.
	 */
	
	private static BigInteger[][] permutationsTable;
	
	/**
	 * Random generator.
	 */
	private final Random m_Random;
	/**
	 * Resulting automaton of generator.
	 */
	private final NestedWordAutomaton<String, String> m_Result;

	/**
	 * Size of the automaton also amount of nodes.
	 */
	int m_size;
	/**
	 * Size of the alphabet.
	 */
	int m_alphabetSize;
	/**
	 * If transition function should be total or not.
	 * If not it can be possible that some transitions are missing
	 * and the DFA is a non-complete DFA.
	 */
	boolean m_isTotal;
	/**
	 * Number of the accepting states.
	 */
	int m_numOfAccStates;
	/**
	 * If true ensures a uniform distribution of the connected DFAs at high cost
	 * of performance for big 'size'. If false random classes of DFAs get
	 * favored over other random classes but the generation is very fast.
	 */
	boolean m_ensureIsUniform;
	/**
	 * If true enables caching of pre-calculated results for future similar
	 * requests. If false caching will not be done. Best results can be achieved
	 * by executing requests with same 'size' and similar 'alphabetSize' behind
	 * one another.
	 */
	boolean m_enableCaching;

	/**
	 * Generates a uniform distributed random connected or not-connected total
	 * or not-total DFA with a given amount of nodes,
	 * size of alphabet and number of accepting states.<br />
	 * <br />
	 * Additionally with following flags:<br />
	 * boolean <b>ensureIsUniform</b> : <b>true</b> Ensures a uniform
	 * distribution of the DFAs at high cost of performance for big 'size'.<br/>
	 * boolean <b>enableCaching</b> : <b>true</b> Enables caching of
	 * pre-calculated results for future similar requests.<br/>
	 * Best results can be achieved by executing requests with same 'size' and
	 * similar 'alphabetSize' behind one another.<br/><br/>
	 * Runtime is in:<br/>
	 * <b>O(n^2 * k) * O(random)</b> if there is a valid cache (n must be equals)<br/>
	 * <b>O(n^3 * k) * O(random)</b> if there is no valid cache<br/>
	 * where 'n' is the amount of nodes, 'k'
	 * the size of the alphabet and 'random' methods of {@link java.util.Random}.
	 * 
	 * @param size
	 *            Amount of nodes
	 * @param alphabetSize
	 *            Size of the alphabet
	 * @param numOfAccStates
	 *            Number of accepting states
	 * @param isTotal
	 *            If transition function should be total or not.
	 *            If not it can be possible that some transitions are missing
	 *            and the DFA is a non-complete DFA.
	 * @return Uniform distributed random total DFA
	 */
	public GetRandomDfa(int size, int alphabetSize, int numOfAccStates, boolean isTotal) {
		m_size = size;
		m_alphabetSize = alphabetSize;
		m_numOfAccStates = numOfAccStates;
		m_isTotal = isTotal;
		m_ensureIsUniform = true;
		m_enableCaching = true;

		m_Random = new Random();
		//If DFA should not be total simulate that
		//using a increased size where the new node is the sink state.
		int generationSize = m_size;
		if (!isTotal) {
			generationSize += 1;
		}
		m_Result = extractPackedDFA(
				generatePackedRandomDFA(generationSize, m_alphabetSize,
						m_numOfAccStates, m_ensureIsUniform, m_enableCaching),
				m_size, m_alphabetSize, m_numOfAccStates, m_isTotal, m_Random);
	}

	/**
	 * Generates a uniform or non-uniform distributed random connected or
	 * not-connected total or not-total DFA with a given
	 * amount of nodes, size of alphabet and number of accepting states.<br />
	 * <br />
	 * Additionally with following flags:<br />
	 * boolean <b>enableCaching</b> : <b>true</b> Enables caching of
	 * pre-calculated results for future similar requests.<br/>
	 * Best results can be achieved by executing requests with same 'size' and
	 * similar 'alphabetSize' behind one another.<br/><br/>
	 * Runtime is in:<br/>
	 * <b>O(n^2 * k) * O(random)</b> if result should be uniform and there
	 * is a valid cache (n must be equals)<br/>
	 * <b>O(n^3 * k) * O(random)</b> if result should be uniform and there is no valid cache<br/>
	 * <b>O(n * k) * O(random)</b> if result should not be uniform<br/>
	 * where 'n' is the amount of nodes, 'k'
	 * the size of the alphabet and 'random' methods of {@link java.util.Random}.
	 * 
	 * @param size
	 *            Amount of nodes
	 * @param alphabetSize
	 *            Size of the alphabet
	 * @param numOfAccStates
	 *            Number of accepting states
	 * @param isTotal
	 *            If transition function should be total or not.
	 *            If not it can be possible that some transitions are missing
	 *            and the DFA is a non-complete DFA.
	 * @param ensureIsUniform
	 *            If true ensures a uniform distribution of the connected DFAs
	 *            at high cost of performance for big 'size'. If false random
	 *            classes of DFAs get favored over other random classes but the
	 *            generation is very fast.
	 * @return Uniform or non-uniform distributed random DFA
	 */
	public GetRandomDfa(int size, int alphabetSize, int numOfAccStates, boolean isTotal,
			boolean ensureIsUniform) {
		m_size = size;
		m_alphabetSize = alphabetSize;
		m_numOfAccStates = numOfAccStates;
		m_isTotal = isTotal;
		m_ensureIsUniform = ensureIsUniform;
		m_enableCaching = true;

		m_Random = new Random();
		//If DFA should not be total simulate that
		//using a increased size where the new node is the sink state.
		int generationSize = m_size;
		if (!isTotal) {
			generationSize += 1;
		}
		m_Result = extractPackedDFA(
				generatePackedRandomDFA(generationSize, m_alphabetSize,
						m_numOfAccStates, m_ensureIsUniform, m_enableCaching),
				m_size, m_alphabetSize, m_numOfAccStates, m_isTotal, m_Random);
	}

	/**
	 * Generates a uniform or non-uniform distributed random connected or
	 * not-connected total or not-total DFA with a given
	 * amount of nodes and size of alphabet.<br/><br/>
	 * Runtime is in:<br/>
	 * <b>O(n^3 * k) * O(random)</b> if result should be uniform and caching is not enabled<br/>
	 * <b>O(n * k) * O(random)</b> if result should not be uniform<br/>
	 * <b>O(n^2 * k) * O(random)</b> if result should be uniform, caching is enabled and there
	 * is a valid cache (n must be equals)<br/>
	 * where 'n' is the amount of nodes, 'k'
	 * the size of the alphabet and 'random' methods of {@link java.util.Random}.
	 * 
	 * @param size
	 *            Amount of nodes
	 * @param alphabetSize
	 *            Size of the alphabet
	 * @param numOfAccStates
	 *            Number of accepting states
	 * @param isTotal
	 *            If transition function should be total or not.
	 *            If not it can be possible that some transitions are missing
	 *            and the DFA is a non-complete DFA.
	 * @param ensureIsUniform
	 *            If true ensures a uniform distribution of the connected DFAs
	 *            at high cost of performance for big 'size'. If false random
	 *            classes of DFAs get favored over other random classes but the
	 *            generation is very fast.
	 * @param enableCaching
	 *            If true enables caching of pre-calculated results for future
	 *            similar requests. If false caching will not be done. Best
	 *            results can be achieved by executing requests with same 'size'
	 *            and similar 'alphabetSize' behind one another.
	 * @return Uniform or non-uniform distributed random DFA
	 */
	public GetRandomDfa(int size, int alphabetSize, int numOfAccStates, boolean isTotal,
			boolean ensureIsUniform, boolean enableCaching) {
		m_size = size;
		m_alphabetSize = alphabetSize;
		m_numOfAccStates = numOfAccStates;
		m_isTotal = isTotal;
		m_ensureIsUniform = ensureIsUniform;
		m_enableCaching = enableCaching;

		m_Random = new Random();
		//If DFA should not be total simulate that
		//using a increased size where the new node is the sink state.
		int generationSize = m_size;
		if (!isTotal) {
			generationSize += 1;
		}
		m_Result = extractPackedDFA(
				generatePackedRandomDFA(generationSize, m_alphabetSize,
						m_numOfAccStates, m_ensureIsUniform, m_enableCaching),
				m_size, m_alphabetSize, m_numOfAccStates, m_isTotal, m_Random);
	}

	@Override
	public boolean checkResult(StateFactory<String> stateFactory)
			throws OperationCanceledException {
		return true;
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result "
				+ m_Result.sizeInformation() + ".";
	}

	@Override
	public NestedWordAutomaton<String, String> getResult() {
		return m_Result;
	}

	@Override
	public String operationName() {
		return "GetRandomDfa";
	}

	@Override
	public String startMessage() {
		return MessageFormat
				.format("Start {0}. Alphabet size {1} Number of states {2} "
						+ "Number of accepting states {3} Is total {4} Ensure is uniform {5} "
						+ "Is caching enabled {6}", operationName(),
						m_alphabetSize, m_size, m_numOfAccStates,
						m_isTotal, m_ensureIsUniform, m_enableCaching);
	}
}
