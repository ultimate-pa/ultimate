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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

/**
 * This class implements the incremental DFA minimization algorithm by Almeida,
 * Moreira, and Reis ('Incremental DFA minimisation').
 * 
 * The basic idea is to check equivalence of each pair of states exactly once
 * (with an order on the states even only once per two states, so
 * <code>q, q'</code> we either check as <code>(q, q')</code> or
 * <code>(q', q)</code>).
 * 
 * Initially each state is not equivalent to all states that have a different
 * final status (<code>q !~ q' <=> (q in F <=> q' not in F)</code>).
 * Also it is clear that each state is equivalent to itself.
 * 
 * If for a pair of states it is not clear whether they are equivalent, then
 * the they are equivalent if and only if all successor states (wrt. a symbol)
 * are equivalent, so we shift the task for one level. Loops are avoided by
 * storing the visited pairs.
 * 
 * If the result was finally found for a pair of states, typically some more
 * pairs of states were investigated. If the answer was positive, all pairs of
 * states that were tested are equivalent. If the answer was negative, some
 * pairs of states were not equivalent. All those pairs are stored and the
 * information is then propagated to avoid checking these states later.
 * 
 * @author Christian
 */
public class MinimizeDfaAmr<LETTER, STATE>
		extends AMinimizeIncremental<LETTER, STATE>
		implements IOperation<LETTER, STATE> {
	/**
	 * The result automaton.
	 */
	private final INestedWordAutomaton<LETTER, STATE> m_result;
	/**
	 * The number of states in the input automaton (often used).
	 */
	private final int m_size;
	/**
	 * The hash capacity for the number of pairs of states (often used).
	 */
	private final int m_hashCapNoTuples;
	/**
	 * Map state -> integer index.
	 */
	private final HashMap<STATE, Integer> m_state2int;
	/**
	 * Map integer index -> state.
	 */
	private final ArrayList<STATE> m_int2state;
	/**
	 * Background array for the Union-Find data structure.
	 */
	private final int[] m_unionFind;
	/**
	 * Potentially equivalent pairs of states.
	 */
	private final SetList m_equiv;
	/**
	 * History of calls to the transition function.
	 */
	private final SetList m_path;
	/**
	 * Set of pairs of states which are not equivalent.
	 */
	private final Set<Tuple> m_neq;
	/**
	 * Stack for explicit version of recursive procedure.
	 */
	private final ArrayDeque<StackElem> m_stack;
	
	// ----------------------- options for tweaking ----------------------- //
	
	/**
	 * Option:
	 * Separate states with different transitions.
	 * 
	 * That is, if there is a letter {@code l} where one of the states has
	 * an outgoing transitions with {@code l} and one has not (hence this
	 * transition would go to an implicit sink state.
	 * 
	 * NOTE: This is only reasonable if the input automaton is not total.
	 * Furthermore, the method becomes incomplete (i.e., may not find the
	 * minimum) if dead ends have not been removed beforehand.
	 */
	private final boolean m_optionNeqTrans = false;
	
	// --------------------------- class methods --------------------------- //
	
	/**
	 * GUI Constructor.
	 * 
	 * @param operand input automaton (DFA)
	 * @throws OperationCanceledException thrown when execution is cancelled
	 * @throws AutomataLibraryException thrown by DFA check
	 */
	public MinimizeDfaAmr(final IUltimateServiceProvider services,
			final StateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand)
			throws OperationCanceledException, AutomataLibraryException {
		this(services, stateFactory, operand, null);
	}
	
	/**
	 * Constructor.
	 * 
	 * @param operand input automaton (DFA)
	 * @param interrupt interrupt
	 * @throws OperationCanceledException thrown when execution is cancelled
	 * @throws AutomataLibraryException thrown by DFA check
	 */
	public MinimizeDfaAmr(final IUltimateServiceProvider services,
			final StateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final Interrupt interrupt)
			throws OperationCanceledException, AutomataLibraryException {
		super(services, stateFactory, "MinimizeAMR", operand, interrupt);
		
		assert super.checkForDfa() : "The input automaton is no DFA.";
		
		m_size = operand.size();
		assert (m_size >= 0) : "The automaton size must be nonnegative.";
		
		// trivial special cases
    	if (m_size <= 1) {
    		m_state2int = null;
    		m_int2state = null;
    		m_unionFind = null;
    		m_neq = null;
    		m_equiv = null;
    		m_path = null;
    		m_stack = null;
    		m_hashCapNoTuples = 0;
    		
    		m_result = m_operand;
    	}
    	else {
    		m_state2int = new HashMap<STATE, Integer>(m_size);
    		m_int2state = new ArrayList<STATE>(m_size);
    		m_unionFind = new int[m_size];
    		
    		/*
    		 * The maximum number of pairs of states without considering the
    		 * order is (n^2 - n)/2.
    		 * 
    		 * This can easily be more than the maximum integer number.
    		 * In that case the constant is set to this bound.
    		 */
    		int possibleOverflow = (m_size * (m_size - 1)) / 2;
    		if (possibleOverflow > 0) {
    			possibleOverflow = computeHashCap(possibleOverflow);
    			if (possibleOverflow > 0) {
    				m_hashCapNoTuples = possibleOverflow;
    			}
    			else {
    				m_hashCapNoTuples = Integer.MAX_VALUE;
    			}
    		}
    		else {
    			m_hashCapNoTuples = Integer.MAX_VALUE;
    		}
    		
    		m_neq = new HashSet<Tuple>(m_hashCapNoTuples);
    		m_equiv = new SetList();
    		m_path = new SetList();
    		m_stack = new ArrayDeque<StackElem>();
    		
			m_result = minimize();
		}
		s_logger.info(exitMessage());
	}
	
	/**
	 * This method invokes the minimization process.
	 * 
	 * @return the minimal DFA
	 * @throws OperationCanceledException thrown when execution is cancelled
	 */
	private INestedWordAutomaton<LETTER, STATE> minimize()
			throws OperationCanceledException {
		// initialize data structures
		preprocess();
		
		// try minimization as long as possible
		findEquiv();
		
		// construct result
		return constructResult();
	}
	
	/**
	 * This method makes the preprocessing step to map states to integers and
	 * vice versa.
	 */
	private void preprocess() {
		int i = -1;
		for (final STATE state : m_operand.getStates()) {
			m_int2state.add(state);
			
			assert (m_state2int.get(state) == null) :
				"The state is already in the map.";
			m_state2int.put(state, ++i);
		}
		
		assert ((m_state2int.size() == m_int2state.size()) &&
				(m_state2int.size() == m_size)) :
					"The mappings do not have the same size as the input "
					+ "automaton";
	}
	
	/**
	 * This method is the main method of the minimization. As long as it runs,
	 * it finds for each pair of states whether they are equivalent or not.
	 * 
	 * It terminates automatically, but can also be halted at any time.
	 * 
	 * pseudocode name: MIN-INCR
	 */
	private void findEquiv() {
		// initialization
		initializeUnionFind();
		intializeTupleSet();
		
		// refinement loop
		for (int p = 0; p < m_size; ++p) {
			for (int q = p + 1; q < m_size; ++q) {
				// termination signal found
				if ((m_interrupt != null) && (m_interrupt.getStatus())) {
					return;
				}
				
				final Tuple tuple = new Tuple(p, q);
				
				// tuple was already found to be not equivalent
				if (m_neq.contains(tuple)) {
					continue;
				}
				
				// states have the same representative
				if (find(p) == find(q)) {
					continue;
				}
				
				// clean global sets
				m_equiv.clean();
				m_path.clean();
				
				// find out whether the states are equivalent or not
				final Iterator<Tuple> it;
				// the states are equivalent
				if (isPairEquiv(tuple)) {
					it = m_equiv.iterator();
					while (it.hasNext()) {
						union(it.next());
					}
				}
				// the states are not equivalent
				else {
					it = m_path.iterator();
					while (it.hasNext()) {
						m_neq.add(it.next());
					}
				}
			}
		}
	}
	
	/**
	 * This method initializes the set of pairs of states which are definitely
	 * not equivalent.
	 * 
	 * The certain candidates are pairs where exactly one state is final.
	 * 
	 * There is a global option for separating states with different outgoing
	 * transitions.
	 * 
	 * @return set of pairs of states not equivalent to each other
	 */
	private void intializeTupleSet() {
		// insert all pairs of states where one is final and one is not
		// TODO this is naive, think about a faster implementation
		for (int i = 0; i < m_size; ++i) {
			final STATE state1 = m_int2state.get(i);
			final boolean isFirstFinal = m_operand.isFinal(state1);
			
			for (int j = i + 1; j < m_size; ++j) {
				final STATE state2 = m_int2state.get(j);
				if (m_operand.isFinal(state2) ^ isFirstFinal) {
					m_neq.add(new Tuple(i, j));
				}
				/*
				 * optional separation of states with different outgoing
				 * transitions
				 */
				else if (m_optionNeqTrans) {
					final HashSet<LETTER> letters = new HashSet<LETTER>();
					for (final OutgoingInternalTransition<LETTER, STATE> out :
							m_operand.internalSuccessors(state1)) {
						letters.add(out.getLetter());
					}
					boolean broken = false;
					for (final OutgoingInternalTransition<LETTER, STATE> out :
    						m_operand.internalSuccessors(state2)) {
						if (! letters.remove(out.getLetter())) {
							m_neq.add(new Tuple(i, j));
							broken = true;
							break;
						}
					}
					if (! (broken || letters.isEmpty())) {
						m_neq.add(new Tuple(i, j));
					}
				}
			}
		}
	}
	
	/**
	 * This method originally recursively calls itself to find out whether two
	 * states are equivalent. It uses the global set lists to store the paths
	 * it searched through.
	 * 
	 * The recursion was transformed to an explicit form using a stack.
	 * 
	 * 
	 * 
	 * pseudocode name: EQUIV-P
	 * 
	 * @param origTuple tuple to check equivalence of
	 * @return true iff the pair of states is equivalent
	 */
	private boolean isPairEquiv(Tuple origTuple) {
		assert (m_stack.size() == 0) : "The stack must be empty.";
		m_stack.add(new StackElem(origTuple));
		
		// NOTE: This line was moved here for faster termination.
		m_equiv.add(origTuple);
		
		assert (! m_stack.isEmpty()) : "The stack must not be empty.";
		do {
			final StackElem elem = m_stack.peekLast();
			final Tuple eTuple = elem.m_tuple;
			
			// already expanded: end of (explicit) recursion
			if (elem.m_expanded) {
				// take element from stack
				m_stack.pollLast();
				
				// all successors and hence also this pair of states equivalent
				m_path.remove(eTuple);
				continue;
			}
			// not yet expanded: continue (explicit) recursion
			else {
				elem.m_expanded = true;
				
				// tuple was already found to be not equivalent
				if (m_neq.contains(eTuple)) {
					m_stack.clear();
					return false;
				}
				
				/*
				 * tuple was already visited on the path, so the states are
				 * equivalent
				 */
				if (m_path.contains(eTuple)) {
					continue;
				}
				
				m_path.add(eTuple);
				
				if (! putSuccOnStack(eTuple)) {
					// one transition is only possible from one state
					m_stack.clear();
					return false;
				}
			}
		} while (! m_stack.isEmpty());
		
		// no witness was found why the states should not be equivalent
		// m_equiv.add(origTuple); // NOTE: This line was moved upwards.
		return true;
	}
	
	/**
	 * This method handles the case of {@link isPairEquiv(Tuple origTuple)}
	 * when the pair of states has not yet been expanded.
	 * 
	 * It pushes the pairs of successor states on the stack.
	 * 
	 * If the states have not been separated wrt. different outgoing
	 * transitions at the beginning, this is checked here and then possibly a
	 * reason for non-equivalence is found.
	 * 
	 * @param tuple pair of states
	 * @return true iff no reason for non-equivalence was found
	 */
	private boolean putSuccOnStack(final Tuple tuple) {
		final STATE firstState = m_int2state.get(tuple.m_first);
		final STATE secondState = m_int2state.get(tuple.m_second);
		
		/*
		 * NOTE: This could be problematic with nondeterministic automata.
		 */
		for (final OutgoingInternalTransition<LETTER, STATE> out :
				m_operand.internalSuccessors(firstState)) {
			final LETTER letter = out.getLetter();
			assert (m_operand.internalSuccessors(secondState,
					letter) != null);
			
			int succP = find(m_state2int.get(out.getSucc()));
			int succQ;
			
			if (m_optionNeqTrans) {
				assert (m_operand.internalSuccessors(secondState,
							letter).iterator().hasNext()) :
					"States with different outgoing transitions " +
					"should have been marked as not equivalent.";
				
				succQ = find(m_state2int.get(m_operand.internalSuccessors(
						secondState, letter).iterator().next().getSucc()));
			}
			else {
				final Iterator<OutgoingInternalTransition<LETTER, STATE>> out2
						= m_operand.internalSuccessors(
								secondState, letter).iterator();
				if (out2.hasNext()) {
					succQ = find(m_state2int.get(out2.next().getSucc()));
				}
				else {
					return false;
				}
			}
			
			if (succP != succQ) {
				if (succP > succQ) {
					final int tmp = succP;
					succP = succQ;
					succQ = tmp;
				}
				final Tuple successorTuple = new Tuple(succP, succQ);
				
				if (! m_equiv.contains(successorTuple)) {
					m_equiv.add(successorTuple);
					
					// break recursion: add to stack
					m_stack.add(new StackElem(successorTuple));
				}
			}
		}
		
		if (! m_optionNeqTrans) {
			for (final OutgoingInternalTransition<LETTER, STATE> out :
				m_operand.internalSuccessors(secondState)) {
				if (! m_operand.internalSuccessors(
						firstState, out.getLetter()).iterator().hasNext()) {
					return false;
				}
			}
		}
		
		return true;
	}
	
	/**
	 * This method constructs the resulting automaton from the set of
	 * equivalent states.
	 * 
	 * @return resulting automaton where equivalent states are merged
	 */
	private INestedWordAutomaton<LETTER, STATE> constructResult() {
		// mapping from states to their representative
		final HashMap<Integer, ? extends Collection<STATE>> state2equivStates =
				computeMapState2Equiv();
		
		// construct result
		final StateFactory<STATE> stateFactory = m_operand.getStateFactory();
		NestedWordAutomaton<LETTER, STATE> result =
				new NestedWordAutomaton<LETTER, STATE>(
						m_Services, 
						m_operand.getInternalAlphabet(),
						m_operand.getCallAlphabet(),
						m_operand.getReturnAlphabet(),
						stateFactory);
		
		// mapping from old state to new state
		final HashMap<Integer, STATE> oldState2newState =
				new HashMap<Integer, STATE>(
						computeHashCap(state2equivStates.size()));
		
		// add states
		assert (m_operand.getInitialStates().iterator().hasNext()) :
			"There is no initial state in the automaton.";
		final int initRepresentative = find(m_state2int.get(
				m_operand.getInitialStates().iterator().next()));
		for (final Entry<Integer, ? extends Collection<STATE>> entry :
				state2equivStates.entrySet()) {
			final int representative = entry.getKey();
			final Collection<STATE> equivStates = entry.getValue();
			
			final STATE newSTate = stateFactory.minimize(equivStates);
			oldState2newState.put(representative, newSTate);
			
			assert (equivStates.iterator().hasNext()) :
				"There is no equivalent state in the collection.";
			result.addState((representative == initRepresentative),
					m_operand.isFinal(equivStates.iterator().next()),
					newSTate);
		}
		
		/*
		 * add transitions
		 * 
		 * NOTE: This exploits the fact that the input is deterministic.
		 */
		for (final Integer oldStateInt : state2equivStates.keySet()) {
			for (final OutgoingInternalTransition<LETTER, STATE> out :
					m_operand.internalSuccessors(
							m_int2state.get(oldStateInt))) {
				result.addInternalTransition(
						oldState2newState.get(oldStateInt),
						out.getLetter(),
						oldState2newState.get(
								find(m_state2int.get(out.getSucc()))));
			}
		}
		
		return result;
	}
	
	/**
	 * This method computes a mapping from old states to new representatives.
	 * 
	 * @return map old state -> new state
	 */
	private HashMap<Integer, ? extends Collection<STATE>>
			computeMapState2Equiv() {
		final HashMap<Integer, LinkedList<STATE>> state2equivStates =
				new HashMap<Integer, LinkedList<STATE>>(
						computeHashCap(m_size));
        for (int i = m_size - 1; i >= 0; --i) {
        	final int representative = find(i);
        	LinkedList<STATE> equivStates =
        			state2equivStates.get(representative);
        	if (equivStates == null) {
        		equivStates = new LinkedList<STATE>();
        		state2equivStates.put(representative, equivStates);
        	}
        	equivStates.add(m_int2state.get(i));
        }
		return state2equivStates;
	}
	
	@Override
	public INestedWordAutomatonSimple<LETTER, STATE> getResult() {
		return m_result;
	}
	
	// --------------------- Union-Find data structure --------------------- //
	
	/**
	 * This method initializes the Union-Find data structure.
	 * 
	 * That is, each state points to itself.
	 * 
	 * pseudocode name: MAKE in for-loop
	 */
	private void initializeUnionFind() {
		for (int i = m_unionFind.length - 1; i >= 0; --i) {
			m_unionFind[i] = i;
		}
	}
	
	/**
	 * This method implements the find operation of the Union-Find data
	 * structure.
	 * 
	 * That is, the representative chain is searched and afterwards all
	 * intermediate representatives in this chain are updated accordingly
	 * for faster future find operations.
	 * 
	 * pseudocode name: FIND
	 * 
	 * @param oldRepresentative state
	 * @return representative of the given state
	 */
	private int find(int oldRepresentative) {
		LinkedList<Integer> path = new LinkedList<Integer>();
		
		while (true) {
			int newRepresentative = m_unionFind[oldRepresentative];
			
			// found the representative
			if (oldRepresentative == newRepresentative) {
				// update representative on the path
				for (final int i : path) {
					m_unionFind[i] = newRepresentative;
				}
				
				return newRepresentative;
			}
			else {
				path.add(oldRepresentative);
				oldRepresentative = newRepresentative;
			}
		}
	}
	
	/**
	 * This method implements the union operation of the Union-Find data
	 * structure.
	 * 
	 * That is, the representative of the second state is set to the
	 * representative of the first state.
	 * 
	 * NOTE: The find operation is used in order to safe one update later on.
	 *       This way the direct representatives are certainly the true
	 *       representatives.
	 * 
	 * pseudocode name: UNION
	 * 
	 * @param tuple pair of states that shall be united  
	 */
	private void union(final Tuple tuple) {
		m_unionFind[find(tuple.m_second)] = find(tuple.m_first);
	}
	
	// ------------------- auxiliary classes and methods ------------------- //
	
	/**
	 * A tuple class for integers.
	 */
	private final class Tuple {
		/**
		 * The first integer.
		 */
		final int m_first;
		/**
		 * The second integer.
		 */
		final int m_second;
		
		/**
		 * Constructor.
		 * 
		 * @param first first state
		 * @param second second state
		 */
		public Tuple(final int first, final int second) {
			assert (first < second) : "The first entry must be the smaller one";
			m_first = first;
			m_second = second;
		}
		
		// TODO: What is a good hash function?
		public int hashCode() {
			return m_first + 17 * m_second;
		}
		
		@SuppressWarnings("unchecked")
		@Override
		public boolean equals(Object other) {
			if (! (other instanceof MinimizeDfaAmr.Tuple)) {
				return false;
			}
			final Tuple o = (Tuple)other;
			return (o.m_first == this.m_first) && (o.m_second == this.m_second);
		}
		
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			builder.append("(");
			builder.append(m_first);
			builder.append(", ");
			builder.append(m_second);
			builder.append(")");
			return builder.toString();
		}
	}
	
	/**
	 * This is a data structure containing a map and a list for fast operations
	 * on the data (tuples, i.e., pairs of states).
	 * 
	 * The map holds pairs(tuple, list node), i.e., it maps a pair of states to
	 * the list node containing it. For iteration the list is used.
	 * 
	 * Insertion and removal both work in {@code O(1)}. The problem here is
	 * that hash maps must be initialized and this takes time {@code O(size)}.
	 * Since {@code size} is in {@code O(n^2)} throughout the execution and the
	 * sets are repeatedly recreated, this comes with a big cost.
	 *   
	 * To avoid this, the map is instead cleaned for all entries, which might
	 * hopefully be much less than all possible entries.
	 */
	private final class SetList {
		/**
		 * Map from state to list node.
		 */
		HashMap<Tuple, ListNode> m_map;
		/**
		 * Doubly-linked list of states.
		 */
		DoublyLinkedList m_list;
		/**
		 * Flag that determines whether the map and list have been initialized.
		 */
		boolean m_isInitialized;
		
		/**
		 * Constructor.
		 */
		public SetList() {
			m_isInitialized = false;
		}
		
		/**
		 * This method adds a pair of states.
		 * 
		 * NOTE: The original pseudocode allows elements to be present
		 * beforehand and removes them first. That is avoided by this
		 * implementation.
    	 * 
    	 * pseudocode name: SET-INSERT
		 * 
		 * @param tuple pair of states
		 */
		void add(final Tuple tuple) {
			assert (! m_map.containsKey(tuple)) :
				"Elements should not be contained twice.";
			
			// insert new pair of states
			m_map.put(tuple, m_list.add(tuple));
		}
		
		/**
		 * This method removes a pair of states.
		 * 
		 * NOTE: The original pseudocode allows elements to not be present
		 * beforehand. That is avoided by this implementation.
    	 * 
    	 * pseudocode name: SET-REMOVE
		 * 
		 * @param tuple pair of states
		 */
		void remove(final Tuple tuple) {
			assert (m_map.containsKey(tuple)) :
				"Only elements contained should be removed.";
			
			// remove pair of states
			m_list.remove(m_map.remove(tuple));
		}
		
		/**
		 * This method checks containment of a pair of states.
    	 * 
    	 * pseudocode name: SET-SEARCH
		 * 
		 * @param tuple pair of states
		 * @return true iff pair of states is contained
		 */
		boolean contains(final Tuple tuple) {
			return m_map.containsKey(tuple);
		}
		
		/**
		 * This method returns an iterator of all contained elements.
    	 * 
    	 * pseudocode name: SET-ELEMENTS
		 * 
		 * @return iterator
		 */
		Iterator<Tuple> iterator() {
			return m_list.iterator(m_map.size());
		}
		
		/**
		 * To avoid re-allocation of the whole memory (and default
		 * initialization), the map is instead cleaned for all entries in the
		 * list.
    	 * 
    	 * pseudocode name: SET-MAKE
		 */
		void clean() {
			if (m_isInitialized) {
				final Iterator<Tuple> it = m_list.iterator(m_map.size());
				while (it.hasNext()) {
					final Tuple t = it.next();
					assert (m_map.containsKey(t)) :
						"The element was not in the map: " + t.toString();
					m_map.remove(t);
				}
				assert (m_map.size() == 0) :
					"There are elements left in the map after cleaning.";
			}
			else {
				m_isInitialized = true;
				m_map = new HashMap<Tuple, ListNode>(m_hashCapNoTuples);
			}
			m_list = new DoublyLinkedList();
		}
		
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			builder.append("(");
			builder.append(m_map);
			builder.append(", ");
			builder.append(m_list);
			builder.append(", ");
			builder.append(m_isInitialized);
			builder.append(")");
			return builder.toString();
		}
		
		/**
		 * This class represents a list node for the {@link DoublyLinkedList}.
		 */
		private final class ListNode {
			/**
			 * The contained pair of states.
			 */
			final Tuple m_tuple;
			/**
			 * Next list node.
			 */
			ListNode m_next;
			/**
			 * Previous list node.
			 */
			ListNode m_prev;
			
			/**
			 * Constructor.
			 * 
			 * @param tuple pair of states
			 */
			public ListNode(final Tuple tuple, final ListNode prev,
					final ListNode next) {
				m_tuple = tuple;
				m_prev = prev;
				m_next = next;
			}
			
			@Override
			public String toString() {
				return m_tuple.toString();
			}
		}
		
		/**
		 * This class implements a simple doubly-linked list where the list
		 * nodes can be accessed. This is used to store them in a hash map for
		 * fast access.
		 */
		private final class DoublyLinkedList {
			/**
			 * First list node.
			 */
			ListNode m_first;
			/**
			 * Last list node.
			 */
			ListNode m_last;
			
			/**
			 * Constructor.
			 */
			public DoublyLinkedList() {
				m_first = null;
				m_last = null;
			}
			
			/**
			 * This method adds a new pair of states to the end of the list in
			 * {@code O(1)}.
			 * 
			 * @param tuple pair of states
			 * @return the new list node
			 */
			ListNode add(final Tuple tuple) {
				assert (tuple != null) :
					"null should not be inserted in the list.";
				
				// first node
				if (m_last == null) {
					assert (m_first == null) :
						"The last list element is null unexpectedly.";
					
					m_first = new ListNode(tuple, null, null);
					m_first.m_prev = m_first;
					m_first.m_next = m_first;
					m_last = m_first;
				}
				// further node
				else {
					assert (m_first != null) :
						"The first list element is null unexpectedly.";
					
					final ListNode prev = m_last;
					m_last = new ListNode(tuple, prev, m_first);
					prev.m_next = m_last;
					m_first.m_prev = m_last;
				}
				
				// return new node
				return m_last;
			}
			
			/**
			 * This method removes a given list node in {@code O(1)}.
			 * 
			 * @param listNode
			 */
			void remove(final ListNode listNode) {
				assert (listNode != null) :
					"null cannot not be removed from the list.";
				
				// only node
				if (listNode.m_next == listNode) {
					m_first = null;
					m_last = null;
				}
				// further node
				else {
    				final ListNode prev = listNode.m_prev;
    				final ListNode next = listNode.m_next;
    				prev.m_next = next;
    				next.m_prev = prev;
    				
    				if (listNode == m_first) {
    					m_first = next;
    					
    					assert (listNode != m_last) :
    						"The node must not be first and last element.";
    				}
    				else if (listNode == m_last) {
    					m_last = prev;
    				}
				}
			}
			
			/**
			 * This method returns an iterator of the list elements.
			 * 
			 * NOTE: It is assumed that the list is not modified during
			 *       iteration.
			 * 
			 * @param size the size of the list (known by the set)
			 * @return iterator of list elements
			 */
			Iterator<Tuple> iterator(final int size) {
				return new Iterator<Tuple>() {
					/**
					 * Number of elements.
					 */
					int m_itSize = size;
					/**
					 * Next element.
					 */
					ListNode m_itNext = m_last;
					
					@Override
					public boolean hasNext() {
						return (m_itSize > 0);
					}

					@Override
					public Tuple next() {
						assert (m_itSize > 0) :
							"The next method must not be called when finished.";
						--m_itSize;
						assert (m_itNext != null) :
							"An empty list should not be asked for the next " +
								"element.";
						m_itNext = m_itNext.m_next;
						assert (m_itNext != null) :
							"An empty list should not be asked for the next " +
								"element.";
						return m_itNext.m_tuple;
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException(
								"Removal is not supported.");
					}
				};
			}
			
			@Override
			public String toString() {
				final StringBuilder builder = new StringBuilder();
				builder.append("{");
				if (m_first != null) {
					builder.append(m_first.toString());
    				ListNode node = m_first.m_next;
    				while (node != m_first) {
        				builder.append(", ");
        				builder.append(node.toString());
        				node = node.m_next;
    				}
				}
				builder.append("}");
				return builder.toString();
			}
		}
	}
	
	/**
	 * This class represents an auxiliary wrapper for stack elements.
	 * An instance contains both a pair of states and a flag indicating whether
	 * this pair has already been investigated or not.
	 * The stack is used is to give an explicit version of the recursive
	 * procedure in the equivalence checking algorithm.
	 */
	private class StackElem {
		/**
		 * Pair of states.
		 */
		final Tuple m_tuple;
		/**
		 * True iff already visited.
		 */
		boolean m_expanded;
		
		/**
		 * Constructor.
		 * 
		 * @param tuple pair of states
		 */
		public StackElem(Tuple tuple) {
			m_tuple = tuple;
			m_expanded = false;
		}
		
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			builder.append("(");
			builder.append(m_tuple);
			builder.append(", ");
			builder.append(m_expanded);
			builder.append(")");
			return builder.toString();
		}
	}
}
