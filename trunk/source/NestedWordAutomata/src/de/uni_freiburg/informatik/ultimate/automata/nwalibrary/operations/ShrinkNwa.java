package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.PriorityQueue;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

/**
 * TODO list:
 * 
 * ask Matthias:
 * <noReduction> return old automaton when no reduction occurred?
 * 
 * <trivialCases> finals.size() = 0 => empty automaton
 *                nonfinals.size() = 0 => possibly MR(Sigma)*, easy to check
 * 
 * <Matthias'Stuff> m_stateFactoryConstruction
 *                   mapping for Hoare annotation
 * 
 * <DoubleDecker> check this?
 * 
 * <splittingPolicy> currently all internal and call splits consider the
 *                   same splitter set
 *                   this could be improved by stopping the split whenever the
 *                   splitter set itself is split
 *                   but this somehow counters the automata implementation,
 *                   since finding the predecessors is expensive...
 *                   for return splits this is already the case
 * 
 * <splitOutgoing> possible improvement: at the beginning split all states
 *                 with respect to outgoing symbols -> necessary condition
 * 
 * <constructAutomaton> how to do this efficiently in the end?
 * 
 * <TIEBREAK> what to do with states that do not need to be split?
 * 
 * <returnSplit> prefer or defer splitter set A?
 * 
 * 
 * misc:
 * <hashCode> overwrite for EquivalenceClass?
 * 
 * <finalize> remove all unnecessary objects in the end
 */

/**
 * This class minimizes nested word automata.
 * 
 * It is based on Hopcroft's minimization for deterministic finite automata.
 * 
 * Basically we do an over-approximation of the language by merging all states.
 * Then iteratively the so-called equivalence classes are split until no more
 * witness for a split is found.
 * 
 * For DFAs the algorithm just performs Hopcroft's algorithm.
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 */
public class ShrinkNwa<LETTER, STATE> implements IOperation<LETTER, STATE> {
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	// old automaton
	private INestedWordAutomaton<LETTER, STATE> m_operand;
	private IDoubleDeckerAutomaton<LETTER, STATE> m_doubleDecker;
	// partition object
	private Partition m_partition;
	// work lists
	private WorkListIntCall m_workListIntCall;
	private WorkListRet m_workListRet;
	// simulates the output automaton
	private ShrinkNwaResult m_result;
	
	// TODO<debug>
	private final boolean DEBUG = false;
	
	/**
	 * StateFactory used for the construction of new states. This is _NOT_ the
	 * state factory relayed to the new automaton.
	 * Necessary because the Automizer needs a special StateFactory during
	 * abstraction refinement (for computation of HoareAnnotation).
	 */
//	private final StateFactory<STATE> m_stateFactoryConstruction;
	
	/**
	 * creates a copy of operand
	 * 
	 * @param operand preprocessed nested word automaton
	 * preprocessing: dead end and unreachable states/transitions removed
	 * @throws OperationCanceledException if cancel signal is received
	 */
	public ShrinkNwa(final INestedWordAutomaton<LETTER,STATE> operand)
			throws OperationCanceledException {
		this(operand, null, operand.getStateFactory(), false);
	}
	
	/**
	 * creates a copy of operand with an initial partition
	 * 
	 * minimization technique for deterministic finite automata by Hopcroft
	 * (http://en.wikipedia.org/wiki/DFA_minimization)
	 * 
	 * @param operand preprocessed nested word automaton
	 * preprocessing: dead end and unreachable states/transitions removed
	 * @param equivalenceClasses represent initial equivalence classes
	 * @param stateFactoryConstruction used for Hoare annotation
	 * @param isFiniteAutomaton true iff automaton is a finite automaton
	 * @throws OperationCanceledException if cancel signal is received
	 */
	@SuppressWarnings("unchecked")
	public ShrinkNwa(
			final INestedWordAutomaton<LETTER,STATE> operand,
			final Collection<Set<STATE>> equivalenceClasses,
			final StateFactory<STATE> stateFactoryConstruction,
			final boolean isFiniteAutomaton)
					throws OperationCanceledException {
		m_operand = operand;
		// TODO<DoubleDecker> check this?
		m_doubleDecker = (IDoubleDeckerAutomaton<LETTER, STATE>)m_operand;
//		m_stateFactoryConstruction = stateFactoryConstruction;
		m_partition = new Partition();
		m_workListIntCall = new WorkListIntCall();
		m_workListRet = new WorkListRet();
		
		// must be the last part of the constructor
		s_Logger.info(startMessage());
		minimize(isFiniteAutomaton, equivalenceClasses);
		s_Logger.info(exitMessage());
	}
	
	// --- [start] main methods --- //
	
	/**
	 * This is the main method that merges states not distinguishable
	 * (based on Hopcroft's algorithm).
	 * 
	 * @param isFiniteAutomaton true iff automaton is a finite automaton
	 * @param modules predefined modules that must be split
	 * @throws OperationCanceledException if cancel signal is received
	 */
	private void minimize(final boolean isFiniteAutomaton,
			final Iterable<Set<STATE>> modules)
			throws OperationCanceledException {
		if (DEBUG)
			System.err.println("---------------START---------------");
		// initialize the partition object
		initialize(modules);
		
		final InternalTransitionIterator internalIterator =
				new InternalTransitionIterator();
		
		// for DFAs only the internal split is both necessary and sufficient
		if (isFiniteAutomaton) {
			// iterative refinement
			while (m_workListIntCall.hasNext()) {
				// cancel if signal is received
				if (! UltimateServices.getInstance().continueProcessing()) {
					throw new OperationCanceledException();
				}
				
				EquivalenceClass a = m_workListIntCall.next();
				
				// internal split
				splitInternalOrCallPredecessors(a, internalIterator);
			}
		}
		// more complicated splitting 
		else {
			final CallTransitionIterator callIterator =
					new CallTransitionIterator();
			
			// iterative refinement
			outer: while (true) {
				// cancel if signal is received
				if (! UltimateServices.getInstance().continueProcessing()) {
					throw new OperationCanceledException();
				}
				
				// internals and calls
				while (m_workListIntCall.hasNext()) {
					// cancel if signal is received
					if (! UltimateServices.getInstance().continueProcessing())
							{
						throw new OperationCanceledException();
					}
					
					EquivalenceClass a = m_workListIntCall.next();
					
					// internal split
					if (DEBUG)
						System.out.println("\n-- internal search");
					splitInternalOrCallPredecessors(a, internalIterator);
					
					// call split
					if (DEBUG)
						System.out.println("\n-- call search");
					splitInternalOrCallPredecessors(a, callIterator);
				}
				
				// return predecessors
				if (m_workListRet.hasNext()) {
					if (DEBUG)
						System.out.println("\n-- detailed return search");
					EquivalenceClass a = m_workListRet.next();
					
					splitReturnPredecessors(a);
				}
				else {
					break outer;
				}
			}
			
			// automaton construction
			constructAutomaton();
		}
		if (DEBUG)
			System.err.println("----------------END----------------");
	}
	
	/**
	 * The partition object is initialized.
	 * Final states are separated from non-final states.
	 * For the passed modules this is assumed.
	 * 
	 * @param modules modules that must be split
	 */
	private void initialize(Iterable<Set<STATE>> modules) {
		// split final from non-final states
		if (modules == null) {
			final HashSet<STATE> finals = new HashSet<STATE>();
			final HashSet<STATE> nonfinals = new HashSet<STATE>();
			
			for (STATE state : m_operand.getStates()) {
				if (m_operand.isFinal(state)) {
					finals.add(state);
				}
				else {
					nonfinals.add(state);
				}
			}
			
			/*
			 * TODO<trivialCases>
			 * finals.size() = 0 => empty automaton
			 * 
			 * nonfinals.size() = 0 => possibly MR(Sigma)*, easy to check:
			 * all states must have all internal and call symbols outgoing
			 * all states must have all down states as return edges outgoing
			 * 
			 * also possible with modules?
			 */
			if (finals.size() > 0) {
				m_partition.addEc(finals);
			}
			if (nonfinals.size() > 0) {
				m_partition.addEc(nonfinals);
			}
		}
		// predefined modules are already split with respect to final states 
		else {
			for (Set<STATE> module : modules) {
				m_partition.addEc(module);
			}
		}
	}
	
	/**
	 * For each state and internal or call symbol respectively do the usual
	 * Hopcroft backwards split.
	 * 
	 * First all predecessor sets (with respect to a single symbol) are found
	 * and then for each such set the states are split from their equivalence
	 * classes.
	 * 
	 * @param a the splitter equivalence class
	 * @param iterator the iterator abstracting from the letter type
	 */
	private void splitInternalOrCallPredecessors(final EquivalenceClass a,
			final ITransitionIterator<LETTER, STATE> iterator) {
		// create a hash map from letter to respective predecessor states
		final HashMap<LETTER, HashSet<STATE>> letter2states =
				new HashMap<LETTER, HashSet<STATE>>();
		for (final STATE state : a.m_states) {
			iterator.nextState(state);
			while (iterator.hasNext()) {
				final LETTER letter = iterator.nextAndLetter();
				HashSet<STATE> predecessorSet =
						letter2states.get(letter);
				if (predecessorSet == null) {
					predecessorSet = new HashSet<STATE>();
					letter2states.put(letter, predecessorSet);
				}
				predecessorSet.add(iterator.getPred());
			}
		}
		
		// split each map value (set of predecessor states)
		for (final HashSet<STATE> predecessorSet : letter2states.values()) {
			assert (! predecessorSet.isEmpty());
			m_partition.splitEquivalenceClasses(predecessorSet);
		}
	}
	
	/**
	 * For each state and return symbol split the linear predecessors
	 * with respect to the successor equivalence classes.
	 * 
	 * To avoid concurrent modifications of the iterator, the method is stopped
	 * here whenever the splitter set itself was split. This could be avoided
	 * by storing the states, but the method will be called with the new
	 * splitter set anyway, so this is not considered necessary.
	 * 
	 * @param a splitter equivalence class
	 */
	private void splitReturnPredecessors(final EquivalenceClass a) {
		// recognize when the splitter set was split itself
		assert (! a.m_isInWorkListIntCall);
		
		// collect incoming return transitions
		HashMap<LETTER, HashSet<STATE>> letter2lin =
				new HashMap<LETTER, HashSet<STATE>>();
		for (final STATE succ : a.m_states) {
			for (final IncomingReturnTransition<LETTER, STATE> edge :
					m_operand.returnPredecessors(succ)) {
				final LETTER letter = edge.getLetter();
				HashSet<STATE> lins = letter2lin.get(letter);
				if (lins == null) {
					lins = new HashSet<STATE>();
					letter2lin.put(letter, lins);
				}
				lins.add(edge.getLinPred());
			}
		}
		
		/*
		 * Find the predecessor equivalence classes.
		 * Since the equivalence classes can be split, create immutable data
		 * structures here.
		 * 
		 * TODO<returnSplit> prefer or defer splitter set A?
		 */
		final HashMap<LETTER, LinkedList<ArrayList<STATE>>> letter2linList =
				new HashMap<LETTER, LinkedList<ArrayList<STATE>>>();
		HashMap<EquivalenceClass, ArrayList<STATE>> ec2list =
				new HashMap<EquivalenceClass, ArrayList<STATE>>();
		for (final Entry<LETTER, HashSet<STATE>> entry :
				letter2lin.entrySet()) {
			final LETTER letter = entry.getKey();
			final LinkedList<ArrayList<STATE>> linList =
					new LinkedList<ArrayList<STATE>>();
			letter2linList.put(letter, linList);
			
			final HashSet<EquivalenceClass> ecs =
					new HashSet<EquivalenceClass>();
			
			for (final STATE lin : entry.getValue()) {
				final EquivalenceClass ec =
						m_partition.m_state2EquivalenceClass.get(lin);
				if (ecs.add(ec)) {
					ArrayList<STATE> ecList = ec2list.get(ec);
					if (ecList == null) {
						ecList = new ArrayList<STATE>(ec.m_states.size());
						ecList.addAll(ec.m_states);
						ec2list.put(ec, ecList);
					}
					linList.add(ecList);
				}
			}
		}
		// delete temporary mapping
		ec2list = null;
		letter2lin = null;
		
		// splits
		for (final Entry<LETTER, LinkedList<ArrayList<STATE>>> entry :
				letter2linList.entrySet()) {
			final LETTER letter = entry.getKey();
			for (final ArrayList<STATE> lins : entry.getValue()) {
				// split linear predecessors
				splitLinPred(lins, a, letter);
				
				// splitter set was split, stop
				if (a.m_isInWorkListIntCall) {
					return;
				}
				
				// split hierarchical predecessors
				splitHierPred(lins, a, letter);
				
				// splitter set was split, stop
				if (a.m_isInWorkListIntCall) {
					return;
				}
			}
		}
	}
	
	/**
	 * This method splits linear predecessor states via return transitions.
	 * 
	 * The rule is to split two states from the class if there is a
	 * hierarchical predecessor in the original automaton with which one state
	 * reaches equivalence class 1 and the other state reaches either another
	 * equivalence class or a sink state.
	 * The latter is the case if there is no respective outgoing transition,
	 * but the hierarchical predecessor is a possible down state.
	 *
	 * @param lins the linear predecessor equivalence class
	 * @param succEc the successor equivalence class
	 * @param letter the letter
	 */
	private void splitLinPred(final Collection<STATE> lins,
			final EquivalenceClass succEc, final LETTER letter) {
		// find hierarchical predecessors
		final HashSet<STATE> hiers = new HashSet<STATE>();
		for (final STATE lin : lins) {
			for (final OutgoingReturnTransition<LETTER, STATE> edge :
				m_operand.returnSuccessors(lin, letter)) {
				hiers.add(edge.getHierPred());
			}
		}
		
		// split by successor equivalence class wrt. hierarchical predecessor
		final int sizeOfLin = lins.size();
		for (final STATE hier : hiers) {
			final HashMap<EquivalenceClass, HashSet<STATE>> succ2lin =
					new HashMap<EquivalenceClass, HashSet<STATE>>();
			final LinkedList<STATE> neutralStates = new LinkedList<STATE>();
			for (final STATE lin : lins) {
				final Iterator<OutgoingReturnTransition<LETTER, STATE>> edges =
						m_operand.returnSucccessors(lin, hier, letter).iterator();
				if (edges.hasNext()) {
					do {
						final OutgoingReturnTransition<LETTER, STATE> edge =
								edges.next();
						final EquivalenceClass currentSuccEc =
								m_partition.m_state2EquivalenceClass.get(
										edge.getSucc());
						HashSet<STATE> linEc = succ2lin.get(currentSuccEc);
						if (linEc == null) {
							linEc = new HashSet<STATE>();
							succ2lin.put(currentSuccEc, linEc);
						}
						linEc.add(lin);
					} while (edges.hasNext());
				}
				else {
					// if the return edge is not possible, ignore state
					if (! m_doubleDecker.isDoubleDecker(lin, hier)) {
						neutralStates.add(lin);
					}
				}
			}
			
			// split
			for (final HashSet<STATE> linSplits : succ2lin.values()) {
				/*
				 * TODO<TIEBREAK> what to do?
				 *                Currently neutral states are seen positive.
				 */
				final SplitCombinator combinator =
						new SplitCombinator(linSplits, neutralStates);
				
				// ignore unaffecting splits
				if (combinator.size() < sizeOfLin) {
					m_partition.splitEquivalenceClasses(combinator);
				}
				else {
					if (DEBUG)
						System.out.println("combinator " + combinator +
								" was ignored");
				}
			}
		}
	}
	
	/**
	 * This method splits hierarchical predecessor states via return
	 * transitions and linear predecessor equivalence classes.
	 * 
	 * The rule is to split two states from the class if there is a
	 * linear predecessor in the original automaton with which one state
	 * reaches equivalence class 1 and the other state reaches either another
	 * equivalence class or a sink state.
	 * The latter is the case if there is no respective outgoing transition,
	 * but the hierarchical predecessor is a possible down state.
	 *
	 * @param lins the linear predecessor equivalence class
	 * @param succEc the successor equivalence class
	 * @param letter the letter
	 */
	private void splitHierPred(final Iterable<STATE> lins,
			final EquivalenceClass succEc, final LETTER letter) {
		for (final STATE lin : lins) {
			// find hierarchical predecessor equivalence classes
			final HashSet<EquivalenceClass> hiers = new HashSet<EquivalenceClass>();
			for (final OutgoingReturnTransition<LETTER, STATE> edge :
				m_operand.returnSuccessors(lin, letter)) {
				hiers.add(m_partition.m_state2EquivalenceClass.get(
						edge.getHierPred()));
			}
			
			final LinkedList<STATE> neutralStates = new LinkedList<STATE>();
			
			// check each hierarchical predecessor
			for (final EquivalenceClass hierEc : hiers) {
				final int sizeOfHier = hierEc.m_states.size();
				
				final HashMap<HashSet<EquivalenceClass>, HashSet<STATE>>
						reachedEc2hier = new HashMap<HashSet<EquivalenceClass>,
						HashSet<STATE>>();
				for (final STATE hier : hierEc.m_states) {
					// collect all reached equivalence classes
					final Iterator<OutgoingReturnTransition<LETTER, STATE>> edges =
							m_operand.returnSucccessors(lin, hier, letter).iterator();
					if (edges.hasNext()) {
						final HashSet<EquivalenceClass> reached =
								new HashSet<EquivalenceClass>();
						do {
							reached.add(m_partition.m_state2EquivalenceClass.get(
									edges.next().getSucc()));
						} while (edges.hasNext());
						
						HashSet<STATE> hierList = reachedEc2hier.get(reached);
						if (hierList == null) {
							hierList = new HashSet<STATE>();
							reachedEc2hier.put(reached, hierList);
						}
						hierList.add(hier);
					}
					else {
						// if the return edge is not possible, ignore state
						if (! m_doubleDecker.isDoubleDecker(lin, hier)) {
							neutralStates.add(hier);
						}
					}
				}
				
				// split
				for (final HashSet<STATE> hierSplits : reachedEc2hier.values()) {
					/*
					 * TODO<TIEBREAK> what to do?
					 *                Currently neutral states are seen positive.
					 */
					final SplitCombinator combinator =
							new SplitCombinator(hierSplits, neutralStates);
					
					// ignore unaffecting splits
					if (combinator.size() < sizeOfHier) {
						m_partition.splitEquivalenceClasses(combinator);
					}
					else {
						if (DEBUG)
							System.out.println("combinator " + combinator +
									" was ignored");
					}
				}
			}
		}
	}
	
	/**
	 * For each remaining equivalence class create a new state.
	 * Also remove all other objects references.
	 */
	private void constructAutomaton() {
//		TODO<noReduction> return old automaton?!
//		if (m_operand.size() == m_partition.m_equivalenceClasses.size()) {
//			return m_operand;
//		}
		m_result = new ShrinkNwaResult();
		
		// clean up
		if (DEBUG) {
			System.out.println(m_partition);
			System.out.println(m_result);
		}
		m_partition = null;
		m_workListIntCall = null;
		m_workListRet = null;
	}
	
	// --- [end] main methods --- //
	
	// --- [start] helper methods and classes --- //
	
	/**
	 * This method computes the size of a hash set to avoid rehashing.
	 * This is only sensible if the maximum size is already known.
	 * Java standard sets the load factor to 0.75.
	 * 
	 * @param size maximum number of elements in the hash set
	 * @return hash set size
	 */
	private int computeHashSetCapacity(final int size) {
		return (int) (size / 0.75 + 1);
	}
	
	/**
	 * A transition iterator is used for splitting internal and call
	 * predecessors.
	 *
	 * @param <STATE> state type
	 * @param <LETTER> letter type
	 */
	private interface ITransitionIterator<LETTER, STATE> {
		/**
		 * A new successor state is considered.
		 *
		 * @param state the successor state
		 * @return
		 */
		void nextState(final STATE state);
		
		/**
		 * The iterator is told to consider the next transition.
		 * 
		 * @return the letter of the next transition
		 */
		LETTER nextAndLetter();
		
		/**
		 * Tells whether the iterator has another transition.
		 *
		 * @return true iff there is another transition left
		 */
		boolean hasNext();
		
		/**
		 * @return the predecessor state
		 */
		STATE getPred();
	}
	
	/**
	 * This is the implementation for internal transitions.
	 */
	private class InternalTransitionIterator implements
			ITransitionIterator<LETTER, STATE> {
		// iterator of the operand
		private Iterator<IncomingInternalTransition<LETTER, STATE>> m_iterator;
		// current transition
		private IncomingInternalTransition<LETTER, STATE> m_transition;
		
		@Override
		public void nextState(final STATE state) {
			m_iterator = m_operand.internalPredecessors(state).iterator();
		}
		
		@Override
		public STATE getPred() {
			return m_transition.getPred();
		}
		
		@Override
		public LETTER nextAndLetter() {
			m_transition = m_iterator.next();
			return m_transition.getLetter();
		}
		
		@Override
		public boolean hasNext() {
			return m_iterator.hasNext();
		}
	}
	
	/**
	 * This is the implementation for call transitions.
	 */
	private class CallTransitionIterator implements
			ITransitionIterator<LETTER, STATE> {
		// iterator of the operand
		private Iterator<IncomingCallTransition<LETTER, STATE>> m_iterator;
		// current transition
		private IncomingCallTransition<LETTER, STATE> m_transition;
		
		@Override
		public void nextState(final STATE state) {
			m_iterator = m_operand.callPredecessors(state).iterator();
		}
		
		@Override
		public LETTER nextAndLetter() {
			m_transition = m_iterator.next();
			return m_transition.getLetter();
		}
		
		@Override
		public STATE getPred() {
			return m_transition.getPred();
		}
		
		@Override
		public boolean hasNext() {
			return m_iterator.hasNext();
		}
	}
	
	/**
	 * This class combines two collection objects to one iterable.
	 */
	private class SplitCombinator implements Iterable<STATE> {
		// iterables
		private Collection<STATE> m_collection1, m_collection2;
		// size
		private final int m_size;
		
		/**
		 * @param iterable1 first collection
		 * @param iterable2 second collection
		 */
		public SplitCombinator(final Collection<STATE> iterable1,
				final Collection<STATE> iterable2) {
			m_collection1 = iterable1;
			m_collection2 = iterable2;
			m_size = m_collection1.size() + m_collection2.size();
		}
		
		/**
		 * @return size of the two collections together
		 */
		public int size() {
			return m_size;
		}

		@Override
		public Iterator<STATE> iterator() {
			return new Iterator<STATE>() {
				private Iterator<STATE> m_it = m_collection1.iterator();
				private boolean m_second = false;
				
				@Override
				public boolean hasNext() {
					return m_it.hasNext();
				}
				
				@Override
				public STATE next() {
					final STATE next = m_it.next();
					if (! m_it.hasNext() && ! m_second) {
						m_second = true;
						m_it = m_collection2.iterator();
					}
					return next;
				}
				
				@Override
				public void remove() {
					throw new UnsupportedOperationException(
							"Removing is not supported.");
				}
			};
		}
		
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			builder.append("{");
			builder.append(m_collection1);
			builder.append(", ");
			builder.append(m_collection2);
			builder.append("}");
			return builder.toString();
		}
	}
	
	// --- [end] helper methods and classes --- //
	
	// --- [start] important inner classes --- //
	
	/**
	 * The partition is the main object of the procedure.
	 * It contains and handles the equivalence classes and works as the
	 * resulting automaton.
	 */
	public class Partition {
		// equivalence classes
		private final Collection<EquivalenceClass> m_equivalenceClasses;
		// mapping 'state -> equivalence class'
		private final HashMap<STATE,EquivalenceClass> m_state2EquivalenceClass;
		// storage for split equivalence classes
		private List<EquivalenceClass> m_splitEquivalenceClasses;
		
		public Partition() {
			m_equivalenceClasses = new LinkedList<EquivalenceClass>();
			m_state2EquivalenceClass = new HashMap<STATE, EquivalenceClass>(
					computeHashSetCapacity(m_operand.size()));
			m_splitEquivalenceClasses = new LinkedList<EquivalenceClass>();
		}
		
		/**
		 * This method adds an equivalence class (also to the work list).
		 * The states mapping is updated accordingly.
		 *
		 * @param module the states in the equivalence class
		 */
		private void addEc(Set<STATE> module) {
			final EquivalenceClass ec = addEcHelper(module);
			for (STATE state : module) {
				m_state2EquivalenceClass.put(state, ec);
			}
		}
		
		/**
		 * This method adds a new equivalence class to the partition.
		 *
		 * @param module the states in the equivalence class
		 * @return the equivalence class
		 */
		private EquivalenceClass addEcHelper(final Set<STATE> module) {
			final EquivalenceClass ec =
				new EquivalenceClass(module);
			m_equivalenceClasses.add(ec);
			return ec;
		}
		
		/**
		 * This method splits a state from its equivalence class.
		 * The equivalence class is remembered 
		 */
		private void splitState(final STATE state) {
			final EquivalenceClass ec = m_state2EquivalenceClass.get(state);
			
			// first occurrence of the equivalence class, mark it
			if (ec.m_intersection.size() == 0) {
				m_splitEquivalenceClasses.add(ec);
			}
			
			// move state to intersection set
			ec.m_intersection.add(state);
			
			// remove state from old set
			ec.m_states.remove(state);
		}
		
		/**
		 * This method finally splits the marked equivalence classes into two.
		 * The states are already split in the equivalence class.
		 * Only if there are states remaining the split is executed, otherwise
		 * the old equivalence class is restored.
		 * 
		 * @param states set of states to split
		 * @return true iff a split occurred
		 */
		private boolean splitEquivalenceClasses(final Iterable<STATE> states) {
			boolean splitOccurred = false;
			
			// process splits
			for (final STATE state : states) {
				if (DEBUG)
					System.out.println("splitting state " + state);
				splitState(state);
			}
			
			// check and finalize splits
			for (final EquivalenceClass ec : m_splitEquivalenceClasses) {
				// split removed every state, restore equivalence class
				if (ec.m_states.isEmpty()) {
					ec.m_states = ec.m_intersection;
					if (DEBUG)
						System.out.println("EC was skipped " + ec);
					
					// reset equivalence class
					ec.reset();
				}
				// do a split
				else {
					splitOccurred = true;
					final Set<STATE> intersection = ec.m_intersection;
					final EquivalenceClass newEc =
							addEcHelper(intersection);
					for (STATE state : intersection) {
						m_state2EquivalenceClass.put(state, newEc);
					}
					
					// put ec in work lists if not already in there
					if (! ec.m_isInWorkListIntCall) {
						ec.m_isInWorkListIntCall = true;
						m_workListIntCall.add(ec);
					}
					if (! ec.m_isInWorkListRet) {
						ec.m_isInWorkListRet = true;
						m_workListRet.add(ec);
					}
					
					// reset equivalence class (before 
					ec.reset();
					
					if (DEBUG)
						System.out.println("EC was split " + ec);
				}
			}
			
			// reset split list
			m_splitEquivalenceClasses = new LinkedList<EquivalenceClass>();
			return splitOccurred;
		}
		
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			builder.append("{");
			String append = "";
			for (final EquivalenceClass ec : m_equivalenceClasses) {
				builder.append(append);
				append = ", ";
				builder.append(ec);
			}
			builder.append("}");
			return builder.toString();
		}
	}
	
	/**
	 * An equivalence class contains states and knows whether it is in the
	 * work list.
	 * 
	 * Two equivalence class objects are equal iff they share the same pointer.
	 * 
	 * TODO<hashCode> overwrite? it works
	 */
	private class EquivalenceClass {
		// the states
		private Set<STATE> m_states;
		// true iff equivalence class is in the respective work list
		private boolean m_isInWorkListIntCall;
		private boolean m_isInWorkListRet;
		// intersection set that finally becomes a new equivalence class
		private Set<STATE> m_intersection;
		
		/**
		 * @param states the set of states for the equivalence class
		 */
		public EquivalenceClass(final Set<STATE> states) {
			m_states = states;
			reset();
			m_isInWorkListIntCall = true;
			m_workListIntCall.add(this);
			m_isInWorkListRet = true;
			m_workListRet.add(this);
		}
		
		/**
		 * This method resets the intersection set.
		 */
		private void reset() {
			m_intersection = new HashSet<STATE>(
					computeHashSetCapacity(m_states.size()));
		}
		
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			String append = "";
			if (! m_isInWorkListIntCall && ! m_isInWorkListRet &&
					m_intersection.isEmpty()) {
				builder.append("<");
				for (final STATE state : m_states) {
					builder.append(append);
					append = ", ";
					builder.append(state);
				}
				builder.append(">");
				return builder.toString();
			}
			
			builder.append("<[");
			builder.append(m_isInWorkListIntCall ? "IC" : "-");
			builder.append(",");
			builder.append(m_isInWorkListRet ? "R" : "-");
			builder.append("], [");
			for (final STATE state : m_states) {
				builder.append(append);
				append = ", ";
				builder.append(state);
			}
			builder.append("], [");
			append = "";
			for (final STATE state : m_intersection) {
				builder.append(append);
				append = ", ";
				builder.append(state);
			}
			builder.append("]>");
			return builder.toString();
		}
	}
	
	/**
	 * The work list has a priority queue of equivalence classes.
	 * 
	 * Since the size of the equivalence classes may change due to splitting,
	 * it is not guaranteed that the order is correct over time, but since it
	 * is a heuristic rather than a rule to prefer smaller splitters first,
	 * this is not considered bad and additional overhead is avoided.
	 */
	private abstract class AWorkList implements Iterator<EquivalenceClass> {
		protected final PriorityQueue<EquivalenceClass> m_queue;
		
		public AWorkList() {
			m_queue = new PriorityQueue<EquivalenceClass>(
					Math.max(m_operand.size(), 1),
					new Comparator<EquivalenceClass>() {
						@Override
						public int compare(EquivalenceClass ec1,
								EquivalenceClass ec2) {
							return ec1.m_states.size() - ec2.m_states.size();
						}
					});
		}
		
		/**
		 * This method adds an equivalence class to the work list.
		 * The caller asserts that the class is not already in the work list
		 * and must inform the equivalence class beforehand.
		 *
		 * @param ec the equivalence class
		 */
		public void add(final EquivalenceClass ec) {
			assert (! m_queue.contains(ec));
			m_queue.add(ec);
		}
		
		@Override
		public boolean hasNext() {
			return (! m_queue.isEmpty());
		}
		
		@Override
		public abstract EquivalenceClass next();
		
		@Override
		public void remove() {
			throw new UnsupportedOperationException(
					"Removing is not supported.");
		}
		
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			toStringHelper(builder);
			builder.append(">>");
			return builder.toString();
		}
		
		/**
		 * This method constructs most of the string representation.
		 *
		 * @param builder the string builder
		 */
		protected void toStringHelper(final StringBuilder builder) {
			builder.append("<<");
			String append = "";
			for (final EquivalenceClass ec : m_queue) {
				builder.append(append);
				append = ", ";
				builder.append(ec);
			}
		}
	}
	
	/**
	 * This class implements the work list for internal and call splits.
	 */
	private class WorkListIntCall extends AWorkList {
		@Override
		public EquivalenceClass next() {
			final EquivalenceClass ec = m_queue.poll();
			ec.m_isInWorkListIntCall = false;
			if (DEBUG)
				System.out.println("\npopping from IntCall WL: " + ec);
			return ec;
		}
		
		@Override
		public void add(final EquivalenceClass ec) {
			assert (ec.m_isInWorkListIntCall);
			if (DEBUG)
				System.out.println("adding of IntCall WL: " + ec);
			super.add(ec);
		}
	}
	
	/**
	 * This class implements the work list for detailed predecessor return
	 * splits.
	 * 
	 * TODO<detailedReturnSplit> could be improved:
	 *                           only classes with returns must be inserted
	 */
	private class WorkListRet extends AWorkList {
		@Override
		public EquivalenceClass next() {
			final EquivalenceClass ec = m_queue.poll();
			ec.m_isInWorkListRet = false;
			if (DEBUG)
				System.out.println("\npopping from detailed return WL: " + ec);
			return ec;
		}
		
		@Override
		public void add(final EquivalenceClass ec) {
			assert (ec.m_isInWorkListRet);
			if (DEBUG)
				System.out.println("adding of detailed return WL: " + ec);
			super.add(ec);
		}
	}
	
	/**
	 * This class temporarily works as the output automaton.
	 * The future idea is not to generate a real object but to simulate states
	 * and transitions with the equivalence class objects.
	 */
	public class ShrinkNwaResult implements
			INestedWordAutomatonSimple<LETTER, STATE> {
		// old automaton
		private final INestedWordAutomaton<LETTER, STATE> m_oldNwa;
		// states
		private final HashSet<STATE> m_finals;
		private final HashSet<STATE> m_nonfinals;
		// initial states
		private final HashSet<STATE> m_initialStates;
		// transitions
		private final HashMap<STATE,
			HashSet<OutgoingInternalTransition<LETTER, STATE>>> m_outInt;
		private final HashMap<STATE,
			HashSet<OutgoingCallTransition<LETTER, STATE>>> m_outCall;
		private final HashMap<STATE,
			HashSet<OutgoingReturnTransition<LETTER, STATE>>> m_outRet;
		
		// TODO<correctness> check that all states have the same edges!
		public ShrinkNwaResult() {
			if (DEBUG)
				System.out.println("\n---- constructing result...");
			m_oldNwa = m_operand;
			m_finals = new HashSet<STATE>();
			m_nonfinals = new HashSet<STATE>();
			m_initialStates = new HashSet<STATE>();
			
			final StateFactory<STATE> factory = m_oldNwa.getStateFactory();
			final HashMap<EquivalenceClass, STATE> ec2state =
					new HashMap<EquivalenceClass, STATE>(
							computeHashSetCapacity(
									m_partition.m_state2EquivalenceClass.
									size()));
			
			final HashSet<EquivalenceClass> initials =
					new HashSet<EquivalenceClass>();
			for (final STATE init : m_oldNwa.getInitialStates()) {
				initials.add(m_partition.m_state2EquivalenceClass.get(init));
			}
			
			m_outInt = new HashMap<STATE,
					HashSet<OutgoingInternalTransition<LETTER, STATE>>>();
			m_outCall = new HashMap<STATE,
					HashSet<OutgoingCallTransition<LETTER, STATE>>>();
			m_outRet = new HashMap<STATE,
					HashSet<OutgoingReturnTransition<LETTER, STATE>>>();
			
			for (final EquivalenceClass ec : m_partition.m_equivalenceClasses)
					{
				final Set<STATE> ecStates = ec.m_states;
				
				// new state
				final STATE newState = factory.minimize(ecStates);
				ec2state.put(ec, newState);
				
				// states
				if (m_oldNwa.isFinal(ecStates.iterator().next())) {
					m_finals.add(newState);
				}
				else {
					m_nonfinals.add(newState);
				}
				
				if (initials.contains(ec)) {
					m_initialStates.add(newState);
				}
			}
			
			// transitions
			for (final EquivalenceClass ec : m_partition.m_equivalenceClasses)
					{
				final STATE newState = ec2state.get(ec);
				if (DEBUG)
					System.out.println(" from state " + newState + 
							" have transitions:");
				
				final STATE representative = ec.m_states.iterator().next();
				
				// internal transitions
				HashSet<OutgoingInternalTransition<LETTER, STATE>> outInt =
						m_outInt.get(newState);
				if (outInt == null) {
					outInt = new HashSet<
							OutgoingInternalTransition<LETTER,STATE>>();
					m_outInt.put(newState, outInt);
				}
				
				HashMap<LETTER, HashSet<STATE>> internals =
						new HashMap<LETTER, HashSet<STATE>>();
				for (final OutgoingInternalTransition<LETTER, STATE> edge :
						m_oldNwa.internalSuccessors(representative)) {
					final LETTER letter = edge.getLetter();
					HashSet<STATE> succs = internals.get(letter);
					if (succs == null) {
						succs = new HashSet<STATE>();
						internals.put(letter, succs);
					}
					succs.add(ec2state.get(m_partition.
							m_state2EquivalenceClass.get(edge.getSucc())));
				}
				for (final Entry<LETTER, HashSet<STATE>> entry :
						internals.entrySet()) {
					for (final STATE succ : entry.getValue()) {
						final OutgoingInternalTransition<LETTER, STATE>
								newEdge = new OutgoingInternalTransition
								<LETTER, STATE> (entry.getKey(), succ);
						if (DEBUG)
							System.out.println("   internal " + newEdge);
						outInt.add(newEdge);
					}
				}
				internals = null;
				
				// call transitions
				HashSet<OutgoingCallTransition<LETTER, STATE>> outCall =
						m_outCall.get(newState);
				if (outCall == null) {
					outCall = new HashSet<
							OutgoingCallTransition<LETTER,STATE>>();
					m_outCall.put(newState, outCall);
				}
				
				HashMap<LETTER, HashSet<STATE>> calls =
						new HashMap<LETTER, HashSet<STATE>>();
				for (final OutgoingCallTransition<LETTER, STATE> edge :
						m_oldNwa.callSuccessors(representative)) {
					final LETTER letter = edge.getLetter();
					HashSet<STATE> succs = calls.get(letter);
					if (succs == null) {
						succs = new HashSet<STATE>();
						calls.put(letter, succs);
					}
					succs.add(ec2state.get(m_partition.
							m_state2EquivalenceClass.get(edge.getSucc())));
				}
				for (final Entry<LETTER, HashSet<STATE>> entry :
					calls.entrySet()) {
					for (final STATE succ : entry.getValue()) {
						final OutgoingCallTransition<LETTER, STATE>
								newEdge = new OutgoingCallTransition
								<LETTER, STATE> (entry.getKey(), succ);
						if (DEBUG)
							System.out.println("   call " + newEdge);
						outCall.add(newEdge);
					}
				}
				calls = null;
				
				/*
				 * return transitions
				 * NOTE: Return transitions need not be present everywhere,
				 *       so each state must be visited.
				 */
				HashSet<OutgoingReturnTransition<LETTER, STATE>> outRet =
						m_outRet.get(newState);
				if (outRet == null) {
					outRet = new HashSet<
							OutgoingReturnTransition<LETTER,STATE>>();
					m_outRet.put(newState, outRet);
				}
				
				HashMap<LETTER, HashMap<STATE, HashSet<STATE>>> returns =
						new HashMap<LETTER,
						HashMap<STATE, HashSet<STATE>>>();
				for (final STATE state : ec.m_states) {
					for (final OutgoingReturnTransition<LETTER, STATE> edge :
							m_oldNwa.returnSuccessors(state)) {
						final LETTER letter = edge.getLetter();
						HashMap<STATE, HashSet<STATE>> lin2succs =
								returns.get(letter);
						if (lin2succs == null) {
							lin2succs = new HashMap<STATE, HashSet<STATE>>();
							returns.put(letter, lin2succs);
						}
						final STATE hier = ec2state.get(
								m_partition.m_state2EquivalenceClass.get(
										edge.getHierPred()));
						HashSet<STATE> succs = lin2succs.get(hier);
						if (succs == null) {
							succs = new HashSet<STATE>();
							lin2succs.put(hier, succs);
						}
						succs.add(ec2state.get(m_partition.
								m_state2EquivalenceClass.get(edge.getSucc())));
					}
					for (final Entry<LETTER, HashMap<STATE, HashSet<STATE>>>
							entry : returns.entrySet()) {
						for (final Entry<STATE, HashSet<STATE>>
								entry2 : entry.getValue().entrySet()) {
							for (final STATE succ : entry2.getValue()) {
								final OutgoingReturnTransition<LETTER, STATE>
										newEdge = new OutgoingReturnTransition
										<LETTER, STATE> (entry2.getKey(),
										entry.getKey(), succ);
								if (DEBUG)
									System.out.println("   return " + newEdge);
								outRet.add(newEdge);
							}
						}
					}
				}
				returns = null;
				
				if (DEBUG) {
					System.out.println("---------------\n resulting in: " +
							newState);
					System.out.println("   internal:");
					System.out.println(m_outInt);
					System.out.println("   call:");
					System.out.println(m_outCall);
					System.out.println("   return:");
					System.out.println(m_outRet);
					System.out.println("---------------");
				}
			}
		}
		
		@Override
		public Set<LETTER> getAlphabet() {
			return m_oldNwa.getAlphabet();
		}
		@Override
		public Set<LETTER> getInternalAlphabet() {
			return m_oldNwa.getInternalAlphabet();
		}
		@Override
		public Set<LETTER> getCallAlphabet() {
			return m_oldNwa.getCallAlphabet();
		}
		@Override
		public Set<LETTER> getReturnAlphabet() {
			return m_oldNwa.getReturnAlphabet();
		}
		@Override
		public STATE getEmptyStackState() {
			return m_oldNwa.getEmptyStackState();
		}
		@Override
		public StateFactory<STATE> getStateFactory() {
			return m_oldNwa.getStateFactory();
		}
		@Override
		public String sizeInformation() {
			return size() + " states.";
		}
		@Override
		public int size() {
			return m_finals.size() + m_nonfinals.size();
		}
		@Override
		public Collection<STATE> getInitialStates() {
			return m_initialStates;
		}
		@Override
		public boolean isInitial(final STATE state) {
			return m_initialStates.contains(state);
		}
		@Override
		public boolean isFinal(final STATE state) {
			return m_finals.contains(state);
		}
		
		@Override
		public boolean accepts(Word<LETTER> word) {
			// TODO Auto-generated method stub
			return m_oldNwa.accepts(word);
		}
		@Override
		public Collection<LETTER> lettersInternal(STATE state) {
			final HashSet<LETTER> result = new HashSet<LETTER>();
			for (final OutgoingInternalTransition<LETTER, STATE> edge :
					m_outInt.get(state)) {
				result.add(edge.getLetter());
			}
			return result;
		}
		@Override
		public Collection<LETTER> lettersCall(STATE state) {
			final HashSet<LETTER> result = new HashSet<LETTER>();
			for (final OutgoingCallTransition<LETTER, STATE> edge :
					m_outCall.get(state)) {
				result.add(edge.getLetter());
			}
			return result;
		}
		@Override
		public Collection<LETTER> lettersReturn(STATE state) {
			final HashSet<LETTER> result = new HashSet<LETTER>();
			for (final OutgoingReturnTransition<LETTER, STATE> edge :
					m_outRet.get(state)) {
				result.add(edge.getLetter());
			}
			return result;
		}
		@Override
		public Iterable<OutgoingInternalTransition<LETTER, STATE>>
				internalSuccessors(STATE state, LETTER letter) {
			final HashSet<OutgoingInternalTransition<LETTER, STATE>> result =
					new HashSet<OutgoingInternalTransition<LETTER,STATE>>();
			for (final OutgoingInternalTransition<LETTER, STATE> edge :
					m_outInt.get(state)) {
				if (edge.getLetter().equals(letter)) {
					result.add(edge);
				}
			}
			return result;
		}
		@Override
		public Iterable<OutgoingInternalTransition<LETTER, STATE>>
				internalSuccessors(STATE state) {
			return m_outInt.get(state);
		}
		@Override
		public Iterable<OutgoingCallTransition<LETTER, STATE>>
				callSuccessors(STATE state, LETTER letter) {
			final HashSet<OutgoingCallTransition<LETTER, STATE>> result =
			new HashSet<OutgoingCallTransition<LETTER,STATE>>();
			for (final OutgoingCallTransition<LETTER, STATE> edge :
					m_outCall.get(state)) {
				if (edge.getLetter().equals(letter)) {
					result.add(edge);
				}
			}
			return result;
		}
		@Override
		public Iterable<OutgoingCallTransition<LETTER, STATE>>
				callSuccessors(STATE state) {
			return m_outCall.get(state);
		}
		@Override
		public Iterable<OutgoingReturnTransition<LETTER, STATE>>
				returnSucccessors(STATE state, STATE hier, LETTER letter) {
			final HashSet<OutgoingReturnTransition<LETTER, STATE>> result =
					new HashSet<OutgoingReturnTransition<LETTER,STATE>>();
			for (final OutgoingReturnTransition<LETTER, STATE> edge :
					m_outRet.get(state)) {
				if (edge.getLetter().equals(letter) &&
						edge.getHierPred().equals(hier)) {
					result.add(edge);
				}
			}
			return result;
		}
		@Override
		public Iterable<OutgoingReturnTransition<LETTER, STATE>>
				returnSuccessorsGivenHier(STATE state, STATE hier) {
			final HashSet<OutgoingReturnTransition<LETTER, STATE>> result =
					new HashSet<OutgoingReturnTransition<LETTER,STATE>>();
			for (final OutgoingReturnTransition<LETTER, STATE> edge :
					m_outRet.get(state)) {
				if (edge.getHierPred().equals(hier)) {
					result.add(edge);
				}
			}
			return result;
		}
		
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			
			builder.append("{N[");
			String append = "";
			for (final STATE state : m_nonfinals) {
				builder.append(append);
				append = ", ";
				builder.append(state);
				if (m_initialStates.contains(state)) {
					builder.append(" (I)");
				}
			}
			builder.append("], F[");
			append = "";
			for (final STATE state : m_finals) {
				builder.append(append);
				append = ", ";
				builder.append(state);
				if (m_initialStates.contains(state)) {
					builder.append(" (I)");
				}
			}
			builder.append("], ");
			builder.append(m_outInt.isEmpty() ? "-" : m_outInt);
			builder.append(", ");
			builder.append(m_outCall.isEmpty() ? "-" : m_outCall);
			builder.append(", ");
			builder.append(m_outRet.isEmpty() ? "-" : m_outRet);
			builder.append("}");
			
			return builder.toString();
		}
	}
	
	// --- [end] important inner classes --- //
	
	// --- [start] framework methods --- //
	
	@Override
	public String operationName() {
		return "shrinkNwa";
	}
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Operand has " +
			m_operand.sizeInformation();
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ". Reduced states from " +
			m_result.m_oldNwa.size() + " to " +
			m_result.size() + ".";
	}
	
	@Override
	public INestedWordAutomatonSimple<LETTER,STATE> getResult()
			throws OperationCanceledException {
		return m_result;
	}
	
	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		s_Logger.info("Start testing correctness of " + operationName());
		boolean correct = true;
		correct &= (ResultChecker.nwaLanguageInclusion(
				ResultChecker.getOldApiNwa(m_operand),
				ResultChecker.getOldApiNwa(m_result),
				stateFactory) == null);
		correct &= (ResultChecker.nwaLanguageInclusion(
				ResultChecker.getOldApiNwa(m_result),
				ResultChecker.getOldApiNwa(m_operand),
				stateFactory) == null);
		if (!correct) {
			ResultChecker.writeToFileIfPreferred(operationName() + "Failed",
					"", m_operand);
		}
		s_Logger.info("Finished testing correctness of " + operationName());
		return correct;
	}
	
	// --- [end] framework methods --- //
}