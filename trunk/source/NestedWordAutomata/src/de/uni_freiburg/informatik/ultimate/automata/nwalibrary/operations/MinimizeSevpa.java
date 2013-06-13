package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

/**
 * minimizer for special type of nested word automata used in Ultimate
 * 
 * based on idea of Hopcroft's minimization for deterministic finite automata
 * applied to nested word automata (some huge differences)
 * 
 * over-approximation of the language due to ignorance of
 * history encoded in call and return edges
 * afterwards soundness is assured using a more expensive analysis
 * this process is looped until no change occurs anymore
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 */
public class MinimizeSevpa<LETTER,STATE> implements IOperation<LETTER,STATE> {
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	// old automaton
	private final INestedWordAutomatonOldApi<LETTER,STATE> m_operand;
	private final IDoubleDeckerAutomaton<LETTER, STATE> m_doubleDecker;
	// new (minimized) automaton
	private NestedWordAutomaton<LETTER,STATE> m_nwa;
	// enables/disables detection of unnecessary states
	private final boolean m_removeUnreachables, m_removeDeadEnds;
	// indicates if states were removed during preprocessing steps
	private boolean m_noStatesRemoved;
	// ID for equivalence classes (inner class, so no static field possible)
	private static int equivalenceClassId = 0;
	// Partition of states into equivalence classes
	private Partition m_Partition = null;
	// Only true after the result was constructed.
	private boolean m_MinimizationFinished = false;
	
	/*
	 * EXPERIMENTAL
	 * deterministic finite automata can be handled more efficiently
	 * 
	 * not even correct for non-total DFAs
	 * but: if non-final states are initially added to the work list,
	 * all examples run with m_onlyOneToWorkList set to true
	 * (but example 08 is even more reduced, so there IS a difference)
	 */
	private final boolean m_onlyOneToWorkList = false;
	// use sound but expensive linear return split
	private final boolean m_splitAllReturnsLin = false;
	// use sound but expensive hierarchical return split
	private final boolean m_splitAllReturnsHier = false;
	
	private final boolean STATISTICS = false;
	private int m_splitsWithChange = 0;
	private int m_splitsWithoutChange = 0;
	
	/* EXPERIMENTAL END */
	
	
	/**
	 * StateFactory used for the construction of new states. This is _NOT_ the
	 * state factory relayed to the new automaton.
	 * Necessary because the Automizer needs a special StateFactory during
	 * abstraction refinement (for computation of HoareAnnotation).
	 */
	private final StateFactory<STATE> m_StateFactoryConstruction;
	
	/**
	 * creates a copy of operand where non-reachable states are omitted
	 * 
	 * @param operand nested word automaton to minimize
	 * @throws OperationCanceledException iff cancel signal is received
	 */
	public MinimizeSevpa(INestedWordAutomatonOldApi<LETTER,STATE> operand)
			throws OperationCanceledException {
		this(operand, null, true, false, operand.getStateFactory());
	}
	
	/**
	 * creates a copy of operand with an initial partition
	 * 
	 * @param operand nested word automaton to minimize
	 * @param equivalenceClasses represent initial equivalence classes
	 * @param removeUnreachables true iff removal of unreachable states is used
	 * @param removeDeadEnds true iff removal of dead-end states is used
	 * @throws OperationCanceledException iff cancel signal is received
	 */
	@SuppressWarnings("unchecked")
	public MinimizeSevpa(
			final INestedWordAutomatonOldApi<LETTER,STATE> operand,
			Collection<Set<STATE>> equivalenceClasses,
			final boolean removeUnreachables,
			final boolean removeDeadEnds,
			StateFactory<STATE> stateFactoryConstruction)
					throws OperationCanceledException {
		m_operand = operand;
		if (operand instanceof IDoubleDeckerAutomaton<?, ?>) {
			m_doubleDecker = (IDoubleDeckerAutomaton<LETTER, STATE>)operand;
		}
		else {
			throw new IllegalArgumentException(
					"Operand must be an IDoubleDeckerAutomaton.");
		}
		m_removeUnreachables = removeUnreachables;
		m_removeDeadEnds = removeDeadEnds;
		m_StateFactoryConstruction = stateFactoryConstruction;
		
		// if no preprocessing is considered, no states can be removed there
		m_noStatesRemoved = 
				! (this.m_removeUnreachables || this.m_removeDeadEnds);
		
		// must be the last part of the constructor
		s_Logger.info(startMessage());
		minimize(equivalenceClasses);
		m_MinimizationFinished = true;
		s_Logger.info(exitMessage());
		
		if (STATISTICS) {
			System.out.println("positive splits: " + m_splitsWithChange);
			System.out.println("negative splits: " + m_splitsWithoutChange);
			System.out.println("quote (p/n): " +
					(m_splitsWithChange / Math.max(m_splitsWithoutChange, 1)));
		}
	}
	
	/**
	 * invokes the minimization
	 * 
	 * @param equivalenceClasses initial partition of the states
	 * @return minimized nested word automaton
	 * @throws OperationCanceledException iff cancel signal is received
	 */
	private NestedWordAutomaton<LETTER,STATE> minimize(
			Collection<Set<STATE>> equivalenceClasses)
					throws OperationCanceledException {
		if (m_operand != null) {
			hopcroftDfaMinimization(equivalenceClasses);
		}
		return m_nwa;
	}
	
	/**
	 * minimization technique for deterministic finite automata by Hopcroft
	 * (http://en.wikipedia.org/wiki/DFA_minimization)
	 * 
	 * @param equivalenceClasses initial partition of the states
	 * @throws OperationCanceledException iff cancel signal is received
	 */
	private void hopcroftDfaMinimization(
			Collection<Set<STATE>> equivalenceClasses)
					throws OperationCanceledException {
		
		// intermediate container for the states
		StatesContainer states = new StatesContainer(m_operand);
		
		// remove unreachable states
		if (m_removeUnreachables) {
			removeUnneccessary(states, true);
			
			s_Logger.debug("Size after deleting unreachable states: " +
					states.size());
		}
		
		// remove dead end states (never lead to final states)
		if (m_removeDeadEnds) {
			removeUnneccessary(states, false);
			
			s_Logger.debug("Size after deleting dead end states: " +
					states.size());
			s_Logger.warn("After some changes by Matthias removal of dead " +
					"ends might lead to wrong results. Remove dead ends" +
					"in advance.");
		}
		
		// cancel if signal is received
		if (! UltimateServices.getInstance().continueProcessing()) {
			throw new OperationCanceledException();
		}
		
		// if no states were removed, some methods can be used more efficiently
		m_noStatesRemoved = (m_operand.size() == states.size());
		
		// merge non-distinguishable states
		m_nwa = mergeStates(states, equivalenceClasses);
		s_Logger.debug("Size after merging identical states: " +
				m_nwa.size());
	}
	
	/**
	 * removes states that are trivially not needed (unreachable or dead end)
	 * 
	 * NOTE: removes less states than possible, since unreachable hierarchical
	 * states are still added, which is much easier to achieve
	 * 
	 * @param states container with reachable states
	 * @param forwards search direction
	 *  - true: removes all states never reachable
	 *  - false: removes all states from which a final state is never reached
	 */
	private void removeUnneccessary(final StatesContainer states,
									final boolean forwards) {
		// expansion list (initialized with either initial or final states)
		LinkedList<STATE> expand = new LinkedList<STATE>();
		/*
		 * already visited states (initialized with expansion list)
		 * (only used for backwards search)
		 */
		HashSet<STATE> visited;
		
		/*
		 * forwards search; starts from initial states
		 * removes unreachable states
		 */
		if (forwards) {
			visited = null;
			Collection<STATE> initials = m_operand.getInitialStates();
			states.addAll(initials);
			expand.addAll(initials);
			
			while (! expand.isEmpty()) {
				STATE state = expand.pop();
				
				// internal transitions
				for (LETTER letter : m_operand.lettersInternal(state)) {
					for (STATE next : m_operand.succInternal(state, letter)) {
						if (! states.contains(next)) {
							states.addState(next);
							expand.add(next);
						}
					}
				}
				
				// call transitions
				for (LETTER letter : m_operand.lettersCall(state)) {
					for (STATE next : m_operand.succCall(state, letter)) {
						if (! states.contains(next)) {
							states.addState(next);
							expand.add(next);
						}
					}
				}
				
				// return transitions
				for (LETTER letter : m_operand.lettersReturn(state)) {
					for (STATE hier : m_operand.hierPred(state, letter)) {
						if (! states.contains(hier)) {
							states.addState(hier);
							expand.add(hier);
						}
						for (STATE next :
								m_operand.succReturn(state, hier, letter)) {
							if (! states.contains(next)) {
								states.addState(next);
								expand.add(next);
							}
						}
					}
				}
			}
		}
		/*
		 * backwards search; starts from reachable final states
		 * removes dead end states from which no final state is reachable
		 */
		else {
			visited = new HashSet<STATE>(computeHashSetCapacity(states.size()));
			Iterator<STATE> iterator = states.getFinalsIterator();
			while (iterator.hasNext()) {
				STATE state = iterator.next();
				expand.add(state);
				visited.add(state);
			}
			
			while (! expand.isEmpty()) {
				STATE state = expand.pop();
				
				// internal transitions
				for (LETTER letter :
						m_operand.lettersInternalIncoming(state)) {
					for (STATE pred : states.predInternal(state, letter)) {
						if (! visited.contains(pred)) {
							visited.add(pred);
							expand.add(pred);
						}
					}
				}
				
				// call transitions
				for (LETTER letter : m_operand.lettersCallIncoming(state)) {
					for (STATE pred : states.predCall(state, letter)) {
						if (! visited.contains(pred)) {
							visited.add(pred);
							expand.add(pred);
						}
					}
				}
				
				// return transitions
				for (LETTER letter : m_operand.lettersReturnIncoming(state)) {
					for (STATE hier : states.predReturnHier(state, letter)) {
						if (! visited.contains(hier)) {
							visited.add(hier);
							expand.add(hier);
						}
						for (STATE next :
								states.predReturnLin(state, letter, hier)) {
							if (!  visited.contains(next)) {
								visited.add(next);
								expand.add(next);
							}
						}
					}
				}
			}
			
			// remove non-reached states (= all states - visited states)
			for (STATE state : m_operand.getStates()) {
				if (! visited.contains(state))
					states.removeState(state);
			}
		}
	}
	
	/**
	 * merges states that are not distinguishable
	 * (based on Hopcroft's algorithm)
	 * 
	 * @param states container with reachable states (gets deleted)
	 * @param equivalenceClasses initial partition of the states
	 * @return equivalent automaton with states merged
	 * @throws OperationCanceledException iff cancel signal is received
	 */
	private NestedWordAutomaton<LETTER, STATE> mergeStates(
			StatesContainer states,
			Collection<Set<STATE>> equivalenceClasses)
					throws OperationCanceledException {
		
		// creation of the initial partition (if not passed in the constructor)
		if (equivalenceClasses == null) {
			assert (m_Partition == null);
			m_Partition = createInitialPartition(states);
		}
		// construct initial partition using collections from constructor
		else {
			assert (m_Partition == null &&
					assertStatesSeparation(equivalenceClasses));
			m_Partition = new Partition(m_operand, states.size());
			
			if (m_noStatesRemoved) {
				for (Set<STATE> ecSet : equivalenceClasses) {
					assert ecSet.size() > 0;
					m_Partition.addEquivalenceClass(
						new EquivalenceClass(ecSet,
							m_operand.isFinal(ecSet.iterator().next())));
				}
			}
			else {
				// number of states to remove (for faster use)
				int toRemove = 0;
				for (Set<STATE> ecSet : equivalenceClasses) {
					toRemove += ecSet.size();
				}
				toRemove -= states.size();
				assert toRemove > 0;
				
				/*
				 * if initial partition was passed, but unnecessary states
				 * were found, then remove them from the partition
				 */
				for (Set<STATE> ecSet : equivalenceClasses) {
					if (toRemove > 0) {
						for (STATE state : ecSet) {
							if (! states.contains(state)) {
								ecSet.remove(state);
								toRemove--;
								if (toRemove == 0) {
									break;
								}
							}
						}
					}
					
					m_Partition.addEquivalenceClass(
						new EquivalenceClass(ecSet,
							m_operand.isFinal(ecSet.iterator().next())));
				}
			}
		}
		
		/*
		 * delete states container data structure 
		 * (not totally possible in Java)
		 */
		states.delete();
		states = null;
		
		// partition refinement
		refinePartition();
		
		// merge states from partition
		return merge();
	}
	
	/**
	 * checks that the states in each equivalence class are all either final
	 * or non-final
	 *
	 * @param equivalenceClasses partition passed in constructor
	 * @return true iff equivalence classes respect final status of states
	 */
	private boolean assertStatesSeparation(
			final Collection<Set<STATE>> equivalenceClasses) {
		for (final Set<STATE> equivalenceClass : equivalenceClasses) {
			final Iterator<STATE> it = equivalenceClass.iterator();
			assert (it.hasNext());
			final boolean isFinal = m_operand.isFinal(it.next());
			while (it.hasNext()) {
				if (isFinal != m_operand.isFinal(it.next())) {
					return false;
				}
			}
		}
		return true;
	}
	
	/**
	 * creates the initial partition
	 * distinguishes between final and non-final states
	 * 
	 * @param states container with reachable states
	 * @return initial partition of the states
	 */
	private Partition createInitialPartition(
			final StatesContainer states) {
		// build two sets with final and non-final states, respectively
		HashSet<STATE> finals, nonfinals;
		
		// if sets already exist, use them
		if (states.wasCopied()) {
			finals = states.getFinals();
			nonfinals = states.getNonfinals();
		}
		// make a copy here if states container has no sets
		else
		// if states were removed, use iterator of states container
		if (! m_noStatesRemoved) {
			finals = new HashSet<STATE>(
					computeHashSetCapacity(states.getRemovedSize(true)));
			nonfinals = new HashSet<STATE>(computeHashSetCapacity(
											states.getRemovedSize(false)));
			Iterator<STATE> iterator = states.getFinalsIterator();
			while (iterator.hasNext()) {
				finals.add(iterator.next());
			}
			iterator = states.getNonfinalsIterator();
			while (iterator.hasNext()) {
				nonfinals.add(iterator.next());
			}
		}
		// if no states were removed, use iterator of original automaton
		else {
			finals = new HashSet<STATE>(
					computeHashSetCapacity(m_operand.getFinalStates().size()));
			nonfinals = new HashSet<STATE>(computeHashSetCapacity(
					m_operand.size() - m_operand.getFinalStates().size()));
			for (STATE state : m_operand.getStates()) {
				if (m_operand.isFinal(state)) {
					finals.add(state);
				}
				else {
					nonfinals.add(state);
				}
			}
		}
		
		// create partition object
		Partition partition =
				new Partition(m_operand, finals.size() + nonfinals.size());
		
		// set up the initial equivalence classes
		
		// final states
		if (finals.size() > 0) {
			EquivalenceClass finalsP = new EquivalenceClass(finals, true, true);
			partition.addEquivalenceClass(finalsP);
		}
		
		// non-final states (initially not in work list)
		if (nonfinals.size() > 0) {
			EquivalenceClass nonfinalsP =
								new EquivalenceClass(nonfinals, false, true);
			partition.addEquivalenceClass(nonfinalsP);
		}
		
		return partition;
	}
	
	/**
	 * iteratively refines partition until fixed point is reached
	 * for each letter finds the set of predecessor states (X)
	 * 
	 * @throws OperationCanceledException iff cancel signal is received
	 */
	private void refinePartition()
			throws OperationCanceledException {
		/*
		 * naiveSplit used as long as possible
		 * then switch to more complicated but sound split
		 */
		boolean naiveSplit = true;
		// assures that complicated split is executed at least once
		boolean firstIteration = true;
		// number of equivalence classes (termination if no change)
		int equivalenceClasses = m_Partition.getEquivalenceClasses().size();
		
		while (true) {
			// fixed point iteration
			while (! m_Partition.workListIsEmpty()) {
				
				// A = next equivalence class from W, also called target set
				TargetSet a = new TargetSet(m_Partition.popFromWorkList());
				assert !a.isEmpty();
				
				// collect all incoming letters (and outgoing returns)
				HashSet<LETTER> internalLetters, callLetters,
								returnLettersOutgoing;
				HashSet<LETTER> returnLetters = new HashSet<LETTER>();
				
				if (naiveSplit) {
					internalLetters = new HashSet<LETTER>();
					callLetters = new HashSet<LETTER>();
					returnLettersOutgoing = new HashSet<LETTER>();
					
					Iterator<STATE> iterator = a.iterator();
					while (iterator.hasNext()) {
						STATE state = iterator.next();
						
						internalLetters.addAll(
								m_operand.lettersInternalIncoming(state));
						callLetters.addAll(
								m_operand.lettersCallIncoming(state));
						returnLetters.addAll(
								m_operand.lettersReturnIncoming(state));
						returnLettersOutgoing.addAll(
								m_operand.lettersReturn(state));
					}
				}
				else {
					internalLetters = null;
					callLetters = null;
					returnLettersOutgoing = null;
					
					Iterator<STATE> iterator = a.iterator();
					while (iterator.hasNext()) {
						STATE state = iterator.next();
						
						returnLetters.addAll(
								m_operand.lettersReturnIncoming(state));
					}
				}
				
				if (naiveSplit) {
					// internal alphabet
					findXByInternalOrCall(a, m_Partition, internalLetters,
							new InternalPredecessorSetFinder(m_Partition, a));
					
					// call alphabet
					findXByInternalOrCall(a, m_Partition, callLetters,
							new CallPredecessorSetFinder(m_Partition, a));
				}
				
				// return alphabet
				
				findXByReturn(a, m_Partition, returnLetters, naiveSplit);
				
				if (naiveSplit) {
					// return successor split
					
					findXByOutgoingReturn(a, m_Partition, returnLettersOutgoing,
							new ReturnSuccessorSetFinder(m_Partition, a));
				}
				
				// remove flags for target set
				a.delete();
				
				// cancel iteration iff cancel signal is received
				if (! UltimateServices.getInstance().continueProcessing()) {
					throw new OperationCanceledException();
				}
			}
			
			// after the first iteration the complicated split is executed
			if (firstIteration) {
				firstIteration = false;
			}
			// termination criterion: complicated split did not change anything
			else {
				if (m_Partition.getEquivalenceClasses().size() ==
						equivalenceClasses) {
					break;
				}
				assert (m_Partition.getEquivalenceClasses().size() >
						equivalenceClasses);
			}

			naiveSplit = !naiveSplit;
			equivalenceClasses = m_Partition.getEquivalenceClasses().size();
			putAllToWorkList(m_Partition, naiveSplit);
		}
	}
	
	/**
	 * finds set of predecessor states X and invokes next step
	 * 
	 * @param a target set of which X shall be computed
	 * @param partition partition of the states
	 * @param alphabet collection of internal or call letters
	 * @param predecessorFinder finds the predecessor set X
	 */
	private void findXByInternalOrCall(TargetSet a, Partition partition,
						final Collection<LETTER> alphabet,
						final APredecessorSetFinder predecessorFinder) {
		for (LETTER letter : alphabet) {
			
			/*
			 * X = predecessor set of A = all states s1
			 * with transition (s1, l, s2) for letter l and s2 in A
			 */
			PredecessorSet x = predecessorFinder.find(letter);
			
			searchY(partition, a, x);
		}
	}
	
	/**
	 * finds set of predecessor states X and invokes next step
	 * considers return letters and splits linear and hierarchical predecessors
	 * 
	 * @param a target set of which X shall be computed
	 * @param partition partition of the states
	 * @param alphabet collection of return letters
	 * @param naiveSplit true iff naive split shall be used
	 */
	private void findXByReturn(TargetSet a, Partition partition,
			final Collection<LETTER> alphabet, final boolean naiveSplit) {
		if (naiveSplit) {
			findXByLinPred(a, partition, alphabet);
			findXByHierPred(a, partition, alphabet);
		}
		else {
			findXByDownStates(a, partition, alphabet);
		}
	}
	
	/**
	 * finds set of linear predecessor states X and invokes next step
	 * 
	 * @param a target set of which X shall be computed
	 * @param partition partition of the states
	 * @param alphabet collection of return letters
	 */
	private void findXByLinPred(TargetSet a, Partition partition,
			final Collection<LETTER> alphabet) {
		for (LETTER letter : alphabet) {
			
			// trivial split: every linear predecessor is different
			if (m_splitAllReturnsLin) {
				ReturnPredecessorLinSetFinder finder =
						new ReturnPredecessorLinSetFinder(partition, a);
				PredecessorSet x = finder.find(letter);
				Iterator<STATE> iterator = x.iterator();
				while (iterator.hasNext()) {
					HashSet<STATE> hashSet =
							new HashSet<STATE>(computeHashSetCapacity(1));
					hashSet.add(iterator.next());
					PredecessorSet x2 = new PredecessorSet(hashSet);
					
					searchY(partition, a, x2);
				}
			}
			/*
			 * only linear predecessors with hierarchical predecessors
			 * from different equivalence classes are split
			 */
			else {
				/*
				 * maps equivalence class EC of hierarchical predecessors
				 * to set of linear predecessors
				 */
				HashMap<EquivalenceClass, HashSet<STATE>> ec2linSet =
						new HashMap<EquivalenceClass, HashSet<STATE>>();
				
				Iterator<STATE> iterator = a.iterator();
				while (iterator.hasNext()) {
					STATE state = iterator.next();
					Iterable<STATE> hierPreds =
							partition.hierPredIncoming(state, letter);
					for (STATE hier : hierPreds) {
						EquivalenceClass ec =
								partition.getEquivalenceClass(hier);
						HashSet<STATE> linSet = ec2linSet.get(ec);
						if (linSet == null) {
							linSet = new HashSet<STATE>();
							ec2linSet.put(ec, linSet);
						}
						for (STATE pred : partition.linPredIncoming(
								state, hier, letter))
						linSet.add(pred);
					}
				}
				
				/*
				 * for each equivalence class of hierarchical predecessors
				 * split the linear predecessors
				 */
				for (HashSet<STATE> set : ec2linSet.values()) {
					PredecessorSet x = new PredecessorSet(set);
					
					searchY(partition, a, x);
				}
			}
		}
	}
	
	/**
	 * finds set of hierarchical predecessor states X and invokes next step
	 * 
	 * @param a target set of which X shall be computed
	 * @param partition partition of the states
	 * @param alphabet collection of return letters
	 */
	private void findXByHierPred(TargetSet a, Partition partition,
			final Collection<LETTER> alphabet) {
		for (LETTER letter : alphabet) {
			
			// trivial split: every linear predecessor is different
			if (m_splitAllReturnsHier) {
				// find all hierarchical predecessors of the states in A
				Iterator<STATE> iterator = a.iterator();
				Collection<STATE> hierPreds = new HashSet<STATE>();
				while (iterator.hasNext()) {
					for (STATE pred : partition.hierPredIncoming(
							iterator.next(), letter)) {
						hierPreds.add(pred);
					}
				}
				
				for (STATE hier : hierPreds) {
					HashSet<STATE> hashSet =
							new HashSet<STATE>(computeHashSetCapacity(1));
					hashSet.add(hier);
					PredecessorSet x = new PredecessorSet(hashSet);
					
					searchY(partition, a, x);
				}
			}
			/*
			 * only hierarchical predecessors with linear predecessors
			 * from different equivalence classes are split
			 */
			else {
				// distinguish linear predecessors by equivalence classes
				HashMap<EquivalenceClass, HashSet<STATE>> ec2hierSet =
						new HashMap<EquivalenceClass, HashSet<STATE>>();
				Iterator<STATE> iterator = a.iterator();
				while (iterator.hasNext()) {
					STATE state = iterator.next();
					for (STATE hier : 
							partition.hierPredIncoming(state, letter)) {
						Iterable<STATE> linPreds =
								partition.linPredIncoming(state, hier, letter);
						for (STATE lin : linPreds) {
							EquivalenceClass ec =
									partition.getEquivalenceClass(lin);
							HashSet<STATE> set = ec2hierSet.get(ec);
							if (set == null) {
								set = new HashSet<STATE>();
								ec2hierSet.put(ec, set);
							}
							set.add(hier);
						}
					}
				}
				
				/*
				 * for each equivalence class of linear predecessors
				 * split hierarchical predecessors
				 */
				for (HashSet<STATE> set : ec2hierSet.values()) {
					PredecessorSet x = new PredecessorSet(set);
					
					searchY(partition, a, x);
				}
			}
		}
	}
	
	/**
	 * splits states which encode different histories in the run
	 * 
	 * distinguishes return transitions by the equivalence class of the
	 * hierarchical and linear predecessor and splits non-similar transitions
	 * 
	 * expensive method, only used to accomplish soundness in the end
	 * 
	 * @param a target set of which X shall be computed
	 * @param partition partition of the states
	 * @param alphabet collection of return letters
	 */
	private void findXByDownStates(TargetSet a, Partition partition,
									Collection<LETTER> alphabet) {
		for (LETTER letter : alphabet) {
			
			// maps hierarchical states to linear states to return transitions
			HashMap<EquivalenceClass,
				HashMap<EquivalenceClass, List<Set<ReturnTransition>>>>
					hier2lin2trans = new HashMap<EquivalenceClass,
					HashMap<EquivalenceClass, List<Set<ReturnTransition>>>>();
			
			Iterator<STATE> iterator = a.iterator();
			// for each successor state 'state' in A:
			while (iterator.hasNext()) {
				STATE state = iterator.next();
				
				// for each hierarchical predecessor 'hier' of 'state':
				for (STATE hier : partition.hierPredIncoming(state, letter)) {
					EquivalenceClass ecHier =
							partition.getEquivalenceClass(hier);
					
					HashMap<EquivalenceClass, List<Set<ReturnTransition>>>
							lin2trans = hier2lin2trans.get(ecHier);
					if (lin2trans == null) {
						lin2trans =  new HashMap<EquivalenceClass,
												List<Set<ReturnTransition>>>();
						hier2lin2trans.put(ecHier, lin2trans);
					}
					
					// for each linear predecessor 'lin' of 'state' and 'hier':
					for (STATE lin :
							partition.linPredIncoming(state, hier, letter)) {
						EquivalenceClass ecLin =
								partition.getEquivalenceClass(lin);
						
						// list of similar sets
						List<Set<ReturnTransition>> similarSetsList =
								lin2trans.get(ecLin);
						if (similarSetsList == null) {
							similarSetsList =
									new LinkedList<Set<ReturnTransition>>();
							lin2trans.put(ecLin, similarSetsList);
						}
						
						// return transition considered
						ReturnTransition transition =
								new ReturnTransition(lin, hier, state);
						
						// find fitting set of similar return transitions
						Set<ReturnTransition> similarSet =
								getSimilarSet(partition, transition,
										letter, similarSetsList);
						if (similarSet == null) {
							similarSet = new HashSet<ReturnTransition>();
							similarSetsList.add(similarSet);
						}
						
						similarSet.add(transition);
					}
				}
			}
			
			// split each set of similar states
			createAndSplitXByDownStates(a, partition, hier2lin2trans);
		}
	}
	
	/**
	 * finds the set of similar return transitions if possible
	 * 
	 * @param partition partition of the states
	 * @param transition return transition
	 * @param letter return letter
	 * @param similarSetsList list of similar sets
	 * @return set of similar return transitions if possible, else null
	 */
	private Set<ReturnTransition> getSimilarSet(
			Partition partition, ReturnTransition transition,
			LETTER letter, List<Set<ReturnTransition>> similarSetsList) {
		for (Set<ReturnTransition> result : similarSetsList) {
			boolean found = true;
			
			// compare with each transition in the set
			for (ReturnTransition trans : result) {
				if (! transition.isSimilar(partition, trans, letter)) {
					found = false;
					break;
				}
			}
			
			// check passed for all transitions in the set
			if (found) {
				return result;
			}
		}
		
		// no fitting set found
		return null;
	}
	
	/**
	 * creates predecessor sets and splits them
	 * 
	 * @param a target set of which X shall be computed
	 * @param partition partition of the states
	 * @param hier2lin2trans hash map with distinguished return transitions
	 */
	private void createAndSplitXByDownStates(
			TargetSet a, Partition partition,
			HashMap<EquivalenceClass, HashMap<EquivalenceClass,
				List<Set<ReturnTransition>>>> hier2lin2trans) {
		for (HashMap<EquivalenceClass, List<Set<ReturnTransition>>> lin2trans :
				hier2lin2trans.values()) {
			for (List<Set<ReturnTransition>> similarSetsList :
					lin2trans.values()) {
				// for each set of similar states perform a split
				for (Set<ReturnTransition> similarSet : similarSetsList) {
					// set up linear and hierarchical predecessor sets
					int size = computeHashSetCapacity(similarSet.size());
					HashSet<STATE> lins = new HashSet<STATE>(size);
					HashSet<STATE> hiers = new HashSet<STATE>(size);
					for (ReturnTransition trans : similarSet) {
						lins.add(trans.getLin());
						hiers.add(trans.getHier());
					}
					
					// split similar linear predecessors
					PredecessorSet x = new PredecessorSet(lins);
					searchY(partition, a, x);
					
					// split similar hierarchical predecessors
					x = new PredecessorSet(hiers);
					searchY(partition, a, x);
				}
			}
		}
	}
	
	/**
	 * split hierarchical predecessors of outgoing return transitions
	 *  
	 * @param a target set of which X shall be computed
	 * @param partition partition of the states
	 * @param alphabet collection of return letters
	 * @param predecessorFinder finds the predecessor set X
	 */
	private void findXByOutgoingReturn(TargetSet a, Partition partition,
			final Collection<LETTER> alphabet,
			final ReturnSuccessorSetFinder predecessorFinder) {
		for (LETTER letter : alphabet) {
			/*
			 * X = predecessor set of A in hierarchical view
			 * = all states h with transition (s1, l, h, s2) for s1 in A
			 */
			PredecessorSet x = predecessorFinder.find(letter);
			
			searchY(partition, a, x);
		}
	}
	
	/**
	 * finds equivalence classes Y where intersection with X is non-empty
	 * and splits Y into 'Y \cap X' and 'Y \ X'
	 * 
	 * @param partition partition of the states
	 * @param a target set of which predecessor set X was computed
	 * @param x predecessor set X
	 */
	private void searchY(Partition partition, TargetSet a,
							PredecessorSet x) {
		assert (x.size() > 0);
		
		/*
		 * list of split equivalence classes
		 */
		LinkedList<EquivalenceClass> intersected =
				new LinkedList<EquivalenceClass>();
		
		// iteratively splits equivalence classes with elements from X
		Iterator<STATE> iterator = x.iterator();
		while (iterator.hasNext()) {
			STATE state = iterator.next();
			
			// find equivalence class Y
			EquivalenceClass y = partition.getEquivalenceClass(state);
			assert y != null;
			
			// move state from Y to Y \cap X
			y.moveState(state, intersected);
			assert y.getIntersection(intersected).contains(state);
			assert ! y.getCollection().contains(state);
		}
		
		// delete X
		x.delete();
		
		// split equivalence classes
		split(partition, a, intersected);
	}
	
	/**
	 * splits equivalence classes Y into 'Y \cap X' and 'Y \ X'
	 * 
	 * @param partition partition of the states
	 * @param a target set of which predecessor set X was computed
	 * @param intersected list of equivalence classes Y
	 */
	private void split(Partition partition, TargetSet a,
			LinkedList<EquivalenceClass> intersected) {
		/*
		 * for all equivalence classes Y not contained in W:
		 * put one or two of {'Y \cap X', 'Y \ X'} in W,
		 * but only if Y was split, i.e., 'Y \ X != {}'
		 */
		for (EquivalenceClass ec : intersected) {
			/*
			 * if Y is empty, then the intersection is not needed
			 * and the states can be restored 
			 */
			if (!ec.isEmpty()) {
				++m_splitsWithChange;
				
				// create new equivalence class
				EquivalenceClass intersection = ec.split(partition);
				
				/*
				 * if Y was in the target set, the split equivalence class
				 * must also be inserted
				 */
				if (ec.isInTargetSet()) {
					a.addEquivalenceClass(intersection);
				}
				
				// if Y was not in work list, put it and/or intersection there
				if (! ec.isInWorkList()) {
					assert (! intersection.isInWorkList());
					
					/*
					 * if deterministic:
					 * put the smaller equivalence class
					 * of {'Y \cap X', 'Y \ X'} in W
					 * NOTE: see note for m_onlyOneToWorkList
					 */
					if (m_onlyOneToWorkList) {
						if (ec.size() <= intersection.size()) {
							partition.addToWorkList(ec);
						}
						else {
							partition.addToWorkList(intersection);
						}
					}
					/*
					 * if non-deterministic:
					 * put both equivalence classes in the work list
					 * (necessary for correctness)
					 */
					else {
						partition.addToWorkList(ec);
						partition.addToWorkList(intersection);
					}
				}
				
				// add return successors to work list
				partition.addReturnsToWorkList(intersection);
			}
			else {
				++m_splitsWithoutChange;
			}
			
			// reset information about the intersection equivalence class
			ec.resetIntersection();
		}
	}
	
	/**
	 * puts all equivalence classes to the work list again
	 * 
	 * @param partition partition of the states
	 * @param naiveSplit true iff naive split is used next
	 */
	private void putAllToWorkList(Partition partition, boolean naiveSplit) {
		// only collect equivalence classes, which have been split lately
		if (naiveSplit) {
			for (EquivalenceClass ec : partition.getEquivalenceClasses()) {
				if (ec.wasSplitDuringSecondPhase()) {
					partition.addToWorkList(ec);
				}
			}
		}
		// only collect equivalence classes with incoming return transitions
		else {
			for (EquivalenceClass ec : partition.getEquivalenceClasses()) {
				if (ec.hasIncomingReturns(partition)) {
					partition.addToWorkList(ec);
				}
			}
		}
	}
	
	/**
	 * merges states from computed equivalence classes
	 * 
	 * @param partition partition of the states
	 */
	private NestedWordAutomaton<LETTER, STATE> merge() {
		// initialize result automaton
		NestedWordAutomaton<LETTER, STATE> result =
			new NestedWordAutomaton<LETTER, STATE>(
				m_operand.getInternalAlphabet(), m_operand.getCallAlphabet(),
				m_operand.getReturnAlphabet(), m_operand.getStateFactory());
		
		/*
		 * make sure every equivalence class has its representative
		 * if an initial state is in the class, then it is chosen
		 */
		m_Partition.setUpRepresentatives();
		
		// use representatives as states
		for (EquivalenceClass ec : m_Partition.getEquivalenceClasses()) {
			if (ec.size() > 0) {
				result.addState(ec.m_isInitial, ec.m_isFinal,
								ec.getRepresentative());
			}
		}
		
		// for all states add all outgoing transitions,
		// but now from representative to representative
		for (EquivalenceClass ec : m_Partition.getEquivalenceClasses()) {
			for (STATE state : ec.getCollection()) {
				STATE representative = m_Partition.getRepresentative(state);
				
				// internal successors
				for (LETTER l : m_operand.lettersInternal(state)) {
					for (STATE next : m_Partition.succInternal(state, l)) {
						result.addInternalTransition(
							representative,
							l,
							m_Partition.getRepresentative(next));
					}
				}
				
				// call successors
				for (LETTER l : m_operand.lettersCall(state)) {
					for (STATE next : m_Partition.succCall(state, l)) {
						result.addCallTransition(
							representative,
							l,
							m_Partition.getRepresentative(next));
					}
				}
				
				// return successors
				for (LETTER l : m_operand.lettersReturn(state)) {
					for (STATE hier : m_Partition.hierPred(state, l)) {
						for (STATE next : m_Partition.succReturn(state,
																hier, l)) {
							result.addReturnTransition(
								representative,
								m_Partition.getRepresentative(hier),
								l,
								m_Partition.getRepresentative(next));
						}
					}
				}
			}
		}
		
		return result;
	}
	
	/**
	 * computes the size of a hash set to avoid rehashing
	 * this is only sensible if the maximum size is already known
	 * Java standard sets the load factor to 0.75
	 * 
	 * @param size maximum number of elements in the hash set
	 * @return hash set size
	 */
	private int computeHashSetCapacity(int size) {
		return (int) (size / 0.75 + 1);
	}
	
	/**
	 * represents a return transition without the letter
	 */
	protected class ReturnTransition {
		private STATE m_lin, m_hier, m_succ;
		
		/**
		 * @param lin linear predecessor state
		 * @param hier hierarchical predecessor state
		 * @param succ successor state
		 */
		protected ReturnTransition(STATE lin, STATE hier, STATE succ) {
			this.m_lin = lin;
			this.m_hier = hier;
			this.m_succ = succ;
		}
		
		/**
		 * @return linear predecessor state
		 */
		public STATE getLin() {
			return m_lin;
		}
		
		/**
		 * @return hierarchical predecessor state
		 */
		public STATE getHier() {
			return m_hier;
		}
		
		/**
		 * @return successor state
		 */
		public STATE getSucc() {
			return m_succ;
		}
		
		/**
		 * finds out if return transitions are similar
		 * to do this, the down state rule is used
		 * 
		 * @param partition partition of the states
		 * @param transition return transition
		 * @param letter return letter
		 * @return true iff return transitions are similar
		 */
		private boolean isSimilar(Partition partition,
				ReturnTransition transition, LETTER letter) {
			// check first hierarchical states pair
			STATE lin = transition.m_lin;
			STATE hier = this.m_hier;
			EquivalenceClass ec =
					partition.getEquivalenceClass(transition.m_succ);
			if (! isSimilarHelper(partition, letter, lin, hier, ec)) {
				return false;
			}
			
			// check second hierarchical states pair
			lin = this.m_lin;
			hier = transition.m_hier;
			ec = partition.getEquivalenceClass(this.m_succ);
			return isSimilarHelper(partition, letter, lin, hier, ec);
		}
		
		/**
		 * helper for isSimilar()
		 * 
		 * @param partition partition of the states
		 * @param letter return letter
		 * @param lin linear predecessor of return transition
		 * @param hier hierarchical predecessor of return transition
		 * @param equivalenceClass equivalence class of successor state
		 * @return true iff return transitions are similar
		 */
		private boolean isSimilarHelper(Partition partition, LETTER letter,
				STATE lin, STATE hier, EquivalenceClass equivalenceClass) {
			if (m_doubleDecker.isDoubleDecker(lin, hier)) {
				if (!checkExistenceOfSimilarTransition(
						partition,
						partition.succReturn(lin, hier, letter),
						equivalenceClass)) {
					return false;
				}
			}
			
			return true;
		}
		
		/**
		 * checks if there is a successor state equivalent to the old one
		 * 
		 * @param partition partition of the states
		 * @param successors collection of possible successor states
		 * @param equivalenceClass equivalence class of successor state 
		 * @return true iff there is an equivalent successor state 
		 */
		private boolean checkExistenceOfSimilarTransition(
				Partition partition,
				Iterable<STATE> successors,
				EquivalenceClass equivalenceClass) {
			for (STATE candidate : successors) {
				if (partition.getEquivalenceClass(candidate).equals(
						equivalenceClass)) {
					return true;
			    }
			}
			
			return false;
		}
		
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			builder.append("(");
			builder.append(m_lin.toString());
			builder.append(", ");
			builder.append(m_hier.toString());
			builder.append(", ");
			builder.append(m_succ.toString());
			builder.append(")");
			return builder.toString();
		}
	}
	
	/**
	 * finds the predecessor set of a target set with respect to a letter
	 */
	abstract class APredecessorSetFinder {
		// partition object
		Partition m_partition;
		TargetSet m_a;
		
		/**
		 * @param partition partition of the states
		 * @param a target set
		 */
		public APredecessorSetFinder(Partition partition,
										TargetSet a) {
			this.m_partition = partition;
			this.m_a = a;
		}
		
		/**
		 * finds the predecessor set of A and adds it to X
		 * 
		 * @param letter letter
		 * @return predecessor set X
		 */
		protected PredecessorSet find(LETTER letter) {
			PredecessorSet x = new PredecessorSet();
			Iterator<STATE> iterator = m_a.iterator();
			while (iterator.hasNext()) {
				STATE state = iterator.next();
				addPred(state, letter, x);
			}
			return x;
		}
		
		/**
		 * adds predecessor states
		 * 
		 * @param state state
		 * @param letter letter
		 * @param x predecessor set
		 */
		protected void addPred(STATE state,
								LETTER letter, PredecessorSet x) {
			throw new AbstractMethodError();
		}
	}
	
	/**
	 * finds the predecessor set of a target set given an internal letter
	 */
	class InternalPredecessorSetFinder extends APredecessorSetFinder {
		/**
		 * @param partition partition of the states
		 * @param a target set
		 */
		public InternalPredecessorSetFinder(Partition partition,
											TargetSet a) {
			super(partition, a);
		}
		
		/**
		 * adds internal predecessor states
		 * 
		 * @param state state
		 * @param letter internal letter
		 * @param x predecessor set
		 */
		@Override
		protected void addPred(STATE state,
								LETTER letter, PredecessorSet x) {
			m_partition.addPredInternal(state, letter, x);
		}
	}
	
	/**
	 * finds the predecessor set of a target set given a call letter
	 */
	class CallPredecessorSetFinder extends APredecessorSetFinder {
		/**
		 * @param partition partition of the states
		 * @param a target set
		 */
		public CallPredecessorSetFinder(Partition partition,
										TargetSet a) {
			super(partition, a);
		}
		
		/**
		 * adds call predecessor states
		 * 
		 * @param state state
		 * @param letter call letter
		 * @param x predecessor set
		 */
		@Override
		protected void addPred(STATE state,
								LETTER letter, PredecessorSet x) {
			m_partition.addPredCall(state, letter, x);
		}
	}
	
	/**
	 * finds the linear predecessor set of a target set given a return letter
	 */
	class ReturnPredecessorLinSetFinder extends APredecessorSetFinder {
		/**
		 * @param partition partition of the states
		 * @param a target set
		 */
		public ReturnPredecessorLinSetFinder(Partition partition,
											TargetSet a) {
			super(partition, a);
		}
		
		/**
		 * adds linear return predecessor states
		 * 
		 * @param state state
		 * @param letter return letter
		 * @param x predecessor set
		 */
		@Override
		protected void addPred(STATE state,
								LETTER letter, PredecessorSet x) {
			for (STATE hier : m_partition.hierPredIncoming(state, letter)) {
				m_partition.addPredReturnLin(state, letter, hier, x);
			}
		}
	}
	
	/**
	 * finds the linear predecessor set of a target set given a return letter
	 * and the hierarchical predecessor
	 */
	class ReturnPredecessorLinSetGivenHierFinder
			extends APredecessorSetFinder {
		// hierarchical predecessor
		STATE m_hier;
		
		/**
		 * @param partition partition of the states
		 * @param a target set
		 * @param hier hierarchical predecessor
		 */
		public ReturnPredecessorLinSetGivenHierFinder(Partition partition,
											TargetSet a, STATE hier) {
			super(partition, a);
			this.m_hier = hier;
		}
		
		/**
		 * adds linear return predecessor states
		 * 
		 * @param state state
		 * @param letter return letter
		 * @param x predecessor set
		 */
		@Override
		protected void addPred(STATE state,
								LETTER letter, PredecessorSet x) {
			m_partition.addPredReturnLin(state, letter, m_hier, x);
		}
	}
	
	/**
	 * finds the successor set of a target set given a return letter
	 */
	class ReturnSuccessorSetFinder extends APredecessorSetFinder {
		/**
		 * @param partition partition of the states
		 * @param a target set
		 */
		public ReturnSuccessorSetFinder(Partition partition,
											TargetSet a) {
			super(partition, a);
		}
		
		/**
		 * adds return successor states
		 * 
		 * @param state state
		 * @param letter return letter
		 * @param x successor set
		 */
		@Override
		protected void addPred(STATE state,
								LETTER letter, PredecessorSet x) {
			m_partition.addSuccReturnHier(state, letter, x);
		}
	}
	
	/**
	 * equivalence class for the merge method
	 * contains the collection of states
	 * = equivalence class and information if the equivalence class is
	 * also contained in work list
	 */
	public class EquivalenceClass {
		// collection with equivalence class's elements
		private Set<STATE> m_collection;
		// equivalence class is contained in work list
		private boolean m_inW;
		// equivalence class is contained in target set
		private boolean m_inA;
		// representative. Note that this is a state of the resulting NWA.
		private STATE m_representative;
		// equivalence class contains final/initial states
		private boolean m_isFinal, m_isInitial;
		// intersection collection during the splitting
		private HashSet<STATE> m_intersection;
		// individual ID
		private final int m_id;
		// incoming returns
		private boolean m_incomingReturns;
		// split occurred
		private boolean m_wasSplit;
		
		/**
		 * constructor for initial equivalence classes
		 * 
		 * @param collection collection of states for the equivalence class
		 * 			must contain at least one element
		 * @param isFinal true iff equivalence states are final
		 */
		public EquivalenceClass(Collection<STATE> collection,
				boolean isFinal) {
			this(collection, isFinal, true);
		}
		
		/**
		 * private constructor for initial equivalence classes
		 * 
		 * @param collection collection of states for the equivalence class
		 * 			must contain at least one element
		 * @param isFinal true iff equivalence states are final
		 * @param inW true iff equivalence class shall be put in work list
		 */
		public EquivalenceClass(Collection<STATE> collection, boolean isFinal,
				boolean inW) {
			this(isFinal, inW, false);
			assert (collection.size() > 0);
			
			if (collection instanceof Set) {
				this.m_collection = (Set<STATE>) collection;
			}
			else {
				this.m_collection = new HashSet<STATE>(computeHashSetCapacity(
														collection.size()));
				for (STATE state : collection) {
					this.m_collection.add(state);
				}
			}
		}
		
		/**
		 * private constructor for minor fields
		 * 
		 * @param isFinal true iff states are final
		 * @param inW equivalence class is in work list
		 * @param inA equivalence class is in target set
		 */
		private EquivalenceClass(boolean isFinal, boolean inW, boolean inA) {
			this.m_isFinal = isFinal;
			this.m_inW = inW;
			this.m_inA = inA;
			// true because then the real result is computed later
			this.m_wasSplit = true;
			// initially intersection is null
			this.m_intersection = null;
			this.m_id = MinimizeSevpa.equivalenceClassId++;
		}
		
		/**
		 * @return true iff two equivalence classes are the same objects
		 */
		@SuppressWarnings("unchecked")
		@Override
		public boolean equals(Object o) {
			if (o instanceof MinimizeSevpa.EquivalenceClass) {
				return this.m_id == ((EquivalenceClass)o).m_id;
			}
			return false;
		}
		
		/**
		 * @return hash code
		 */
		@Override
		public int hashCode() {
			return this.m_id;
		}
		
		/**
		 * @return collection of states
		 */
		Collection<STATE> getCollection() {
			return m_collection;
		}
		
		/**
		 * @return true iff equivalence class is in work list
		 */
		boolean isInWorkList() {
			return m_inW;
		}
		
		/**
		 * should only be called by the partition object
		 * 
		 * @param inW true iff equivalence class is now in the work list
		 */
		private void setInWorkList(boolean inW) {
			this.m_inW = inW;
		}
		
		/**
		 * @return true iff equivalence class is in target set
		 */
		boolean isInTargetSet() {
			return m_inA;
		}
		
		/**
		 * @param inA true iff equivalence class is in target set
		 */
		void setInTargetSet(boolean inA) {
			this.m_inA = inA;
		}
		
		/**
		 * @return true iff states are final
		 */
		boolean isFinal() {
			return m_isFinal;
		}
		
		/**
		 * setter
		 */
		void setWasSplit() {
			this.m_wasSplit = true;
		}
		
		/**
		 * @param intersected collection of intersected equivalence classes
		 * 			needed to remember new intersections
		 * @return collection of states in the intersection
		 */
		Collection<STATE> getIntersection(
							Collection<EquivalenceClass> intersected) {
			/*
			 * if equivalence class was split the first time during loop,
			 * create a new collection for intersection
			 */
			if (m_intersection == null) {
				m_intersection = new HashSet<STATE>();
				intersected.add(this);
			}
			return m_intersection;
		}
		
		/**
		 * resets the intersection equivalence class to null
		 */
		void resetIntersection() {
			// if collection is empty, intersection can be restored
			if (m_collection.isEmpty()) {
				m_collection = m_intersection;
			}
			m_intersection = null;
		}
		
		/**
		 * @return representative state (initial if possible)
		 */
		STATE getRepresentative() {
			return m_representative;
		}
		
		/**
		 * @return size of the collection
		 */
		int size() {
			return m_collection.size();
		}
		
		/**
		 * @return true iff collection is empty
		 */
		boolean isEmpty() {
			return m_collection.size() == 0;
		}
		
		/**
		 * @param state state to add
		 * @return true iff state was not contained before
		 */
		boolean add(STATE state) {
			return m_collection.add(state);
		}
		
		/**
		 * moves a state from one equivalence class to intersection
		 * 
		 * @param state state to move
		 * @param intersected collection of intersected equivalence classes
		 * 			remembered for later computations
		 */
		public void moveState(STATE state,
								Collection<EquivalenceClass> intersected) {
			assert m_collection.contains(state);
			m_collection.remove(state);
			getIntersection(intersected).add(state);
		}
		
		/**
		 * sets the equivalence class as initial
		 */
		void markAsInitial() {
			m_isInitial = true;
		}
		
		/**
		 * creates new state as merge of all states in this equivalence class
		 */
		void setUpRepresentative() {
			m_representative = m_StateFactoryConstruction.minimize(m_collection);
		}
		
		/**
		 * splits an equivalence class into two
		 * 
		 * @param partition partition of the states
		 * @return split equivalence class
		 */
		public EquivalenceClass split(Partition partition) {
			EquivalenceClass intersection =
					new EquivalenceClass(getIntersection(null), isFinal(),
														isInWorkList());
			partition.addEquivalenceClass(intersection);
			m_wasSplit = true;
						
			// refresh state mapping
			for (STATE state : intersection.getCollection()) {
				partition.setEquivalenceClass(state, intersection);
			}
			
			return intersection;
		}
		
		/**
		 * NOTE: is only correct, since the method is always called with
		 * wasSplitDuringSecondPhase() alternately and only at certain points
		 * 
		 * @param partition partition of the states
		 * @return true iff there are states with incoming return transitions
		 */
		boolean hasIncomingReturns(Partition partition) {
			// if a split occurred, the result has to be recomputed
			if (m_wasSplit) {
				m_wasSplit = false;
				
				m_incomingReturns = false;
				for (STATE state : m_collection) {
					if (partition.hasIncomingReturns(state)) {
						m_incomingReturns = true;
						break;
					}
				}
			}
			
			return m_incomingReturns;
		}
		
		/**
		 * NOTE: is only correct, since the method is always called with
		 * hasIncomingReturns() alternately and only at certain points
		 * 
		 * @return true iff equivalence class was split during second phase
		 */
		boolean wasSplitDuringSecondPhase() {
			if (m_wasSplit) {
				m_wasSplit = false;
				return true;
			}
			return false;
		}
		
		/**
		 * @return string representation
		 */
		@Override
		public String toString() {
			StringBuilder builder = new StringBuilder();
			
			builder.append("[");
			for (STATE state : m_collection) {
				builder.append(state.toString());
				builder.append(", ");
			}
			if (builder.length() > 2) {
				builder.delete(builder.length() - 2, builder.length());
			}
			builder.append("]");
			if (m_isFinal) {
				builder.append("f");
			}
			if (m_inW) {
				builder.append("w");
			}
			
			return builder.toString();
		}
	}
	
	/**
	 * collection of equivalence classes and a mapping
	 * 'state -> equivalence class' for fast access
	 */
	public class Partition {
		// original nested word automaton
		private INestedWordAutomatonOldApi<LETTER, STATE> m_parentOperand;
		// equivalence classes
		private LinkedList<EquivalenceClass> m_equivalenceClasses;
		// work list (W) with equivalence classes still to refine
		private WorkList m_workList;
		// mapping 'state -> equivalence class'
		private HashMap<STATE,EquivalenceClass> m_mapState2EquivalenceClass;
		
		/**
		 * @param operand original nested word automaton
		 * @param states number of states (avoids rehashing)
		 */
		Partition(INestedWordAutomatonOldApi<LETTER, STATE> operand, int states) {
			this.m_parentOperand = operand;
			this.m_equivalenceClasses = new LinkedList<EquivalenceClass>();
			this.m_workList = new WorkList(m_parentOperand.size() / 2);
			this.m_mapState2EquivalenceClass =
				new HashMap<STATE, EquivalenceClass>(
									computeHashSetCapacity(states));
		}
		
		public void splitOccurred(EquivalenceClass ec, EquivalenceClass cap) {
			ec.setWasSplit();
			cap.setWasSplit();
		}
		
		/**
		 * for each equivalence class merges the states and sets the resulting
		 * state as the representative of the equivalence class
		 */
		void setUpRepresentatives() {
			/*
			 * if an equivalence class contains an initial state,
			 * the whole equivalence class should be initial
			 */
			for (STATE state : m_parentOperand.getInitialStates()) {
				EquivalenceClass ec = m_mapState2EquivalenceClass.get(state);
				// null check needed in case state was removed beforehand
				if (ec != null) {
					assert (ec.size() > 0);
					ec.markAsInitial();
				}
			}
			
			// inserts a new state with sensible naming
			for (EquivalenceClass ec : m_equivalenceClasses) {
				ec.setUpRepresentative();
			}
		}
		
		/**
		 * @return all equivalence classes
		 */
		LinkedList<EquivalenceClass> getEquivalenceClasses() {
			return m_equivalenceClasses;
		}
		
		/**
		 * @param equivalenceClass new equivalence class
		 */
		void addEquivalenceClass(EquivalenceClass equivalenceClass) {
			m_equivalenceClasses.add(equivalenceClass);
			if (equivalenceClass.isInWorkList()) {
				m_workList.add(equivalenceClass);
			}
			for (STATE state : equivalenceClass.getCollection()) {
				m_mapState2EquivalenceClass.put(state, equivalenceClass);
			}
		}
		
		/**
		 * @param state state in equivalence class
		 * @return equivalence class containing the state
		 */
		EquivalenceClass getEquivalenceClass(STATE state) {
			return m_mapState2EquivalenceClass.get(state);
		}
		
		/**
		 * @param state state in equivalence class
		 * @return representative of equivalence class containing the state
		 */
		STATE getRepresentative(STATE state) {
			return getEquivalenceClass(state).getRepresentative();
		}
		
		/**
		 * @param state state for equivalence class
		 * @param equivalenceClass 
		 */
		protected void setEquivalenceClass(STATE state, 
									EquivalenceClass equivalenceClass) {
			m_mapState2EquivalenceClass.put(state, equivalenceClass);
		}
		
		/**
		 * @return true iff work list is empty
		 */
		boolean workListIsEmpty() {
			return m_workList.isEmpty();
		}
		
		/**
		 * @param equivalenceClass equivalence class for the work list
		 */
		void addToWorkList(EquivalenceClass equivalenceClass) {
			m_workList.add(equivalenceClass);
			equivalenceClass.setInWorkList(true);
		}
		
		/**
		 * adds all equivalence classes to the work list,
		 * of which a state is reached from a newly outgoing return
		 * 
		 * @param equivalenceClass equivalence class with states from
		 * 			predecessor set of which return successors are to be
		 * 			added to the work list
		 */
		void addReturnsToWorkList(EquivalenceClass equivalenceClass) {
			Collection<STATE> collection = equivalenceClass.getCollection();
			Iterator<STATE> iterator = collection.iterator();
			while (iterator.hasNext()) {
				STATE state = iterator.next();
				
				// successors via linear edge
				for (LETTER letter : m_parentOperand.lettersReturn(state)) {
					Iterable<STATE> hierPreds = hierPred(state, letter);
					for (STATE hier : hierPreds) {
						Iterable<STATE> succStates =
								succReturn(state, hier, letter);
						for (STATE succ : succStates) { 
							EquivalenceClass ec = getEquivalenceClass(succ);
							if (! ec.isInWorkList()) {
								addToWorkList(ec);
							}
						}
					}
				}
				
				// successors via hierarchical edge
				if (m_noStatesRemoved) {
					for (LETTER letter :
							m_parentOperand.lettersReturnSummary(state)) {
						Iterable<SummaryReturnTransition<LETTER, STATE>>
							succs =
								m_parentOperand.returnSummarySuccessor(
										letter, state);
						for (SummaryReturnTransition<LETTER, STATE> t :
								succs) {
							EquivalenceClass ec = getEquivalenceClass(
									t.getSucc());
							if (! ec.isInWorkList()) {
								addToWorkList(ec);
							}
						}
					}
				}
				else {
					for (LETTER letter :
							m_parentOperand.lettersReturnSummary(state)) {
						Iterable<SummaryReturnTransition<LETTER, STATE>>
							succs =
								m_parentOperand.returnSummarySuccessor(
										letter, state);
						for (SummaryReturnTransition<LETTER, STATE> t :
								succs) {
							EquivalenceClass ec = getEquivalenceClass(
									t.getSucc());
							if (ec != null) {
								if (! ec.isInWorkList()) {
									addToWorkList(ec);
								}
							}
						}
					}
				}
			}
		}
		
		/**
		 * @return next equivalence class in the work list
		 */
		EquivalenceClass popFromWorkList() {
			EquivalenceClass ec = m_workList.pop();
			ec.setInWorkList(false);
			return ec;
		}
		
		/**
		 * @param state state
		 * @return true iff state has an incoming return transition
		 */
		public boolean hasIncomingReturns(STATE state) {
			return m_parentOperand.lettersReturnIncoming(state).size() > 0;
		}
		
		/**
		 * finds successor states
		 * (for avoiding states that have already been removed)
		 * 
		 * @param states set of target states
		 */
		private Collection<STATE> neighbors(Iterable<STATE> states) {
			LinkedList<STATE> result = new LinkedList<STATE>();
			for (STATE s : states) {
				if (m_mapState2EquivalenceClass.get(s) != null) {
					result.add(s);
				}
			}
			return result;
		}
		/**
		 * finds successor states more efficiently if no states were removed
		 * 
		 * NOTE: method exists if return value of NestedWordAutomaton
		 * is changed to Iterable<STATE>, so one can create a list here
		 * 
		 * @param states set of target states
		 */
		private Iterable<STATE> neighborsEfficient(
				Iterable<STATE> states) {
			return states;
		}
		Iterable<STATE> succInternal(STATE state, LETTER letter) {
			if (m_noStatesRemoved) {
				return neighborsEfficient(
								m_parentOperand.succInternal(state, letter));
			}
			else {
				return neighbors(m_parentOperand.succInternal(state, letter));
			}
		}
		Iterable<STATE> succCall(STATE state, LETTER letter) {
			if (m_noStatesRemoved) {
				return neighborsEfficient(m_parentOperand.succCall(state,
																	letter));
			}
			else {
				return neighbors(m_parentOperand.succCall(state, letter));
			}
		}
		Iterable<STATE> succReturn(STATE state, STATE hier, LETTER letter) {
			if (m_noStatesRemoved) {
				return neighborsEfficient(
								m_parentOperand.succReturn(state, hier,
															letter));
			}
			else {
				return neighbors(m_parentOperand.succReturn(state, hier,
															letter));
			}
		}
		Iterable<STATE> hierPred(STATE state, LETTER letter) {
			if (m_noStatesRemoved) {
				return neighborsEfficient(m_parentOperand.hierPred(state,
																	letter));
			}
			else {
				return neighbors(m_parentOperand.hierPred(state, letter));
			}
		}
		Iterable<STATE> linPredIncoming(STATE state, STATE hier,
											LETTER letter) {
			if (m_noStatesRemoved) {
				return neighborsEfficient(m_parentOperand.predReturnLin(
						state, letter, hier));
			}
			else {
				return neighbors(m_parentOperand.predReturnLin(
						state, letter, hier));
			}
		}
		Iterable<STATE> hierPredIncoming(STATE state, LETTER letter) {
			if (m_noStatesRemoved) {
				return neighborsEfficient(m_parentOperand.predReturnHier(
						state, letter));
			}
			else {
				return neighbors(m_parentOperand.predReturnHier(state,
																letter));
			}
		}
		
		/**
		 * finds predecessor states and directly adds elements to the set
		 * 
		 * @param states target states of edges
		 * @param x predecessor set
		 */
		private void addNeighbors(Iterable<STATE> states,
				PredecessorSet x) {
			for (STATE s : states) {
				if (m_mapState2EquivalenceClass.get(s) != null) {
					x.add(s);
				}
			}
		}
		/**
		 * finds predecessor states and directly adds elements to the set
		 * more efficient variant if no states were removed
		 * 
		 * @param states target states of edges
		 * @param x predecessor set
		 */
		private void addNeighborsEfficient(Iterable<STATE> states,
				PredecessorSet x) {
			for (STATE s : states) {
				x.add(s);
			}
		}
		void addPredInternal(STATE state, LETTER letter, PredecessorSet x) {
			if (m_noStatesRemoved) {
				addNeighborsEfficient(m_parentOperand.predInternal(state,
																letter), x);
			}
			else {
				addNeighbors(m_parentOperand.predInternal(state, letter), x);
			}
		}
		void addPredCall(STATE state, LETTER letter, PredecessorSet x) {
			if (m_noStatesRemoved) {
				addNeighborsEfficient(m_parentOperand.predCall(state, letter),
										x);
			}
			else {
				addNeighbors(m_parentOperand.predCall(state, letter), x);
			}
		}
		void addPredReturnLin(STATE state, LETTER letter,
				STATE hier, PredecessorSet x) {
			if (m_noStatesRemoved) {
				addNeighborsEfficient(
						m_parentOperand.predReturnLin(state, letter, hier), x);
			}
			else {
				addNeighbors(
						m_parentOperand.predReturnLin(state, letter, hier), x);
			}
		}
		void addPredReturnHier(STATE state, LETTER letter, PredecessorSet x) {
			if (m_noStatesRemoved) {
				addNeighborsEfficient(
						m_parentOperand.predReturnHier(state, letter), x);
			}
			else {
				addNeighbors(m_parentOperand.predReturnHier(state, letter), x);
			}
		}
		void addSuccReturnHier(STATE state, LETTER letter, PredecessorSet x) {
			HashSet<STATE> hierSet = new HashSet<STATE>();
			for (STATE hier : m_parentOperand.hierPred(state, letter)) {
				hierSet.add(hier);
			}
			
			if (m_noStatesRemoved) {
				addNeighborsEfficient(hierSet, x);
			}
			else {
				addNeighbors(hierSet, x);
			}
		}
		
		/**
		 * @return string representation
		 */
		@Override
		public String toString() {
			StringBuilder builder = new StringBuilder();
			
			builder.append("{ ");
			for (EquivalenceClass ec : m_equivalenceClasses) {
				builder.append(ec.toString());
				builder.append(",\n");
			}
			if (builder.length() > 2) {
				builder.delete(builder.length() - 2, builder.length());
			}
			builder.append(" }");
			
			return builder.toString();
		}
	}
	
	/**
	 * target set 'A' of which the predecessor set is computed
	 * in order to get valid results, the original equivalence class A has to
	 * be remembered somehow, since it can be destroyed during the splitting
	 * 
	 * NOTE: iterator must be used in 'hasNext()-loop'
	 * and with no change to the equivalence classes during iteration
	 */
	class TargetSet {
		LinkedList<EquivalenceClass> m_equivalenceClasses;
		
		/**
		 * @param firstEquivalenceClass first equivalence class
		 * 			(must not be null)
		 */
		public TargetSet(EquivalenceClass firstEquivalenceClass) {
			assert firstEquivalenceClass != null;
			this.m_equivalenceClasses = new LinkedList<EquivalenceClass>();
			this.m_equivalenceClasses.add(firstEquivalenceClass);
			firstEquivalenceClass.setInTargetSet(true);
		}
		
		/**
		 * @return iterator over all states
		 * 
		 * NOTE: is only correct if used in 'hasNext()-loop',
		 * but therefore needs less overhead
		 * NOTE: is only correct if no further equivalence classes are added
		 * during iteration
		 */
		Iterator<STATE> iterator() {
			return new Iterator<STATE>() {
				private ListIterator<EquivalenceClass> listIterator =
										m_equivalenceClasses.listIterator();
				private Iterator<STATE> equivalenceClassIterator = null;
				private STATE next = initialize();
				
				@Override
				public boolean hasNext() {
					return next != null;
				}
				
				@Override
				public STATE next() {
					assert next != null;
					
					// next element already computed before
					STATE result = next;
					
					// compute next element
					computeNext();
					
					return result;
				}
				
				private STATE initialize() {
					equivalenceClassIterator =
							listIterator.next().getCollection().iterator();
					computeNext();
					return next;
				}
				
				private void computeNext() {
					if (equivalenceClassIterator.hasNext()) {
						next = equivalenceClassIterator.next();
					}
					else {
						while (listIterator.hasNext()) {
							equivalenceClassIterator =
									listIterator.next().getCollection().
															iterator();
							
							if (equivalenceClassIterator.hasNext()) {
								next = equivalenceClassIterator.next();
								return;
							}
						}
						
						next = null;
					}
				}
				
				@Override
				public void remove() {
					throw new UnsupportedOperationException();
				}
			};
		}
		
		/**
		 * @param equivalenceClass new equivalence class
		 */
		void addEquivalenceClass(EquivalenceClass equivalenceClass) {
			m_equivalenceClasses.add(equivalenceClass);
			equivalenceClass.setInTargetSet(true);
		}
		
		/**
		 * delete object and reset flag in equivalence class objects
		 */
		void delete() {
			for (EquivalenceClass ec : m_equivalenceClasses) {
				ec.setInTargetSet(false);
			}
			
			m_equivalenceClasses = null;
		}
		
		/**
		 * @return true iff equivalence class is empty
		 */
		boolean isEmpty() {
			return ! iterator().hasNext();
		}
		
		/**
		 * @return string representation
		 */
		@Override
		public String toString() {
			StringBuilder builder = new StringBuilder();
			builder.append("{");
			
			for (EquivalenceClass ec : m_equivalenceClasses) {
				builder.append(ec.toString());
				builder.append("\n");
			}
			builder.append("}");
			
			return builder.toString();
		}
	}
	
	/**
	 * work list which is roughly sorted by size (small < big)
	 * 
	 * NOTE: ordering is not assured, since equivalence classes often change
	 * size, which results in reordering, which again is not efficient,
	 * since PriorityQueue does not offer a decreaseKey() method
	 */
	class WorkList {
		PriorityQueue<EquivalenceClass> m_queue;
		
		/**
		 * constructor
		 */
		public WorkList(int size) {
			if (size == 0) {
				// special case where automaton has no reachable states
				size = 1;
			}
			this.m_queue = new PriorityQueue<EquivalenceClass>(size,
					new Comparator<EquivalenceClass>() {
						@Override
						public int compare(EquivalenceClass ec1,
								EquivalenceClass ec2) {
							return ec1.size() - ec2.size();
						}
					});
		}
		
		/**
		 * @param equivalenceClass equivalence class to add
		 */
		public void add(EquivalenceClass equivalenceClass) {
			assert (! m_queue.contains(equivalenceClass));
			m_queue.add(equivalenceClass);
		}
		
		/**
		 * @return next equivalence class according to the ordering
		 */
		public EquivalenceClass pop() {
			return m_queue.poll();
		}
		
		/**
		 * @return true iff work list is empty
		 */
		public boolean isEmpty() {
			return m_queue.isEmpty();
		}
		
		/**
		 * @return string representation
		 */
		@Override
		public String toString() {
			StringBuilder builder = new StringBuilder();
			
			builder.append("{");
			builder.append(m_queue.toString());
			builder.append("}");
			
			return builder.toString();
		}
	}
	
	/**
	 * representation of the collection of predecessor states
	 */
	class PredecessorSet {
		HashSet<STATE> m_collection;
		
		/**
		 * constructor
		 */
		public PredecessorSet() {
			this (new HashSet<STATE>());
		}
		
		/**
		 * @param hashSet hash set of states
		 */
		public PredecessorSet(HashSet<STATE> hashSet) {
			assert hashSet != null;
			this.m_collection = hashSet;
		}
		
		/**
		 * @return iterator for the collection
		 */
		Iterator<STATE> iterator() {
			return m_collection.iterator();
		}
		
		/**
		 * @param state state to add
		 */
		void add(STATE state) {
			m_collection.add(state);
		}
		
		/**
		 * melds two predecessor sets
		 * 
		 * @param other other predecessor set
		 */
		void meld(PredecessorSet other) {
			m_collection.addAll(other.m_collection);
		}
		
		/**
		 * @return size of the collection
		 */
		int size() {
			return m_collection.size();
		}
		
		/**
		 * @return true iff collection is empty
		 */
		boolean isEmpty() {
			return m_collection.isEmpty();
		}
		
		/**
		 * deletes all stored elements
		 */
		void delete() {
			m_collection = null;
		}
		
		/**
		 * @return string representation
		 */
		@Override
		public String toString() {
			return m_collection.toString();
		}
	}
	
	/**
	 * intermediate data storage for states reachable in the automaton
	 * already distinguishes between final and non-final states
	 * either has a copy of the states or only knows the removed states
	 */
	class StatesContainer {
		// original nested word automaton
		private INestedWordAutomatonOldApi<LETTER, STATE> m_parentOperand;
		// states
		private HashSet<STATE> m_finals;
		private HashSet<STATE> m_nonfinals;
		// true iff a real copy is made
		private StatesContainerMode m_mode;
		
		/**
		 * constructor
		 */
		StatesContainer(INestedWordAutomatonOldApi<LETTER, STATE> operand) {
			this.m_parentOperand = operand;
			if (m_removeUnreachables) {
				this.m_mode = StatesContainerMode.makeCopy;
			}
			else if (m_removeDeadEnds) {
				this.m_mode = StatesContainerMode.saveRemoved;
			}
			else {
				this.m_mode = StatesContainerMode.none;
			}
			
			switch (this.m_mode) {
				// if unreachable states shall be removed, make a copy
				case makeCopy :
					this.m_finals =
					new HashSet<STATE>(computeHashSetCapacity(
							m_parentOperand.getFinalStates().size()));
					this.m_nonfinals =
						new HashSet<STATE>(computeHashSetCapacity(
							m_parentOperand.size() -
							m_parentOperand.getFinalStates().size()));
					break;
				/*
				 * if only dead ends shall be removed,
				 * only remember removed states
				 */
				case saveRemoved :
					this.m_finals = new HashSet<STATE>();
					this.m_nonfinals = new HashSet<STATE>();
					break;
				// else the sets are not needed
				case none :
					this.m_finals = null;
					this.m_nonfinals = null;
					break;
				default :
					assert false;
			}
		}
		
		/**
		 * fast notice of trivial automaton
		 * 
		 * @return true iff there are final states
		 */
		public boolean hasFinals() {
			switch (m_mode) {
				case makeCopy :
					return m_finals.size() > 0;
				case saveRemoved :
					return (
						(m_parentOperand.getFinalStates().size() -
							m_finals.size()) > 0);
				case none :
					return (m_parentOperand.getFinalStates().size() > 0);
				default :
					assert false;
					return false;
			}
		}
		
		/**
		 * passes the copied set of states
		 * only used in case when states were copied
		 * 
		 * @return non-final states
		 */
		HashSet<STATE> getNonfinals() {
			assert m_mode == StatesContainerMode.makeCopy;
			return m_nonfinals;
		}
		
		/**
		 * @return iterator of non-final states
		 */
		Iterator<STATE> getNonfinalsIterator() {
			switch (m_mode) {
				case makeCopy :
					return m_nonfinals.iterator();
				case saveRemoved :
					return new Iterator<STATE>() {
						private Iterator<STATE> iterator =
								m_parentOperand.getStates().iterator();
						private STATE next = computeNext();
						
						@Override
						public boolean hasNext() {
							return next != null;
						}
						
						@Override
						public STATE next() {
							assert next != null;
							
							// next element already computed before
							STATE result = next;
							
							// compute next element
							next = computeNext();
							
							return result;
						}
						
						private STATE computeNext() {
							STATE nextFound;
							while (iterator.hasNext()) {
								nextFound = iterator.next();
								if (! m_parentOperand.isFinal(nextFound) &&
										contains(nextFound)) {
									return nextFound;
								}
							}
							return null;
						}
					
						@Override
						public void remove() {
							throw new UnsupportedOperationException();
						}
					};
				// this case is possible to solve, but not needed
				case none :
					assert false;
					return null;
				default : 
					assert false;
					return null;
			}
		}
		
		/**
		 * passes the copied set of states
		 * only used in case when states were copied
		 * 
		 * @return final states
		 */
		HashSet<STATE> getFinals() {
			assert m_mode == StatesContainerMode.makeCopy;
			return m_finals;
		}
		
		/**
		 * @return iterator of final states
		 * 
		 * NOTE: is only correct if used in 'hasNext()-loop',
		 * but therefore needs less overhead
		 * NOTE: is only correct if no further equivalence classes are added
		 * during iteration
		 */
		Iterator<STATE> getFinalsIterator() {
			switch (m_mode) {
			case makeCopy :
				return m_finals.iterator();
			case saveRemoved :
				return new Iterator<STATE>() {
					private Iterator<STATE> iterator =
							m_parentOperand.getFinalStates().iterator();
					private STATE next = computeNext();
					
					@Override
					public boolean hasNext() {
						return next != null;
					}
					
					@Override
					public STATE next() {
						assert next != null;
						
						// next element already computed before
						STATE result = next;
						
						// compute next element
						next = computeNext();
						
						return result;
					}
					
					private STATE computeNext() {
						STATE nextFound;
						while (iterator.hasNext()) {
							nextFound = iterator.next();
							if (contains(nextFound)) {
								return nextFound;
							}
						}
						return null;
					}
				
					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
				};
			case none :
				return m_parentOperand.getFinalStates().iterator();
			default : 
				assert false;
				return null;
			}
		}
		
		/**
		 * number of states removed (only used for hash set initialization)
		 * 
		 * @param finals true iff number of final states is needed
		 * 				false iff number of non-final states is needed
		 * @return number of removed states
		 */
		int getRemovedSize(boolean finals) {
			assert (m_mode == StatesContainerMode.saveRemoved);
			
			if (finals) {
				return m_finals.size();
			}
			else {
				return m_nonfinals.size();
			}
		}
		
		/**
		 * creates a collection of the non-final states for the merge
		 * in case of an automaton with no word accepted
		 * 
		 * @return collection of non-final states
		 */
		Collection<STATE> getTrivialAutomatonStates() {
			switch (m_mode) {
				case makeCopy :
					return m_nonfinals;
				case saveRemoved :
					LinkedList<STATE> result = new LinkedList<STATE>();
					Iterator<STATE> iterator = getNonfinalsIterator();
					while (iterator.hasNext()) {
						result.add(iterator.next());
					}
					return result;
				case none :
					return m_parentOperand.getStates();
				default :
					assert false;
					return null;
			}
		}
		
		/**
		 * @return number of states
		 */
		int size() {
			switch (m_mode) {
				case makeCopy :
					return m_finals.size() + m_nonfinals.size();
				case saveRemoved :
					return m_parentOperand.size() - m_finals.size() -
							m_nonfinals.size();
				case none :
					return m_parentOperand.size();
				default :
					assert false;
					return 0;
			}
		}
		
		/**
		 * @param state the state (must be contained in the original automaton)
		 * @return true iff state was not removed
		 */
		boolean contains(STATE state) {
			switch (m_mode) {
				case makeCopy :
					return (m_nonfinals.contains(state) ||
							m_finals.contains(state));
				case saveRemoved :
					return (! (m_nonfinals.contains(state) ||
							m_finals.contains(state)));
				case none :
					return m_parentOperand.getStates().contains(state);
				default :
					assert false;
					return false;
			}
		}
		
		/**
		 * adds a state
		 * only used if copy of states is made
		 * 
		 * @param state new state
		 */
		void addState(STATE state) {
			switch (m_mode) {
				case makeCopy :
					if (m_parentOperand.isFinal(state)) {
						m_finals.add(state);
					}
					else {
						m_nonfinals.add(state);
					}
					return;
				case saveRemoved :
				case none :
				default :
					assert false;
					return;
			}
		}
		
		/**
		 * adds a collection of states
		 * only used if copy of states is made
		 * 
		 * @param states collection of new states
		 */
		public void addAll(Collection<STATE> states) {
			switch (m_mode) {
				case makeCopy :
					for (STATE state : states) {
						addState(state);
					}
					return;
				case saveRemoved :
				case none :
				default :
					assert false;
					return;
			}
		}
		
		/**
		 * @param state state to remove
		 */
		void removeState(STATE state) {
			switch (m_mode) {
				case makeCopy :
					if (! m_nonfinals.remove(state)) {
						m_finals.remove(state);
					}
					return;
				case saveRemoved :
					if (m_parentOperand.isFinal(state)) {
						m_finals.add(state);
					}
					else {
						m_nonfinals.add(state);
					}
					return;
				case none :
				default :
					assert false;
					return;
			}
		}
		
		/**
		 * @return true iff states set is a real copy
		 */
		boolean wasCopied() {
			return m_mode == StatesContainerMode.makeCopy;
		}
		
		/**
		 * deletes all stored elements
		 */
		void delete() {
			switch (m_mode) {
				case makeCopy :
				case saveRemoved :
					m_finals = null;
					m_nonfinals = null;
					return;
				case none :
					return;
				default :
					assert false;
					return;
			}
		}
		
		/*
		 * --- transition helpers
		 * (for avoiding states that have already been removed)
		 */
		private Collection<STATE> neighbors(Iterable<STATE> states) {
			switch (m_mode) {
				case makeCopy :
				case saveRemoved :
					LinkedList<STATE> result = new LinkedList<STATE>();
					for (STATE s : states) {
						if (contains(s)) {
							result.add(s);
						}
					}
					return result;
				case none :
				default :
					assert false;
					return null;
			}
		}
		Collection<STATE> predInternal(STATE state, LETTER letter) {
			return neighbors(m_parentOperand.predInternal(state, letter));
		}
		Collection<STATE> predCall(STATE state, LETTER letter) {
			return neighbors(m_parentOperand.predCall(state, letter));
		}
		Collection<STATE> predReturnLin(STATE state, LETTER letter,
										STATE hier) {
			return neighbors(m_parentOperand.predReturnLin(state, letter,
															hier));
		}
		Collection<STATE> predReturnHier(STATE state, LETTER letter) {
			return neighbors(m_parentOperand.predReturnHier(state, letter));
		}
	}
	
	/**
	 * possible modes of the states container
	 */
	private enum StatesContainerMode {
		/**
		 * makes a copy of the used states
		 */
		makeCopy,
		/**
		 * makes a copy of the unused states
		 */
		saveRemoved,
		/**
		 * directly passes the states from the original automaton
		 */
		none;
	}
	
	/**
	 * Returns a Map from states of the input automaton to states of the output
	 * automaton. The image of a state oldState is the representative of 
	 * oldStates equivalence class.
	 * This method can only be used if the minimization is finished.
	 */
	public Map<STATE,STATE> getOldState2newState() {
		if (!m_MinimizationFinished) {
			throw new IllegalStateException();
		}
		
		Map<STATE,STATE> oldState2newState = new Map<STATE,STATE>() {

			@Override
			public int size() {
				return m_Partition.m_mapState2EquivalenceClass.size();
			}

			@Override
			public boolean isEmpty() {
				return m_Partition.m_mapState2EquivalenceClass.isEmpty();
			}

			@Override
			public boolean containsKey(Object key) {
				return m_Partition.m_mapState2EquivalenceClass.containsKey(key);
			}

			@Override
			public boolean containsValue(Object value) {
				throw new UnsupportedOperationException();
			}

			@Override
			public STATE get(Object key) {
				return m_Partition.m_mapState2EquivalenceClass.get(key).
															getRepresentative();
			}

			@Override
			public STATE put(STATE key, STATE value) {
				throw new UnsupportedOperationException();
			}

			@Override
			public STATE remove(Object key) {
				throw new UnsupportedOperationException();
			}

			@Override
			public void putAll(Map<? extends STATE, ? extends STATE> m) {
				throw new UnsupportedOperationException();
			}

			@Override
			public void clear() {
				throw new UnsupportedOperationException();
			}

			@Override
			public Set<STATE> keySet() {
				return m_Partition.m_mapState2EquivalenceClass.keySet();
			}

			@Override
			public Collection<STATE> values() {
				throw new UnsupportedOperationException();
			}

			@Override
			public Set<java.util.Map.Entry<STATE, STATE>> entrySet() {
				throw new UnsupportedOperationException();
			}
		};
		return oldState2newState;
	}
	
	@Override
	public String operationName() {
		return "minimizeSevpa";
	}
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Operand " +
			m_operand.sizeInformation() + ".";
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ". Reduced states from " +
			m_operand.size() + " to " + m_nwa.size();
	}
	
	@Override
	public INestedWordAutomatonOldApi<LETTER,STATE> getResult()
			throws OperationCanceledException {
		return m_nwa;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		s_Logger.info("Start testing correctness of " + operationName());
		boolean correct = true;
		correct &= (ResultChecker.nwaLanguageInclusion(m_operand, m_nwa, stateFactory) == null);
		assert correct;
		correct &= (ResultChecker.nwaLanguageInclusion(m_nwa, m_operand, stateFactory) == null);
		assert correct;
		if (!correct) {
			ResultChecker.writeToFileIfPreferred(operationName() + "Failed", "", m_operand);
		}
		s_Logger.info("Finished testing correctness of " + operationName());
		return correct;
	}
}