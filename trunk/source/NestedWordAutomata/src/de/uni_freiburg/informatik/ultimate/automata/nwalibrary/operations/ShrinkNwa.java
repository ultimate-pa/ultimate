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
 * <splittingPolicy> currently all internal (call, return) splits consider the
 *                   same splitter set
 *                   this could be improved by stopping the split whenever the
 *                   splitter set itself is split
 *                   but this somehow counters the automata implementation,
 *                   since finding the predecessors is expensive
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
 * <inform> somehow the EC has to be informed when a successor EC was split
 *          currently informs ALL hierarchical successors
 * 
 * <linSuccSplit> more efficiently possible
 * 
 * <hierRetPred> is this necessary?
 * 
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
	private WorkListRetPred m_workListRetPred;
	/*private WorkListRetSucc m_workListRetSucc; TODO<old>*/
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
		m_workListRetPred = new WorkListRetPred();
		/*m_workListRetSucc = new WorkListRetSucc(); TODO<old>*/
		
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
				splitInternalOrCallPredecessors(a,
						new InternalTransitionIterator());
			}
		}
		// more complicated splitting 
		else {
			// global down states split
			if (DEBUG)
				System.out.println("-- down states split");
			splitDownStates();
			
			if (DEBUG)
				System.out.println("\n-- normal splitting");
			
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
					splitInternalOrCallPredecessors(a,
							new InternalTransitionIterator());
					
					// call split
					if (DEBUG)
						System.out.println("\n-- call search");
					splitInternalOrCallPredecessors(a,
							new CallTransitionIterator());
				}
				
				// return predecessors
				if (m_workListRetPred.hasNext()) {
					if (DEBUG)
						System.out.println("\n-- return search");
					EquivalenceClass a = m_workListRetPred.next();
					
					splitReturnPredecessors(a);
				}
				else {
					break outer;
				}
				
				/* TODO<old>
				// return successors
				while (m_workListRetSucc.hasNext()) {
					// cancel if signal is received
					if (! UltimateServices.getInstance().continueProcessing())
							{
						throw new OperationCanceledException();
					}
					
					if (DEBUG)
						System.out.println("\n-- ret succ search");
					// return successor split
					splitLinearReturnSuccessors(m_workListRetSucc.next());
					
					// go back to cheap split if possible
					if (m_workListIntCall.hasNext() ||
							m_workListRetPred.hasNext()) {
						continue outer;
					}
				}
				*/
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
	 * Globally for each state with outgoing return transitions get the
	 * respective
	 * 1) down states and
	 * 2) hierarchical predecessors.
	 * 
	 * Note that 2) is always a subset of 1), since other transitions have
	 * been removed in the input automaton.
	 * 
	 * If 2) is a PROPER subset of 1) and not the empty set, split the
	 * difference 1) - 2).
	 * TODO<DownStates> this split is not correct:
	 *                  negative states could be combined
	 *                  probably this split is not needed, but a more
	 *                  complicated return split instead
	 * 
	 * As a cheap byproduct also split states with no outgoing return edges.
	 */
	@SuppressWarnings("unchecked")
	private void splitDownStates() {
		// states with no outgoing return edges can be split as byproduct
		final HashSet<STATE> noOutgoingReturnStates = new HashSet<STATE>(
				computeHashSetCapacity(m_operand.size()));
		
		for (final STATE state : m_operand.getStates()) {
			final Iterator<OutgoingReturnTransition<LETTER, STATE>>
					returnEdges = m_operand.returnSuccessors(state).iterator();
			if (returnEdges.hasNext()) {
				if (DEBUG)
					System.out.println("considering state " + state);
				
				final HashMap<LETTER, HashSet<STATE>> letter2positiveStates =
						new HashMap<LETTER, HashSet<STATE>>();
				final HashSet<LETTER> candidates = new HashSet<LETTER>();
				
				// collect all outgoing return edges for the state
				do {
					final OutgoingReturnTransition<LETTER, STATE> edge =
							returnEdges.next();
					final LETTER letter = edge.getLetter();
					if (m_doubleDecker.isDoubleDecker(state,
							edge.getHierPred())) {
						HashSet<STATE> set = letter2positiveStates.get(letter);
						if (set == null) {
							set = new HashSet<STATE>();
							letter2positiveStates.put(letter, set);
						}
						set.add(edge.getSucc());
					}
					// possibly split with respect to this letter
					else {
						candidates.add(letter);
					}
				} while (returnEdges.hasNext());
				
				// check for splits
				for (final LETTER letter : letter2positiveStates.keySet()) {
					if (candidates.contains(letter)) {
						final HashSet<STATE> candidateSet =
								letter2positiveStates.get(letter);
						assert (! candidateSet.isEmpty());
						
						// do a split
						if (DEBUG)
							System.out.println("split due to down state: " +
									candidateSet);
						m_partition.splitEquivalenceClasses(candidateSet
								/*, false TODO<old> */
								);
					}
				}
			}
			// state has no outgoing return edges, definite split
			else {
				if (DEBUG)
					System.out.println("ignoring state " + state);
				noOutgoingReturnStates.add(state);
			}
		}
		
		// split states with no outgoing return edges
		if (DEBUG)
			System.out.println("split no out ret: " + noOutgoingReturnStates);
		m_partition.splitEquivalenceClasses(noOutgoingReturnStates
				/*, false TODO<old> */
				);
		
		if (DEBUG)
			System.out.println("DownStates split: " +
					m_partition.m_equivalenceClasses.size());
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
			m_partition.splitEquivalenceClasses(predecessorSet
					/*, false TODO<old> */
					);
		}
	}
	
	/**
	 * For each state and return symbol split the linear predecessors
	 * with respect to the hierarchical predecessor sets.
	 * 
	 * TODO<linRetPred> This split may be too eager, not sure whether
	 *                  hierarchical predecessors really have to be considered.
	 * 
	 * @param a splitter equivalence class
	 */
	private void splitLinearReturnPredecessorsOld(final EquivalenceClass a) {
		// map for linear split: LETTER -> (EC(hier) -> Set(lin))
		final HashMap<LETTER, HashMap<EquivalenceClass, HashSet<STATE>>>
			letter2hier2lin =
			new HashMap<LETTER, HashMap<EquivalenceClass, HashSet<STATE>>>();
		
		// find split candidates
		for (final STATE state : a.m_states) {
			final Iterator<IncomingReturnTransition<LETTER, STATE>> iterator =
					m_operand.returnPredecessors(state).iterator();
			while (iterator.hasNext()) {
				final IncomingReturnTransition<LETTER, STATE> edge =
						iterator.next();
				final LETTER letter = edge.getLetter();
				
				HashMap<EquivalenceClass, HashSet<STATE>> hier2lin =
						letter2hier2lin.get(letter);
				if (hier2lin == null) {
					hier2lin = new HashMap<EquivalenceClass, HashSet<STATE>>();
					letter2hier2lin.put(letter, hier2lin);
				}
				final EquivalenceClass hierEc =
						m_partition.m_state2EquivalenceClass.get(edge.getHierPred());
				
				HashSet<STATE> lins = hier2lin.get(hierEc);
				if (lins == null) {
					lins = new HashSet<STATE>();
					hier2lin.put(hierEc, lins);
				}
				lins.add(edge.getLinPred());
			}
		}
		
		// split each map value (again a map)
		for (final HashMap<EquivalenceClass, HashSet<STATE>> hier2lin :
				letter2hier2lin.values()) {
			assert (! hier2lin.isEmpty());
			// split each map value (set of predecessor states)
			for (final HashSet<STATE> lin : hier2lin.values()) {
				assert (! lin.isEmpty());
				
				m_partition.splitEquivalenceClasses(lin
						/*, false TODO<old> */
						);
			}
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
		
		// split linear predecessors with respect to a letter
		for (final HashSet<STATE> lins : letter2lin.values()) {
			m_partition.splitEquivalenceClasses(lins);
		}
		// splitter set was split, stop
		if (a.m_isInWorkListIntCall) {
			return;
		}
		
		/*
		 * Find the predecessor equivalence classes.
		 * Since the equivalence classes can be split, create immutable data
		 * structures here.
		 * 
		 * TODO<returnSplit> prefer or defer splitter set A?
		 */
		final HashMap<LETTER, HashSet<ArrayList<STATE>>> letter2linSet =
				new HashMap<LETTER, HashSet<ArrayList<STATE>>>();
		HashMap<EquivalenceClass, ArrayList<STATE>> ec2lin =
				new HashMap<EquivalenceClass, ArrayList<STATE>>();
		for (final Entry<LETTER, HashSet<STATE>> entry :
				letter2lin.entrySet()) {
			final LETTER letter = entry.getKey();
			final HashSet<ArrayList<STATE>> linSet =
					new HashSet<ArrayList<STATE>>();
			letter2linSet.put(letter, linSet);
			final Iterable<STATE> lins = entry.getValue();
			for (final STATE lin : lins) {
				final EquivalenceClass ec =
						m_partition.m_state2EquivalenceClass.get(lin);
				ArrayList<STATE> linList = ec2lin.get(ec);
				if (linList == null) {
					linList = new ArrayList<STATE>(ec.m_states.size());
					ec2lin.put(ec, linList);
				}
				linSet.add(linList);
				linList.add(lin);
			}
		}
		// delete temporary mapping
		ec2lin = null;
		letter2lin = null;
		
		// splits
		for (final Entry<LETTER, HashSet<ArrayList<STATE>>> entry :
				letter2linSet.entrySet()) {
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
		
//		TODO<old2>
//		for (Entry<LETTER, HashMap<STATE, HashSet<STATE>>> entry:
//				letter2lin2hier.entrySet()) {
//			final LETTER letter = entry.getKey();
//			final HashMap<STATE, HashSet<STATE>> lin2hiers = entry.getValue();
//			
//			// collect all linear predecessor equivalence classes
//			final HashSet<EquivalenceClass> lins =
//					new HashSet<EquivalenceClass>();
//			for (final STATE lin : lin2hiers.keySet()) {
//				lins.add(m_partition.m_state2EquivalenceClass.get(lin));
//			}
//			
//			/*
//			 * for each equivalence class of linear predecessors check
//			 * hierarchical predecessors
//			 */
//			for (final EquivalenceClass linEc : lins) {
//				for (final STATE lin : linEc.m_states) {
//					final HashSet<EquivalenceClass> hiers =
//							new HashSet<EquivalenceClass>();
//					// find hierarchical predecessor equivalence classes
//					for (final STATE hier : lin2hiers.get(lin)) {
//						hiers.add(m_partition.
//								m_state2EquivalenceClass.get(hier));
//					}
//					
//					// check hierarchical predecessor equivalence classes
//					for (final EquivalenceClass hierEc : hiers) {
//						for (final STATE hier : hierEc.m_states) {
//							final LinkedList<STATE> negatives =
//									new LinkedList<STATE>();
//							final Iterator<OutgoingReturnTransition
//									<LETTER, STATE>> it = m_operand.
//									returnSucccessors(lin, hier, letter).
//									iterator();
//							boolean found = false;
//							
//							/*
//							 * if there is no outgoing return transition,
//							 * the DownStates split assures correctness
//							 */
//							if (it.hasNext()) {
//								do {
//									final STATE succ = it.next().getSucc();
//									if (m_partition.m_state2EquivalenceClass.
//											get(succ) == a) {
//										found = true;
//										break;
//									}
//								} while (it.hasNext());
//								
//								if (! found) {
//									negatives.add(hier);
//								}
//							}
//							else {
//								assert ! ((IDoubleDeckerAutomaton
//										<LETTER, STATE>)m_operand).
//										isDoubleDecker(lin, hier);
//							}
//							
//							/*
//							 * To avoid concurrent modifications, whenever a
//							 * split occurred stop the procedure.
//							 * TODO<splitLinPred> This is way too expensive!
//							 */
//							if (m_partition.splitEquivalenceClasses(negatives))
//									{
//								if (! a.m_isInWorkListRetPred) {
//									a.m_isInWorkListRetPred = true;
//									m_workListRetPred.add(a);
//								}
//								return;
//							}
//						}
//					}
//				}
//			}
//		}
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
		
			/* TODO<old2>
			for (final OutgoingReturnTransition<LETTER, STATE> edge :
					) {
				final EquivalenceClass currentSuccEc =
						m_partition.m_state2EquivalenceClass.get(
								edge.getSucc());
				HashSet<STATE> hiers = succ2hier.get(currentSuccEc);
				if (hiers == null) {
					hiers = new HashSet<STATE>();
					succ2hier.put(currentSuccEc, hiers);
				}
				hiers.add(edge.getHierPred());
			}
			
			// split different hierarchical predecessors
			// TODO not correct
			final HashSet<EquivalenceClass> hierEcs =
					new HashSet<EquivalenceClass>();
			for (final HashSet<STATE> hiers : succ2hier.values()) {
				final HashSet<STATE> positives = new HashSet<STATE>();
				
				for (final STATE hier : hiers) {
					final EquivalenceClass hierEc =
							m_partition.m_state2EquivalenceClass.get(hier);
					if (hierEcs.add(hierEc)) {
						// check behavior for hierarchical equivalence class
						for (final STATE hierCheck : hierEc.m_states) {
							if (hiers.contains(hierCheck) ||
									m_operand.returnSucccessors(
									lin, hierCheck, letter).iterator().
									hasNext()) {
								positives.add(hierCheck);
							}
						}
					}
				}
				
				m_partition.splitEquivalenceClasses(positives);
			}
		}
		*/
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
	 * For each state and return symbol split the hierarchical predecessors
	 * with respect to the linear predecessor sets.
	 * 
	 * @param a splitter equivalence class
	 */
	private void splitHierarchicalReturnPredecessors(
			final EquivalenceClass a) {
		// TODO<hierRetPred> is this necessary?
	}
	
	/**
	 * TODO<linRetSucc> For nondeterministic transitions this could split too
	 *                  eagerly.
	 * 
	 * For each state and return symbol split the linear successors
	 * with respect to the hierarchical predecessor sets.
	 * 
	 * By assumption each state in A has exactly the same outgoing return
	 * edges wrt. the same hierarchical predecessor equivalence classes.
	 * 
	 * @param a splitter equivalence class
	 */
	private void splitLinearReturnSuccessors(final EquivalenceClass a) {
		// arbitrary representative
		final STATE representative = a.m_states.iterator().next();
		assert (representative != null);
		
		// recognize when the splitter set was split itself
		final int sizeOfA = a.m_states.size();
		
		// collect all return letters with respective hierarchical predecessors
		final HashMap<LETTER, HashSet<EquivalenceClass>> letter2hierEc =
				new HashMap<LETTER, HashSet<EquivalenceClass>>();
		for (final OutgoingReturnTransition<LETTER, STATE> edge :
			m_operand.returnSuccessors(representative)) {
			final LETTER letter = edge.getLetter();
			HashSet<EquivalenceClass> hierEcs = letter2hierEc.get(letter);
			if (hierEcs == null) {
				hierEcs = new HashSet<EquivalenceClass>();
				letter2hierEc.put(letter, hierEcs);
			}
			hierEcs.add(m_partition.m_state2EquivalenceClass.get(
					edge.getHierPred()));
		}
		
		for (Entry<LETTER, HashSet<EquivalenceClass>> entry :
				letter2hierEc.entrySet()) {
			final LETTER letter = entry.getKey();
			final HashMap<EquivalenceClass, HashSet<STATE>> succEc2hier =
					new HashMap<EquivalenceClass, HashSet<STATE>>();
			
			for (final STATE lin : a.m_states) {
				// for each linear predecessor check the respective transitions
				for (final EquivalenceClass hierEc : entry.getValue()) {
					for (final STATE hier : hierEc.m_states) {
						for (final OutgoingReturnTransition<LETTER, STATE> edge
								: m_operand.returnSucccessors(lin, hier,
										letter)) {
							final EquivalenceClass succEc =
									m_partition.m_state2EquivalenceClass.get(
									edge.getSucc());
							HashSet<STATE> hiers = succEc2hier.get(succEc);
							if (hiers == null) {
								hiers = new HashSet<STATE>();
								succEc2hier.put(succEc, hiers);
							}
							hiers.add(edge.getHierPred());
						}
					}
				}
				
				// split states
				for (final Entry<EquivalenceClass, HashSet<STATE>> entry2 :
						succEc2hier.entrySet()) {
					final HashSet<STATE> hiers = entry2.getValue();
					
					// must inform all hierarchical successor classes
					m_partition.splitEquivalenceClasses(hiers
							/*, true TODO<old> */
							);
				}
				
				/*
				 * To avoid concurrent modifications of the iterator, the
				 * method is stopped here whenever the splitter set itself was
				 * split. This could be avoided by storing the states, but the
				 * method will be called with this new splitter set anyway, so
				 * this is not considered necessary.
				 */
				if (a.m_states.size() < sizeOfA) {
					return;
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
		m_workListRetPred = null;
		/*m_workListRetSucc = null; TODO<old>*/
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
			final EquivalenceClass ec = addEcHelper(module
					/*, false TODO<old>
					 */);
			for (STATE state : module) {
				m_state2EquivalenceClass.put(state, ec);
			}
		}
		
		/**
		 * This method adds a new equivalence class to the partition.
		 *
		 * @param module the states in the equivalence class
		 * @param informed true iff the equivalence class is an informer
		 * @return the equivalence class
		 */
		private EquivalenceClass addEcHelper(final Set<STATE> module/*,
				final boolean informed TODO<old>
				*/) {
			final EquivalenceClass ec =
				new EquivalenceClass(module
						/*, informed TODO<old>
						 */);
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
		 * @param informSuccessors true iff hierarchical successors must be
		 *        informed
		 * @return true iff a split occurred
		 */
		private boolean splitEquivalenceClasses(final Iterable<STATE> states
				/*,final boolean informSuccessors TODO<old>
				 */) {
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
							addEcHelper(intersection
									//, ec.m_isInformed TODO<old>
									);
					for (STATE state : intersection) {
						m_state2EquivalenceClass.put(state, newEc);
					}
					
					// put ec in work lists if not already in there
					if (! ec.m_isInWorkListIntCall) {
						ec.m_isInWorkListIntCall = true;
						m_workListIntCall.add(ec);
					}
					if (! ec.m_isInWorkListRetPred) {
						ec.m_isInWorkListRetPred = true;
						m_workListRetPred.add(ec);
					}
					/*
					if (! ec.m_isInWorkListRetSucc) {
						ec.m_isInWorkListRetSucc = true;
						m_workListRetSucc.add(ec);
					} TODO<old>*/
					
					// reset equivalence class (before 
					ec.reset();
					
					if (DEBUG)
						System.out.println("EC was split " + ec);
					
					/* TODO<old>
					// inform hierarchical successors
					if (informSuccessors) {
						informSuccessors(ec, newEc);
					}
					*/
				}
			}
			
			// reset split list
			m_splitEquivalenceClasses = new LinkedList<EquivalenceClass>();
			return splitOccurred;
		}
		
		/**
		 * This method informs all hierarchical successor equivalence classes,
		 * i.e., it puts them in the linear return predecessor work list.
		 * 
		 * In fact, this task is delayed to the respective work list.
		 *
		 * @param oldEc one hierarchical predecessor equivalence class
		 * @param newEc the other hierarchical predecessor equivalence class
		 */
		/* TODO<old>
		private void informSuccessors(final EquivalenceClass oldEc,
				final EquivalenceClass newEc) {
			m_workListRetPred.inform(oldEc);
			m_workListRetPred.inform(newEc);
		}
		*/
		
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
		private boolean m_isInWorkListRetPred;
		private boolean m_isInWorkListRetSucc;
		/* TODO<old>
		 * private boolean m_isInformed;*/
		// intersection set that finally becomes a new equivalence class
		private Set<STATE> m_intersection;
		
		/**
		 * @param states the set of states for the equivalence class
		 * @param informed true iff the equivalence class is an informer
		 */
		public EquivalenceClass(final Set<STATE> states
				/*, final boolean informed TODO<old>*/
				) {
			m_states = states;
			reset();
			m_isInWorkListIntCall = true;
			m_workListIntCall.add(this);
			m_isInWorkListRetPred = true;
			m_workListRetPred.add(this);
			/* TODO<old>
			m_isInWorkListRetSucc = true;
			m_workListRetSucc.add(this);
			m_isInformed = informed;
			if (m_isInformed) {
				m_workListRetPred.inform(this);
			}
			*/
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
			if (! m_isInWorkListIntCall && ! m_isInWorkListRetPred &&
					! m_isInWorkListRetSucc && m_intersection.isEmpty()) {
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
			builder.append(m_isInWorkListRetPred ? "RP" : "-");
			builder.append(",");
			builder.append(m_isInWorkListRetSucc ? "RS" : "-");
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
			m_queue = new PriorityQueue<EquivalenceClass>(m_operand.size(),
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
	 * This class implements the work list for predecessor return splits.
	 */
	private class WorkListRetPred extends AWorkList {
		/* TODO<old>
		private final PriorityQueue<EquivalenceClass> m_informQueue;
		
		public WorkListRetPred() {
			super();
			m_informQueue = new PriorityQueue<EquivalenceClass>(
					m_operand.size(),
					new Comparator<EquivalenceClass>() {
						@Override
						public int compare(EquivalenceClass ec1,
								EquivalenceClass ec2) {
							return ec1.m_states.size() - ec2.m_states.size();
						}
					});
		}
		*/
		
		@Override
		public EquivalenceClass next() {
			final EquivalenceClass ec = m_queue.poll();
			ec.m_isInWorkListRetPred = false;
			if (DEBUG)
				System.out.println("\npopping from RetPred WL: " + ec);
			return ec;
		}
		
		/* TODO<old>
		@Override
		public boolean hasNext() {
			if (! m_queue.isEmpty()) {
				return true;
			}
			if (m_informQueue.isEmpty()) {
				return false;
			}
			do {
				final EquivalenceClass hierPred = m_informQueue.poll();
				assert (hierPred.m_isInformed);
				hierPred.m_isInformed = false;
				
				if (DEBUG)
					System.out.println("informing successors of " + hierPred);
				
				for (final STATE hier : hierPred.m_states) {
					for (final LETTER letter :
							m_operand.lettersReturnSummary(hier)) {
						for (final SummaryReturnTransition<LETTER, STATE>
								trans : m_operand.
								returnSummarySuccessor(letter, hier)) {
							final EquivalenceClass successor =
									m_partition.m_state2EquivalenceClass.get(
											trans.getSucc());
							
							// inform a successor equivalence class
							// TODO<inform> is this enough?
							if (! successor.m_isInWorkListRetPred) {
								successor.m_isInWorkListRetPred = true;
								add(successor);
								if (DEBUG)
									System.out.println("EC was informed " +
											successor);
							}
						}
					}
				}
				
				// found a possible splitter, break for now
				if (! m_queue.isEmpty()) {
					return true;
				}
			} while (! m_informQueue.isEmpty());
			return false;
		}
		*/
		
		@Override
		public void add(final EquivalenceClass ec) {
			assert (ec.m_isInWorkListRetPred);
			if (DEBUG)
				System.out.println("adding of RetPred WL: " + ec);
			super.add(ec);
		}
		
		/**
		 * This method puts an equivalence class into the inform work list.
		 * The successor equivalence classes are evaluated  
		 *
		 * @param ec
		 */
		/* TODO<old>
		private void inform(final EquivalenceClass ec) {
			if (! ec.m_isInformed) {
				ec.m_isInformed = true;
				m_informQueue.add(ec);
			}
		}
		
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			toStringHelper(builder);
			builder.append(", informs ");
			String append = "";
			for (final EquivalenceClass ec : m_informQueue) {
				builder.append(append);
				append = ", ";
				builder.append(ec);
			}
			builder.append(">>");
			return builder.toString();
		}
		*/
	}
	
	/**
	 * This class implements the work list for return successor splits.
	 */
	private class WorkListRetSucc extends AWorkList {
		@Override
		public EquivalenceClass next() {
			final EquivalenceClass ec = m_queue.poll();
			ec.m_isInWorkListRetSucc = false;
			if (DEBUG)
				System.out.println("\npopping from RetSucc WL: " + ec);
			return ec;
		}
		
		@Override
		public void add(final EquivalenceClass ec) {
			assert (ec.m_isInWorkListRetSucc);
			if (DEBUG)
				System.out.println("adding of RetSucc WL: " + ec);
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