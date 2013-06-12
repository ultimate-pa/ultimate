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
 * <threading> identify possibilities for threading and implement it
 * 
 * 
 * misc:
 * <hashCode> overwrite for EquivalenceClass?
 * 
 * <finalize> remove all unnecessary objects in the end
 * 
 * <statistics> remove in the end
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
	// placeholder equivalence class
	final HashSet<EquivalenceClass> m_negativeSet;
	// simulates the output automaton
	private ShrinkNwaResult m_result;
	
	// TODO<debug>
	private final boolean DEBUG = false;
	private final boolean DEBUG2 = false;
	
	// TODO<statistics>
	private final boolean STATISTICS = false;
	private int m_splitsWithChange = 0;
	private int m_splitsWithoutChange = 0;
	private int m_incomingTransitions = 0;
	private int m_noIncomingTransitions = 0;
	
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
		m_negativeSet = new HashSet<EquivalenceClass>();
		m_negativeSet.add(new EquivalenceClass());
		
		// must be the last part of the constructor
		s_Logger.info(startMessage());
		minimize(isFiniteAutomaton, equivalenceClasses);
		s_Logger.info(exitMessage());
		
		if (STATISTICS) {
			System.out.println("positive splits: " + m_splitsWithChange);
			System.out.println("negative splits: " + m_splitsWithoutChange);
			System.out.println("quota (p/n): " +
					(((float)m_splitsWithChange) /
							((float)Math.max(m_splitsWithoutChange, 1))));
			System.out.println("incoming transition checks : " +
					m_incomingTransitions);
			System.out.println("no incoming transitions found : " +
					m_noIncomingTransitions);
			System.out.println("quota (p/n): " +
					(((float)m_incomingTransitions) /
							((float)Math.max(m_noIncomingTransitions, 1))));
		}
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
				splitInternalOrCallPredecessors(a, internalIterator, true);
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
					if (a.m_incomingInt == EIncomingStatus.inWL) {
						a.m_incomingInt = EIncomingStatus.unknown;
						if (DEBUG)
							System.out.println("\n-- internal search");
						splitInternalOrCallPredecessors(a, internalIterator,
								true);
					}
					
					// call split
					if (a.m_incomingCall == EIncomingStatus.inWL) {
						a.m_incomingCall = EIncomingStatus.unknown;
						if (DEBUG)
							System.out.println("\n-- call search");
						splitInternalOrCallPredecessors(a, callIterator,
								false);
					}
				}
				
				// return predecessors
				if (m_workListRet.hasNext()) {
					if (DEBUG)
						System.out.println("\n-- return search");
					EquivalenceClass a = m_workListRet.next();
					
					splitReturnPredecessorsNew(a);
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
	 * @param isInternal true iff split is internal
	 */
	private void splitInternalOrCallPredecessors(final EquivalenceClass a,
			final ITransitionIterator<LETTER, STATE> iterator,
			final boolean isInternal) {
		assert ((isInternal &&
				(iterator instanceof ShrinkNwa.InternalTransitionIterator) &&
				(a.m_incomingInt != EIncomingStatus.inWL)) ||
				(! isInternal) &&
				((iterator instanceof ShrinkNwa.CallTransitionIterator) &&
				(a.m_incomingCall != EIncomingStatus.inWL)));
		
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
		
		// remember that this equivalence class has no incoming transitions
		if (letter2states.isEmpty()) {
			if (isInternal) {
				a.m_incomingInt = EIncomingStatus.none;
			}
			else {
				a.m_incomingCall = EIncomingStatus.none;
			}
			if (STATISTICS)
				++m_noIncomingTransitions;
		}
		else {
			if (STATISTICS)
				++m_incomingTransitions;
			
			// split each map value (set of predecessor states)
			for (final HashSet<STATE> predecessorSet :
					letter2states.values()) {
				assert (! predecessorSet.isEmpty());
				m_partition.splitEquivalenceClasses(predecessorSet);
			}
		}
	}
	
	/**
	 * Do a backwards split for return transitions. Since there are both linear
	 * and hierarchical predecessors, both of them have to be considered.
	 * This makes this split both complicated and expensive.
	 * 
	 * First all incoming return transitions are collected. Then all reached
	 * equivalence classes are found and put into two mappings, one from linear
	 * and one from hierarchical states. With these mappings the splits are
	 * performed.
	 * 
	 * TODO<iteration> possibly make a copy of hierarchical equivalence classes
	 *                 for fast iteration (only if more than once)
	 * TODO<singletons> detect singleton equivalence classes and do not add
	 *                  them to the splitting lists
	 *
	 * @param a splitter equivalence class
	 */
	private void splitReturnPredecessorsNew(final EquivalenceClass a) {
		assert (a.m_incomingRet != EIncomingStatus.inWL);
		
		// collect incoming return transitions
		HashMap<LETTER, HashMap<EquivalenceClass, HashSet<EquivalenceClass>>>
				letter2lin2hier = new HashMap<LETTER, HashMap<EquivalenceClass,
				HashSet<EquivalenceClass>>>();
		int numberOfLinearEcs = 0;
		for (final STATE succ : a.m_states) {
			for (final IncomingReturnTransition<LETTER, STATE> edge :
					m_operand.returnPredecessors(succ)) {
				final LETTER letter = edge.getLetter();
				HashMap<EquivalenceClass, HashSet<EquivalenceClass>> lin2hier =
						letter2lin2hier.get(letter);
				if (lin2hier == null) {
					lin2hier = new HashMap<EquivalenceClass,
							HashSet<EquivalenceClass>>();
					letter2lin2hier.put(letter, lin2hier);
					++numberOfLinearEcs;
				}
				final EquivalenceClass linEc = m_partition.
						m_state2EquivalenceClass.get(edge.getLinPred());
				HashSet<EquivalenceClass> hier = lin2hier.get(linEc);
				if (hier == null) {
					hier = new HashSet<EquivalenceClass>();
					lin2hier.put(linEc, hier);
				}
				hier.add(m_partition.m_state2EquivalenceClass.get(
						edge.getHierPred()));
			}
		}
		
		// remember that this equivalence class has no incoming transitions
		if (letter2lin2hier.isEmpty()) {
			a.m_incomingRet = EIncomingStatus.none;
			if (STATISTICS)
				++m_noIncomingTransitions;
			
			return;
		}
		
		if (STATISTICS)
			++m_incomingTransitions;
		
		if (DEBUG2) {
			System.err.println(m_partition.m_equivalenceClasses);
			System.err.println("-- new return mapping: from A = " + a);
			System.err.println(letter2lin2hier);
		}
		
		// set up mappings with information for splitting
		final LinkedList<HashMap<STATE,
			HashMap<EquivalenceClass, HashMap<Set<EquivalenceClass>,
			Set<STATE>>>>> listLin2hierEc2succ2hier =
			new LinkedList<HashMap<STATE, HashMap<EquivalenceClass,
			HashMap<Set<EquivalenceClass>,Set<STATE>>>>>();
		final ArrayList<HashMap<STATE, HashMap<Set<EquivalenceClass>,
			Set<STATE>>>> listHier2succ2lin = new ArrayList<HashMap<STATE,
			HashMap<Set<EquivalenceClass>,Set<STATE>>>>(numberOfLinearEcs);
		
		for (final Entry<LETTER, HashMap<EquivalenceClass,
				HashSet<EquivalenceClass>>> outerEntry :
					letter2lin2hier.entrySet()) {
			final LETTER letter = outerEntry.getKey();
			
			if (DEBUG2)
				System.err.println("next letter: " + letter);
			
			for (final Entry<EquivalenceClass, HashSet<EquivalenceClass>>
					innerEntry : outerEntry.getValue().entrySet()) {
				final EquivalenceClass linEc = innerEntry.getKey();
				final HashMap<STATE, HashMap<EquivalenceClass,
					HashMap<Set<EquivalenceClass>, Set<STATE>>>>
					lin2hierEc2succ2hier = new HashMap<STATE,
					HashMap<EquivalenceClass, HashMap<Set<EquivalenceClass>,
					Set<STATE>>>>();
				
				if (DEBUG2)
					System.err.println("-next linEc: " + linEc);
				
				final HashMap<STATE, HashMap<Set<EquivalenceClass>,
					Set<STATE>>> hier2succ2lin = new HashMap<STATE,
					HashMap<Set<EquivalenceClass>,Set<STATE>>>(
							computeHashSetCapacity(linEc.m_states.size()));
				listHier2succ2lin.add(hier2succ2lin);
				
				for (final STATE lin : linEc.m_states) {
					if (DEBUG2)
						System.err.println("--next lin : " + lin);
					
					final HashMap<EquivalenceClass, HashMap<Set<
						EquivalenceClass>, Set<STATE>>> hierEc2succ2hier =
						new HashMap<EquivalenceClass, HashMap<Set<
						EquivalenceClass>, Set<STATE>>>();
					
					for (final EquivalenceClass hierEc :
							innerEntry.getValue()) {
						final HashMap<Set<EquivalenceClass>, Set<STATE>>
							succ2hier = new HashMap<Set<EquivalenceClass>,
							Set<STATE>>();
						
						if (DEBUG2)
							System.err.println("next hierEc: " + hierEc);
						
						for (final STATE hier : hierEc.m_states) {
							
							HashMap<Set<EquivalenceClass>, Set<STATE>>
								succ2lin = hier2succ2lin.get(hier);
							if (succ2lin == null) {
								succ2lin = new HashMap<Set<EquivalenceClass>,
										Set<STATE>>();
								hier2succ2lin.put(hier, succ2lin);
							}
							
							if (DEBUG2)
								System.err.println("next hier  : " + hier);
							
							final Iterator<OutgoingReturnTransition<
								LETTER, STATE>> edges = m_operand.
								returnSucccessors(lin, hier, letter).
								iterator();
							
							if (edges.hasNext()) {
								final HashSet<EquivalenceClass> succEcs =
										new HashSet<EquivalenceClass>();
								do {
									final OutgoingReturnTransition
										<LETTER, STATE> edge = edges.next();
									if (DEBUG2)
										System.err.println("next trans : " +
												edge);
									
									final EquivalenceClass succEc =
											m_partition.
											m_state2EquivalenceClass.get(
													edge.getSucc());
									if (DEBUG2)
										System.err.println("this succEc: " +
												succEc);
									
									succEcs.add(succEc);
								} while (edges.hasNext());
								if (DEBUG2)
									System.err.println("all succEcs: " +
											succEcs);
								
								Set<STATE> hierSet = succ2hier.get(succEcs);
								if (hierSet == null) {
									hierSet = new HashSet<STATE>();
									succ2hier.put(succEcs, hierSet);
								}
								hierSet.add(hier);
								Set<STATE> linSet = succ2lin.get(succEcs);
								if (linSet == null) {
									linSet = new HashSet<STATE>();
									succ2lin.put(succEcs, linSet);
								}
								linSet.add(lin);
							}
							else {
								if (m_doubleDecker.isDoubleDecker(lin, hier)) {
									if (DEBUG2)
										System.err.println("no trans, but DS");
									
									Set<STATE> hierSet =
											succ2hier.get(m_negativeSet);
									if (hierSet == null) {
										hierSet = new HashSet<STATE>();
										succ2hier.put(m_negativeSet, hierSet);
									}
									hierSet.add(hier);
									Set<STATE> linSet =
											succ2lin.get(m_negativeSet);
									if (linSet == null) {
										linSet = new HashSet<STATE>();
										succ2lin.put(m_negativeSet, linSet);
									}
									linSet.add(lin);
								}
								else {
									if (DEBUG2)
										System.err.println("no trans, no DS");
								}
							}
						}
						
						if (DEBUG2)
							System.err.println("succ2hier: " + succ2hier);
						
						if (! succ2hier.isEmpty()) {
							hierEc2succ2hier.put(hierEc, succ2hier);
						}
					}
					if (! hierEc2succ2hier.isEmpty()) {
						lin2hierEc2succ2hier.put(lin, hierEc2succ2hier);
					}
				}
				if (! lin2hierEc2succ2hier.isEmpty()) {
					listLin2hierEc2succ2hier.add(lin2hierEc2succ2hier);
				}
				
				if (DEBUG2) {
					System.err.println("hier2succ2lin: " + hier2succ2lin);
					System.err.println("lin2hierEc2succ2hier: " +
							lin2hierEc2succ2hier);
				}
			}
		}
		
		// split
		splitReturnHelper(listLin2hierEc2succ2hier, listHier2succ2lin);
	}
	
	/**
	 * This method constructs the graphs with the information collected before
	 * and calls the splitting method.
	 * Beforehand all the necessary information of which states have to be
	 * separated has been collected.
	 * 
	 * The problem here are the neutral states: The idea is to keep as many of
	 * them as possible without a split. In general, this is hard.
	 * 
	 * TODO<returnSplit> use more efficient split that exploits that the
	 *                   equivalence class is always the same
	 * 
	 * TODO<returnSplit> stop when A has been split?
	 * 
	 * TODO<graphs> the graphs are usually big, but sparse
	 *              this is both memory and runtime inefficient, since finding
	 *              neighbors is expensive
	 *              probably keep lists of neighbors instead
	 *
	 * @param listLin2hierEc2succ2hier list of linears to hierarchical
	 *        equivalence classes to successors to hierarchicals
	 * @param listHier2succ2lin list of hierarchicals to successors to linears
	 */
	private void splitReturnHelper(final LinkedList<HashMap<STATE,
			HashMap<EquivalenceClass, HashMap<Set<EquivalenceClass>,
			Set<STATE>>>>> listLin2hierEc2succ2hier,
			final List<HashMap<STATE, HashMap<Set<EquivalenceClass>,
			Set<STATE>>>> listHier2succ2lin) {
		if (DEBUG2) {
			System.err.println("\nlistLin2hierEc2succ2hier: " +
					listLin2hierEc2succ2hier);
			System.err.println("listHier2succ2lin: " + listHier2succ2lin +
					"\n");
		}
		
		// construct graphs
		// TODO<findEcs> find equivalence classes in previous method
		final HashMap<EquivalenceClass, SplittingGraph> ec2graph =
				new HashMap<EquivalenceClass, SplittingGraph>();
		for (final HashMap<STATE, HashMap<EquivalenceClass,
				HashMap<Set<EquivalenceClass>, Set<STATE>>>>
				lin2hierEc2succ2hier : listLin2hierEc2succ2hier) {
			for (final STATE lin : lin2hierEc2succ2hier.keySet()) {
				final EquivalenceClass ec = m_partition.
						m_state2EquivalenceClass.get(lin);
				if (ec2graph.get(ec) == null) {
					if (DEBUG2)
						System.err.println("adding lin. EC graph: " + ec);
					ec2graph.put(ec, new SplittingGraph(ec.m_states));
				}
				else {
					if (DEBUG2)
						System.err.println("ignoring lin. EC graph: " + ec);
				}
			}
		}
		for (final HashMap<STATE, HashMap<Set<EquivalenceClass>, Set<STATE>>>
				hier2succ2lin : listHier2succ2lin) {
			for (final STATE hier : hier2succ2lin.keySet()) {
				final EquivalenceClass ec = m_partition.
						m_state2EquivalenceClass.get(hier);
				if (ec2graph.get(ec) == null) {
					if (DEBUG2)
						System.err.println("adding hier. EC graph: " + ec);
					ec2graph.put(ec, new SplittingGraph(ec.m_states));
				}
				else {
					if (DEBUG2)
						System.err.println("ignoring hier. EC graph: " + ec);
				}
			}
		}
		
		final HashSet<SplittingGraph> visitedGraphs =
				new HashSet<SplittingGraph>();
		
		// local hierarchical split and global linear split
		for (final HashMap<STATE, HashMap<EquivalenceClass,
				HashMap<Set<EquivalenceClass>, Set<STATE>>>>
				lin2hierEc2succ2hier : listLin2hierEc2succ2hier) {
			
			if (DEBUG2)
				System.err.println(
						"\n\nconsider lin2hierEc2succ2hier " +
								lin2hierEc2succ2hier);
			
			for (final Entry<STATE, HashMap<EquivalenceClass,
					HashMap<Set<EquivalenceClass>, Set<STATE>>>>
					lin2hierEc2succ2hierEntry :
						lin2hierEc2succ2hier.entrySet()) {
				final STATE lin = lin2hierEc2succ2hierEntry.getKey();
				final HashMap<EquivalenceClass, HashMap<Set<EquivalenceClass>,
					Set<STATE>>> hierEc2succ2hier =
					lin2hierEc2succ2hierEntry.getValue();
				if (DEBUG2)
					System.err.println(
							"\n\nconsider lin2hierEc2succ2hierEntry " +
							lin2hierEc2succ2hierEntry);
				
				final HashMap<EquivalenceClass,
					HashMap<HashSet<Set<EquivalenceClass>>, Set<STATE>>>
					gHierEc2Succ2states = new HashMap<EquivalenceClass,
					HashMap<HashSet<Set<EquivalenceClass>>,Set<STATE>>>();
				
				for (final Entry<EquivalenceClass,
						HashMap<Set<EquivalenceClass>, Set<STATE>>>
						hierEc2succ2hierEntry : hierEc2succ2hier.entrySet()) {
					final EquivalenceClass hierEc =
							hierEc2succ2hierEntry.getKey();
					final HashMap<Set<EquivalenceClass>, Set<STATE>>
						succ2hier = hierEc2succ2hierEntry.getValue();
					
					HashMap<HashSet<Set<EquivalenceClass>>, Set<STATE>>
						gSucc2states = gHierEc2Succ2states.get(hierEc);
					if (gSucc2states == null) {
						gSucc2states = new HashMap<HashSet<
								Set<EquivalenceClass>>, Set<STATE>>();
						gHierEc2Succ2states.put(hierEc, gSucc2states);
					}
					
					if (DEBUG2)
						System.err.println(
								"\n\nconsider hierEc2succ2hierEntry " +
										hierEc2succ2hierEntry);
					final HashSet<Set<EquivalenceClass>> succs =
							new HashSet<Set<EquivalenceClass>>();
					if (DEBUG2)
						System.err.println("\nnext succ2hier: " + succ2hier);
					final int size = succ2hier.size();
					if (size > 0) {
						// linear split only sensible with more than one set
						if (size > 1) {
							for (final Entry<Set<EquivalenceClass>, Set<STATE>>
									innerEntry : succ2hier.entrySet()) {
								final Set<STATE> hiers = innerEntry.getValue();
								
								// local hierarchical split
								if (DEBUG2)
									System.err.println(
											"local hierarchical split: " +
													hiers);
								
								assert hiers.iterator().hasNext();
								final SplittingGraph graph = ec2graph.get(
										m_partition.m_state2EquivalenceClass.
										get(hiers.iterator().next()));
								visitedGraphs.add(graph);
								
								graph.split(hiers);
								
								// global linear split collection
								succs.add(innerEntry.getKey());
							}
						}
						// singleton sets are ignored
						else {
							if (DEBUG2)
								System.err.println("ignoring, only one");
							
							// global linear split collection
							assert (succ2hier.keySet().iterator().hasNext());
							succs.add(succ2hier.keySet().iterator().next());
						}
						
						// global linear split collection
						Set<STATE> gLins = gSucc2states.get(succs);
						if (gLins == null) {
							gLins = new HashSet<STATE>();
							gSucc2states.put(succs, gLins);
						}
						gLins.add(lin);
						if (DEBUG2) {
							System.err.println("succs: " + succs);
							System.err.println("gLins: " + gLins);
						}
					}
					else {
						if (DEBUG2)
							System.err.println("ignoring, none");
					}
					
					resetGraphSets(visitedGraphs, ec2graph);
				}
				
				// global linear split
				if (DEBUG2)
					System.err.println("\nglobal linear splits: " +
							gHierEc2Succ2states);
				for (final HashMap<HashSet<Set<EquivalenceClass>>,
						Set<STATE>> succ2gLins :
						gHierEc2Succ2states.values()) {
					if (succ2gLins.size() > 1) {
						for (final Set<STATE> gLins : succ2gLins.values()) {
							if (DEBUG2)
								System.err.println("global linear split: " +
										gLins);
							
							assert gLins.iterator().hasNext();
							final SplittingGraph graph = ec2graph.get(
									m_partition.m_state2EquivalenceClass.
									get(gLins.iterator().next()));
							visitedGraphs.add(graph);
							graph.split(gLins);
						}
						
						resetGraphSets(visitedGraphs, ec2graph);
					}
					else {
						if (DEBUG2)
							System.err.println("ignoring, only " +
									succ2gLins.size());
					}
				}
			}
		}
		
		// local linear split and global hierarchical split
		for (final HashMap<STATE, HashMap<Set<EquivalenceClass>, Set<STATE>>>
				hier2succ2lin : listHier2succ2lin) {
			if (DEBUG2)
				System.err.println("\n\nconsider hier2succ2lin " +
						hier2succ2lin);
			final HashMap<HashSet<Set<EquivalenceClass>>, Set<STATE>>
					gSucc2states =
					new HashMap<HashSet<Set<EquivalenceClass>>, Set<STATE>>();
			
			for (final Entry<STATE, HashMap<Set<EquivalenceClass>, Set<STATE>>>
					entry : hier2succ2lin.entrySet()) {
				final HashSet<Set<EquivalenceClass>> succs =
						new HashSet<Set<EquivalenceClass>>();
				if (DEBUG2)
					System.err.println("\nnext entry: " + entry);
				final HashMap<Set<EquivalenceClass>, Set<STATE>> succ2lin =
						entry.getValue();
				final int size = succ2lin.size();
				if (size > 0) {
					// linear split only sensible with more than one set
					if (size > 1) {
						for (final Entry<Set<EquivalenceClass>, Set<STATE>>
								innerEntry : succ2lin.entrySet()) {
							final Set<STATE> lins = innerEntry.getValue();
							
							// local linear split
							if (DEBUG2)
								System.err.println("local linear split: " +
										lins);
							
							assert lins.iterator().hasNext();
							final SplittingGraph graph = ec2graph.get(
									m_partition.m_state2EquivalenceClass.
									get(lins.iterator().next()));
							visitedGraphs.add(graph);
							graph.split(lins);
							
							// global hierarchical split collection
							succs.add(innerEntry.getKey());
						}
					}
					// singleton sets are ignored
					else {
						if (DEBUG2)
							System.err.println("ignoring, only one");
						
						// global hierarchical split collection
						assert (succ2lin.keySet().iterator().hasNext());
						succs.add(succ2lin.keySet().iterator().next());
					}
					
					// global hierarchical split collection
					Set<STATE> gHiers = gSucc2states.get(succs);
					if (gHiers == null) {
						gHiers = new HashSet<STATE>();
						gSucc2states.put(succs, gHiers);
					}
					gHiers.add(entry.getKey());
					if (DEBUG2) {
						System.err.println("succs: " + succs);
						System.err.println("gHiers: " + gHiers);
					}
				}
				else {
					if (DEBUG2)
						System.err.println("ignoring, none");
				}
				
				resetGraphSets(visitedGraphs, ec2graph);
			}
			
			// global hierarchical split
			// TODO<globalLinearSplit> this specific split may not be necessary
			if (DEBUG2)
				System.err.println("\nglobal hierarchical splits: " +
						gSucc2states);
			if (gSucc2states.size() > 1) {
				for (final Set<STATE> gHiers : gSucc2states.values()) {
					if (DEBUG2)
						System.err.println("global hierarchical split: " +
								gHiers);
					
					assert gHiers.iterator().hasNext();
					final SplittingGraph graph = ec2graph.get(
							m_partition.m_state2EquivalenceClass.
							get(gHiers.iterator().next()));
					visitedGraphs.add(graph);
					graph.split(gHiers);
				}
			}
			else {
				if (DEBUG2)
					System.err.println("ignoring, only " +
							gSucc2states.size());
			}
			
			resetGraphSets(visitedGraphs, ec2graph);
		}
		
		if (DEBUG2) {
			System.err.println("\n\nfinal graphs:");
			for (SplittingGraph graph : ec2graph.values()) {
				System.err.println(graph);
			}
		}
		
		splitGraphs(ec2graph.values());
	}
	
	/**
	 * This method splits states according to the graph coloring.
	 * 
	 * This is a naive split, but solving this problem optimally is NP-hard.
	 * However, even with the optimal solution it is not guaranteed that the
	 * split is the best, since neutral states can turn out to behave badly in
	 * the assigned equivalence class.
	 *
	 * @param graphs the graphs
	 */
	private void splitGraphs(Collection<SplittingGraph> graphs) {
		if (DEBUG2)
			System.err.println("\n\nstarting the coloring");
		
		for (final SplittingGraph graph : graphs) {
			if (DEBUG2)
				System.err.println("\nnext graph: " + graph);
			final int size = graph.m_graph.length;
			assert (size > 0);
			
			// ignore singleton equivalence classes
			if (size == 1) {
				continue;
			}
			
			final ArrayList<HashSet<Integer>> colors =
					new ArrayList<HashSet<Integer>>(size);
			
			// assign first color to first state
			graph.m_colors[0] = 1;
			HashSet<Integer> color0 = new HashSet<Integer>();
			color0.add(0);
			colors.add(color0);
			color0 = null;
			
			for (int state = 1; state < size; ++state) {
				// take the next state
				if (DEBUG2)
					System.err.println("next state: " + state +
							" = " + graph.m_index2state.get(state));
				
				// find blocked colors
				final HashSet<Integer> neighborColors = new HashSet<Integer>(
						computeHashSetCapacity(colors.size()));
				final Iterator<Integer> neighbors =
						graph.neighborsIterator(state);
				while (neighbors.hasNext()) {
					final int neighbor = neighbors.next();
					assert (neighbor != state);
					
					if (DEBUG2)
						System.err.println("next neighbor: " + neighbor +
								" = " + graph.m_index2state.get(neighbor));
					
					// not yet assigned, ignore it
					if (neighbor > state) {
						continue;
					}
					
					assert (graph.m_colors[neighbor] > 0) &&
							graph.m_colors[neighbor] <= colors.size();
					neighborColors.add(graph.m_colors[neighbor]);
				}
				
				// no color fit, create a new color
				if (neighborColors.size() == colors.size()) {
					final int newColorValue = colors.size() + 1;
					graph.m_colors[state] = newColorValue;
					HashSet<Integer> newColor = new HashSet<Integer>();
					newColor.add(state);
					colors.add(newColorValue - 1, newColor);
				}
				// find appropriate color (must exist)
				else {
					int color = 0;
					while (true) {
						// try current color
						if (neighborColors.contains(++color)) {
							continue;
						}
						
						// no conflict, use the current color
						assert (color <= colors.size());
						graph.m_colors[state] = color;
						colors.get(color - 1).add(state);
						break;
					}
				}
			}
			
			if (DEBUG2)
				System.err.println("all colors are set: " + colors);
			
			// split according to the colors (first color not necessary)
			for (int i = colors.size() - 1; i > 0; --i) {
				final HashSet<Integer> color = colors.get(i);
				final ArrayList<STATE> states =
						new ArrayList<STATE>(color.size());
				int index = -1;
				for (final int state : color) {
					states.add(++index, graph.m_index2state.get(state));
				}
				
				m_partition.splitEquivalenceClasses(states);
				if (DEBUG2)
					System.err.println("splitting states: " + states);
			}
		}
		
		if (DEBUG2)
			System.err.println("finished return split");
	}
	
	/**
	 * This method analyzes the given information and does the splitting for
	 * return edges.
	 * Beforehand all the necessary information of which states have to be
	 * separated has been collected. Here this is extracted from the data
	 * structures and the splitting is invoked.
	 * 
	 * The problem here are the neutral states: The idea is to keep as many of
	 * them as possible without a split. In general, this is hard.
	 * 
	 * This is a naive version that separates each set and does not consider
	 * better sharing of neutral states.
	 * 
	 * TODO<returnSplit> use more efficient split that exploits that the
	 *                   equivalence class is always the same
	 * 
	 * TODO<returnSplit> stop when A has been split?
	 *
	 * @param listLin2succ2hier list of linears to successors to hierarchicals
	 * @param listHier2succ2lin list of hierarchicals to successors to linears
	 */
	// TODO<remove>
	private void splitReturnHelperNaive(final List<HashMap<STATE,
			HashMap<Set<EquivalenceClass>, Set<STATE>>>> listLin2succ2hier,
			final List<HashMap<STATE, HashMap<Set<EquivalenceClass>,
			Set<STATE>>>> listHier2succ2lin) {
		if (DEBUG2) {
			System.err.println("listLin2succ2hier: " + listLin2succ2hier);
			System.err.println("listHier2succ2lin: " + listHier2succ2lin);
		}
		
		HashMap<HashSet<Set<EquivalenceClass>>, Set<STATE>> gSucc2states =
				new HashMap<HashSet<Set<EquivalenceClass>>, Set<STATE>>();
		
		// local hierarchical split and global linear split
		for (final HashMap<STATE, HashMap<Set<EquivalenceClass>, Set<STATE>>>
				lin2succ2hier : listLin2succ2hier) {
			final HashSet<Set<EquivalenceClass>> succs =
					new HashSet<Set<EquivalenceClass>>();
			
			for (final Entry<STATE, HashMap<Set<EquivalenceClass>, Set<STATE>>>
					entry : lin2succ2hier.entrySet()) {
				final HashMap<Set<EquivalenceClass>, Set<STATE>> succ2hier =
						entry.getValue();
				final int size = succ2hier.size();
				if (size > 0) {
					if (size > 1) {
						for (final Entry<Set<EquivalenceClass>, Set<STATE>>
								innerEntry : succ2hier.entrySet()) {
							// local hierarchical split
							m_partition.splitEquivalenceClasses(
									innerEntry.getValue());
							if (DEBUG2)
								System.err.println(
										"local hierarchical split: " +
										innerEntry.getValue());
							
							// global linear split collection
							succs.add(innerEntry.getKey());
						}
					}
					else {
						assert (succ2hier.keySet().iterator().hasNext());
						succs.add(succ2hier.keySet().iterator().next());
					}
					
					// global linear split collection
					Set<STATE> gLins = gSucc2states.get(succs);
					if (gLins == null) {
						gLins = new HashSet<STATE>();
						gSucc2states.put(succs, gLins);
					}
					gLins.add(entry.getKey());
				}
			}
			
			// global linear split
			// TODO<returnSplit> this specific split is probably not necessary
			if (gSucc2states.size() > 1) {
				for (final Set<STATE> gLins : gSucc2states.values()) {
					if (DEBUG2)
						System.err.println("global linear split: " + gLins);
					m_partition.splitEquivalenceClasses(gLins);
				}
			}
		}
		
		gSucc2states =
				new HashMap<HashSet<Set<EquivalenceClass>>, Set<STATE>>();
		
		// local linear split and global hierarchical split
		for (final HashMap<STATE, HashMap<Set<EquivalenceClass>, Set<STATE>>>
				hier2succ2lin : listHier2succ2lin) {
			final HashSet<Set<EquivalenceClass>> succs =
					new HashSet<Set<EquivalenceClass>>();
			
			for (final Entry<STATE, HashMap<Set<EquivalenceClass>, Set<STATE>>>
					entry : hier2succ2lin.entrySet()) {
				final HashMap<Set<EquivalenceClass>, Set<STATE>> succ2lin =
						entry.getValue();
				final int size = succ2lin.size();
				if (size > 0) {
					if (size > 1) {
						for (final Entry<Set<EquivalenceClass>, Set<STATE>>
								innerEntry : succ2lin.entrySet()) {
							// local linear split
							m_partition.splitEquivalenceClasses(
									innerEntry.getValue());
							if (DEBUG2)
								System.err.println("local linear split: " +
										innerEntry.getValue());
							
							// global hierarchical split collection
							succs.add(innerEntry.getKey());
						}
					}
					else {
						assert (succ2lin.keySet().iterator().hasNext());
						succs.add(succ2lin.keySet().iterator().next());
					}
					
					// global hierarchical split collection
					Set<STATE> gHiers = gSucc2states.get(succs);
					if (gHiers == null) {
						gHiers = new HashSet<STATE>();
						gSucc2states.put(succs, gHiers);
					}
					gHiers.add(entry.getKey());
				}
			}
			
			// global hierarchical split
			if (gSucc2states.size() > 1) {
				for (final Set<STATE> gHiers : gSucc2states.values()) {
					if (DEBUG2)
						System.err.println("global hierarchical split: " + gHiers);
					m_partition.splitEquivalenceClasses(gHiers);
				}
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
	// TODO<remove>
	private void splitReturnPredecessorsOld(final EquivalenceClass a) {
		// recognize when the splitter set was split itself
		assert (a.m_incomingRet != EIncomingStatus.inWL);
		
		// collect incoming return transitions
		final HashSet<STATE> hiers = new HashSet<STATE>();
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
				hiers.add(edge.getHierPred());
			}
		}
		
		// remember that this equivalence class has no incoming transitions
		if (letter2lin.isEmpty()) {
			a.m_incomingRet = EIncomingStatus.none;
			if (STATISTICS)
				++m_noIncomingTransitions;
		}
		else {
			if (STATISTICS)
				++m_incomingTransitions;
			
			/*
			 * Find the predecessor equivalence classes.
			 * Since the equivalence classes can be split, create immutable
			 * data structures here.
			 */
			final HashMap<LETTER, LinkedList<ArrayList<STATE>>> letter2linList
					= new HashMap<LETTER, LinkedList<ArrayList<STATE>>>();
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
					splitLinPred(lins, hiers, a, letter);
					
					// splitter set was split, stop
					if ((a.m_incomingInt == EIncomingStatus.inWL) ||
							(a.m_incomingCall == EIncomingStatus.inWL)) {
						return;
					}
					
					// split hierarchical predecessors
					splitHierPred(lins, hiers, a, letter);
					
					// splitter set was split, stop
					if ((a.m_incomingInt == EIncomingStatus.inWL) ||
							(a.m_incomingCall == EIncomingStatus.inWL)) {
						return;
					}
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
	 * @param lins the linear predecessor states
	 * @param hiers the hierarchical predecessor states
	 * @param succEc the successor equivalence class
	 * @param letter the letter
	 */
	private void splitLinPred(final Collection<STATE> lins,
			final Collection<STATE> hiers, final EquivalenceClass succEc,
			final LETTER letter) {
		// split by successor equivalence class wrt. hierarchical predecessor
		final int sizeOfLin = lins.size();
		final HashSet<STATE> negativeStates = new HashSet<STATE>();
		for (final STATE hier : hiers) {
			final HashMap<EquivalenceClass, HashSet<STATE>> succ2lin =
					new HashMap<EquivalenceClass, HashSet<STATE>>();
			final HashSet<STATE> neutralStates = new HashSet<STATE>();
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
						if (! negativeStates.contains(lin)) {
							neutralStates.add(lin);
						}
					}
					else {
						negativeStates.add(lin);
						neutralStates.remove(lin);
					}
				}
			}
			
			// split
			final Iterator<HashSet<STATE>> positives =
					succ2lin.values().iterator();
			// positive states
			if (positives.hasNext()) {
				do {
					final HashSet<STATE> positiveStates = positives.next();
					/*
					 * TODO<TIEBREAK> what to do?
					 *                Currently neutral states are seen
					 *                positive.
					 */
					final SplitCombinator combinator =
							new SplitCombinator(positiveStates, neutralStates);
					
					// ignore unaffecting splits
					if (combinator.size() < sizeOfLin) {
						m_partition.splitEquivalenceClasses(combinator);
					}
					else {
						if (DEBUG)
							System.out.println("combinator " + combinator +
									" was ignored");
					}
				} while (positives.hasNext());
			}
			// no positive states, split negative states
			else {
				if (! negativeStates.isEmpty()) {
					m_partition.splitEquivalenceClasses(negativeStates);
					if (DEBUG)
						System.out.println(
								"splitting negative states only: " +
										negativeStates);
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
	 * @param lins the linear predecessor states
	 * @param hiers the hierarchical predecessor states
	 * @param succEc the successor equivalence class
	 * @param letter the letter
	 */
	private void splitHierPred(final Iterable<STATE> lins,
			final Collection<STATE> hiers, final EquivalenceClass succEc,
			final LETTER letter) {
		// find hierarchical predecessor equivalence classes
		final HashSet<EquivalenceClass> hierEcs =
				new HashSet<EquivalenceClass>();
		for (final STATE hier : hiers) {
			hierEcs.add(m_partition.m_state2EquivalenceClass.get(hier));
		}
		
		final HashSet<STATE> negativeStates = new HashSet<STATE>();
		for (final STATE lin : lins) {
			final HashSet<STATE> neutralStates = new HashSet<STATE>();
			
			// check each hierarchical predecessor
			for (final EquivalenceClass hierEc : hierEcs) {
				final int sizeOfHier = hierEc.m_states.size();
				
				final HashMap<HashSet<EquivalenceClass>, HashSet<STATE>>
						reachedEc2hier = new HashMap<HashSet<EquivalenceClass>,
						HashSet<STATE>>();
				for (final STATE hier : hierEc.m_states) {
					// collect all reached equivalence classes
					final Iterator<OutgoingReturnTransition<LETTER, STATE>>
							edges = m_operand.returnSucccessors(lin, hier,
									letter).iterator();
					if (edges.hasNext()) {
						final HashSet<EquivalenceClass> reached =
								new HashSet<EquivalenceClass>();
						do {
							reached.add(m_partition.m_state2EquivalenceClass.
									get(edges.next().getSucc()));
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
							if (! negativeStates.contains(hier)) {
								neutralStates.add(hier);
							}
						}
						else {
							negativeStates.add(hier);
							neutralStates.remove(hier);
						}
					}
				}
				
				// split
				final Iterator<HashSet<STATE>> positives =
						reachedEc2hier.values().iterator();
				// positive states
				if (positives.hasNext()) {
					do {
						final HashSet<STATE> positiveStates = positives.next();
						/*
						 * TODO<TIEBREAK> what to do?
						 *                Currently neutral states are seen
						 *                positive.
						 */
						final SplitCombinator combinator =
								new SplitCombinator(positiveStates,
										neutralStates);
						
						// ignore unaffecting splits
						if (combinator.size() < sizeOfHier) {
							m_partition.splitEquivalenceClasses(combinator);
						}
						else {
							if (DEBUG)
								System.out.println("combinator " + combinator +
										" was ignored");
						}
					} while (positives.hasNext());
				}
				// no positive states, split negative states
				else {
					if (! negativeStates.isEmpty()) {
						m_partition.splitEquivalenceClasses(negativeStates);
						if (DEBUG)
							System.out.println(
									"splitting negative states only: " +
											negativeStates);
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
	 * This enum is used to tell for an equivalence class whether it contains
	 * incoming transitions. Since it is expensive to compute this each time,
	 * only the answer "no" is correct.
	 * This status is inherited by the two resulting equivalence classes after
	 * a split.
	 * The idea is to not insert such equivalence classes in the work list, for
	 * which it is known that there are no incoming transitions.
	 * The status is updated as a byproduct after the search for transitions.
	 */
	private enum EIncomingStatus {
		/** unknown whether there are incoming transitions */
		unknown,
		
		/** equivalence class is in work list */
		inWL,
		
		/** there are no incoming transitions */
		none
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
	
	/**
	 * TODO<comment>
	 */
	private class SplittingGraph {
		private ArrayList<Set<STATE>> m_sets; // TODO<remove> remove later
		private final HashMap<STATE, Integer> m_state2index;
		private final HashMap<Integer, STATE> m_index2state;
		private final int[] m_colors;
		private boolean[][] m_graph;
		
		public SplittingGraph(final Set<STATE> states) {
			final int size = states.size();
			m_sets = new ArrayList<Set<STATE>>(size);
			m_state2index = new HashMap<STATE, Integer>(
					computeHashSetCapacity(size));
			m_index2state = new HashMap<Integer, STATE>(
					computeHashSetCapacity(size));
			m_colors = new int[size];
			
			int index = -1;
			for (final STATE state : states) {
				m_state2index.put(state, ++index);
				m_index2state.put(index, state);
			}
			
			m_graph = new boolean[size][];
			for (int i = 0; i < size; ++i) {
				m_graph[i] = new boolean[i];
			}
		}
		
		private void split(final Set<STATE> states) {
			if (m_sets.size() > 0) {
				final Iterator<STATE> it = setsIterator();
				while (it.hasNext()) {
					final STATE oldState = it.next();
					final int oldStateIndex;
					
					/*
					 * TODO<bug> this is a bug currently
					 */
					try{
						oldStateIndex = m_state2index.get(oldState);
					}
					catch (NullPointerException e) {
						throw new AssertionError("NPE with oldState: " +
								oldState);
					}
					for (final STATE state : states) {
						try{
							assert (! oldState.equals(state)) &&
								(m_state2index.containsKey(state)) &&
								(oldStateIndex != m_state2index.get(state));
						} catch (AssertionError e) {
							throw new AssertionError("oldState vs. state: " +
									oldState + state);
						}
						
						setConnected(oldStateIndex, m_state2index.get(state));
					}
				}
			}
			m_sets.add(states);
			
			if (DEBUG2) {
				final StringBuilder builder = new StringBuilder();
				builder.append("added new set: ");
				builder.append(states);
				builder.append("\ngraph so far:");
				for (int i = 0; i < m_graph.length; ++i) {
					final boolean[] row = m_graph[i];
					for (int j = 0; j < i; ++j) {
						builder.append(row[j] ? 1 : 0);
						builder.append(" ");
					}
					if (i < m_graph.length - 1) {
						builder.append("\n");
					}
				}
				System.err.println(builder.toString());
			}
		}
		
		private void setConnected(final int i, final int j) {
			assert (i >= 0) && (j >= 0) && (i != j) &&
					(i < m_graph.length) && (j < m_graph.length);
			
			if (i < j) {
				m_graph[j][i] = true;
			}
			else {
				m_graph[i][j] = true;
			}
		}
		
		private Iterator<Integer> neighborsIterator(final int i) {
			assert (i >= 0) && (i < m_graph.length);
			return new Iterator<Integer>() {
				private int m_i = (i == 0) ? 1 : i;
				private int m_j = -1;
				private boolean m_inColumn = (i == 0);
				private int m_next;
				
				@Override
				public boolean hasNext() {
					if (! m_inColumn) {
						while (++m_j < m_i) {
							if (m_graph[m_i][m_j]) {
								m_next = m_j;
								return true;
							}
						}
						m_inColumn = true;
					}
					while (++m_i < m_graph.length) {
						if (m_graph[m_i][m_j]) {
							m_next = m_i;
							return true;
						}
					}
					return false;
				}
				
				@Override
				public Integer next() {
					assert (m_next >= 0) && (m_next < m_graph.length) :
						"hasNext() must be used.";
					return m_next;
				}
				
				@Override
				public void remove() {
					throw new UnsupportedOperationException(
							"Removing is not allowed.");
				}
			};
		}
		
		private Iterator<STATE> setsIterator() {
			assert (m_sets.size() > 0) &&
					(m_sets.get(m_sets.size() - 1) != null) &&
					(m_sets.get(m_sets.size() - 1).iterator().hasNext());
			
			return new Iterator<STATE>() {
				private int m_index = m_sets.size() - 1;
				private Iterator<STATE> m_iterator =
						m_sets.get(m_index).iterator();
				private STATE m_next;
				
				@Override
				public boolean hasNext() {
					if (m_iterator.hasNext()) {
						m_next = m_iterator.next();
					}
					else if (m_index > 0) {
						--m_index;
						m_iterator = m_sets.get(m_index).iterator();
					}
					else {
						m_next = null;
						return false;
					}
					return true;
				}
				
				@Override
				public STATE next() {
					assert (m_next != null) : "hasNext() must be used.";
					return m_next;
				}
				
				@Override
				public void remove() {
					throw new UnsupportedOperationException(
							"Removing is not allowed.");
				}
			};
		}
		
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			
			builder.append("mapping: ");
			builder.append(m_state2index);
			builder.append("\ncolors: [");
			for (int i = 0; i < m_colors.length; ++i) {
				builder.append(m_colors[i]);
				builder.append(", ");
			}
			builder.append("]\nsets: ");
			builder.append(m_sets);
			builder.append("\ngraph:");
			for (int i = 0; i < m_graph.length; ++i) {
				final boolean[] row = m_graph[i];
				for (int j = 0; j < i; ++j) {
					builder.append(row[j] ? 1 : 0);
					builder.append(" ");
				}
				if (i < m_graph.length - 1) {
					builder.append("\n");
				}
			}
			
			return builder.toString();
		}
	}
	
	/**
	 * This method resets the state sets in the graphs.
	 *
	 * @param graphs the graphs to reset
	 * @param ec2graph all graphs for assertion checking
	 */
	private void resetGraphSets(final HashSet<SplittingGraph> graphs,
			final HashMap<EquivalenceClass, SplittingGraph> ec2graph) {
		for (final SplittingGraph graph : graphs) {
			graph.m_sets.clear();
			
			if (DEBUG2)
				System.err.println("  resetting graph " + graph);
		}
		graphs.clear();
		
		assert (allGraphsCleared(ec2graph.values()));
	}
	
	/**
	 * This method checks that all graphs have their sets cleared.
	 *
	 * @param allGraphs all graphs for assertion checking
	 * @return true iff all sets are cleared
	 */
	private boolean allGraphsCleared(
			final Collection<SplittingGraph> allGraphs) {
		for (final SplittingGraph graph : allGraphs) {
			if (graph.m_sets.size() > 0) {
				return false;
			}
		}
		return true;
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
		private void addEc(final Set<STATE> module) {
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
			final EquivalenceClass ec = new EquivalenceClass(module);
			m_equivalenceClasses.add(ec);
			return ec;
		}
		
		/**
		 * This method adds an equivalence class to the partition that resulted
		 * from a split.
		 *
		 * @param parent the parent equivalence class
		 * @return the equivalence class
		 */
		private EquivalenceClass addEcHelper(final EquivalenceClass parent) {
			final EquivalenceClass ec = new EquivalenceClass(parent);
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
					++m_splitsWithoutChange;
					
					// reset equivalence class
					ec.reset();
				}
				// do a split
				else {
					if (DEBUG)
						System.out.println("EC was split " + ec);
					++m_splitsWithChange;
					
					splitOccurred = true;
					final Set<STATE> intersection = ec.m_intersection;
					final EquivalenceClass newEc = addEcHelper(ec);
					for (STATE state : intersection) {
						m_state2EquivalenceClass.put(state, newEc);
					}
					
					// put ec in work lists if not already in there
					if (ec.m_incomingInt == EIncomingStatus.unknown) {
						ec.m_incomingInt = EIncomingStatus.inWL;
						m_workListIntCall.add(ec);
					}
					if (ec.m_incomingCall == EIncomingStatus.unknown) {
						ec.m_incomingCall = EIncomingStatus.inWL;
						if (ec.m_incomingInt != EIncomingStatus.inWL) {
							m_workListIntCall.add(ec);
						}
					}
					if (ec.m_incomingRet == EIncomingStatus.unknown) {
						ec.m_incomingRet = EIncomingStatus.inWL;
						m_workListRet.add(ec);
					}
					
					// reset equivalence class (before 
					ec.reset();
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
		// intersection set that finally becomes a new equivalence class
		private Set<STATE> m_intersection;
		// status regarding incoming transitions
		private EIncomingStatus m_incomingInt, m_incomingCall, m_incomingRet;
		
		/**
		 * @param states the set of states for the equivalence class
		 */
		public EquivalenceClass(final Set<STATE> states) {
			m_states = states;
			reset();
			m_incomingInt = EIncomingStatus.inWL;
			m_incomingCall = EIncomingStatus.inWL;
			m_workListIntCall.add(this);
			m_incomingRet = EIncomingStatus.inWL;
			m_workListRet.add(this);
		}
		
		public EquivalenceClass(final EquivalenceClass parent) {
			m_states = parent.m_intersection;
			reset();
			switch (parent.m_incomingInt) {
				case unknown:
				case inWL:
					m_incomingInt = EIncomingStatus.inWL;
					m_workListIntCall.add(this);
					break;
				case none:
					m_incomingInt = EIncomingStatus.none;
			}
			switch (parent.m_incomingCall) {
				case unknown:
				case inWL:
					m_incomingCall = EIncomingStatus.inWL;
					if (m_incomingInt != EIncomingStatus.inWL) {
						m_workListIntCall.add(this);
					}
					break;
				case none:
					m_incomingCall = EIncomingStatus.none;
			}
			switch (parent.m_incomingRet) {
				case unknown:
				case inWL:
					m_incomingRet = EIncomingStatus.inWL;
					m_workListRet.add(this);
					break;
				case none:
					m_incomingRet = EIncomingStatus.none;
					break;
			}
		}
		
		/**
		 * This constructor is reserved for the placeholder equivalence class.
		 */
		private EquivalenceClass() {
			m_states = null;
			m_intersection = null;
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
			if (m_states == null) {
				return "negative equivalence class";
			}
			
			if (!DEBUG && DEBUG2) {
				return toStringShort();
			}
			
			final StringBuilder builder = new StringBuilder();
			String append = "";
			
			builder.append("<[");
			builder.append(m_incomingInt);
			builder.append(",");
			builder.append(m_incomingCall);
			builder.append(",");
			builder.append(m_incomingRet);
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
		
		/**
		 * This method returns a short representation of the equivalence class
		 * with only the states.
		 * States in the intersection are not visible.
		 *
		 * @return a short string representation of the states
		 */
		public String toStringShort() {
			if (m_states == null) {
				return "negative equivalence class";
			}
			
			final StringBuilder builder = new StringBuilder();
			String append = "";
			
			builder.append("<");
			for (final STATE state : m_states) {
				builder.append(append);
				append = ", ";
				builder.append(state);
			}
			builder.append(">");
			
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
			if (DEBUG)
				System.out.println("\npopping from IntCall WL: " + ec);
			return ec;
		}
		
		@Override
		public void add(final EquivalenceClass ec) {
			assert ((ec.m_incomingInt == EIncomingStatus.inWL) ||
					(ec.m_incomingCall == EIncomingStatus.inWL));
			if (DEBUG)
				System.out.println("adding of IntCall WL: " + ec);
			super.add(ec);
		}
	}
	
	/**
	 * This class implements the work list for predecessor return splits.
	 */
	private class WorkListRet extends AWorkList {
		@Override
		public EquivalenceClass next() {
			final EquivalenceClass ec = m_queue.poll();
			ec.m_incomingRet = EIncomingStatus.unknown;
			if (DEBUG)
				System.out.println("\npopping from return WL: " + ec);
			return ec;
		}
		
		@Override
		public void add(final EquivalenceClass ec) {
			assert (ec.m_incomingRet == EIncomingStatus.inWL);
			if (DEBUG)
				System.out.println("adding of return WL: " + ec);
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
						HashMap<STATE, HashSet<STATE>> hier2succs =
								returns.get(letter);
						if (hier2succs == null) {
							hier2succs = new HashMap<STATE, HashSet<STATE>>();
							returns.put(letter, hier2succs);
						}
						final STATE hier = ec2state.get(
								m_partition.m_state2EquivalenceClass.get(
										edge.getHierPred()));
						HashSet<STATE> succs = hier2succs.get(hier);
						if (succs == null) {
							succs = new HashSet<STATE>();
							hier2succs.put(hier, succs);
						}
						succs.add(ec2state.get(m_partition.
								m_state2EquivalenceClass.get(edge.getSucc())));
					}
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
			ResultChecker.writeToFileIfPreferred(operationName() + " failed",
					"", m_operand);
		}
		s_Logger.info("Finished testing correctness of " + operationName());
		return correct;
	}
	
	// --- [end] framework methods --- //
}