package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
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
 * <DoubleDecker> check this?
 * 
 * <splittingPolicy> currently all internal and call splits consider the
 *                   same splitter set
 *                   this could be improved by stopping the split whenever the
 *                   splitter set itself is split
 *                   but this somehow counters the automata implementation,
 *                   since finding the predecessors is expensive...
 * 
 * <splitOutgoing> possible improvement: at the beginning split all states
 *                 with respect to outgoing symbols -> necessary condition
 * 
 * <constructAutomaton> how to do this efficiently in the end?
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
	final EquivalenceClass m_negativeClass;
	// simulates the output automaton
	private ShrinkNwaResult m_result;
	
	// TODO<debug>
	private final boolean DEBUG = false;
	private final boolean DEBUG3 = false;
	
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
	private final StateFactory<STATE> m_stateFactory;
	
	/**
	 * creates a copy of operand
	 * 
	 * @param operand preprocessed nested word automaton
	 * preprocessing: dead end and unreachable states/transitions removed
	 * @throws OperationCanceledException if cancel signal is received
	 */
	public ShrinkNwa(final INestedWordAutomaton<LETTER,STATE> operand)
			throws OperationCanceledException {
		this(operand, null, null, false, false);
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
	 * @param stateFactory used for Hoare annotation
	 * @param includeMapping true iff mapping old to new state is needed
	 * @param isFiniteAutomaton true iff automaton is a finite automaton
	 * @throws OperationCanceledException if cancel signal is received
	 */
	@SuppressWarnings("unchecked")
	public ShrinkNwa(
			final INestedWordAutomaton<LETTER,STATE> operand,
			final Collection<Set<STATE>> equivalenceClasses,
			final StateFactory<STATE> stateFactory,
			final boolean includeMapping,
			final boolean isFiniteAutomaton)
					throws OperationCanceledException {
		m_operand = operand;
		// TODO<DoubleDecker> check this?
		m_doubleDecker = (IDoubleDeckerAutomaton<LETTER, STATE>)m_operand;
		m_stateFactory = (stateFactory == null)
				? m_operand.getStateFactory()
				: stateFactory;
		m_partition = new Partition();
		m_workListIntCall = new WorkListIntCall();
		m_workListRet = new WorkListRet();
		m_negativeSet = new HashSet<EquivalenceClass>();
		m_negativeClass = new EquivalenceClass();
		m_negativeSet.add(m_negativeClass);
		
		// must be the last part of the constructor
		s_Logger.info(startMessage());
		minimize(isFiniteAutomaton, equivalenceClasses, includeMapping);
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
	 * @param includeMapping true iff mapping old to new state is needed
	 * @throws OperationCanceledException if cancel signal is received
	 */
	private void minimize(final boolean isFiniteAutomaton,
			final Iterable<Set<STATE>> modules, final boolean includeMapping)
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
					
					splitReturnPredecessors(a);
				}
				else {
					break outer;
				}
			}
			
			// automaton construction
			constructAutomaton(includeMapping);
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
			assert assertStatesSeparation(modules) :
				"The states in the initial modules are not separated with " +
				"respect to their final status.";
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
	 * This method implements the return split.
	 * 
	 * For each return symbol respectively first find the predecessor states
	 * (both linear and hierarchical). With this mark the simple splits for
	 * linear and hierarchical states. Then find violations due to the neutral
	 * states and break ties on which states to split there. In the end execute
	 * the whole splits.
	 *
	 * @param a the splitter equivalence class
	 */
	private void splitReturnPredecessors(final EquivalenceClass a) {
		assert (a.m_incomingRet != EIncomingStatus.inWL);
		
		// data structures for the linear and hierarchical predecessors
		final HashMap<LETTER, HashMap<STATE, HashSet<EquivalenceClass>>>
			letter2lin2hierEcSet = new HashMap<LETTER, HashMap<STATE,
			HashSet<EquivalenceClass>>>();
		final HashMap<LETTER, HashMap<STATE, HashSet<EquivalenceClass>>>
			letter2hier2linEcSet = new HashMap<LETTER, HashMap<STATE,
			HashSet<EquivalenceClass>>>();
		
		// collect incoming return transitions and update data structures
		splitReturnFindTransitions(a, letter2lin2hierEcSet,
				letter2hier2linEcSet);
		
		assert ((letter2lin2hierEcSet.isEmpty() &&
					letter2hier2linEcSet.isEmpty()) ||
				(! letter2lin2hierEcSet.isEmpty() &&
						! letter2hier2linEcSet.isEmpty()));
		
		// no return transitions found, remember that
		if (letter2lin2hierEcSet.isEmpty()) {
			a.m_incomingRet = EIncomingStatus.none;
			if (STATISTICS)
				++m_noIncomingTransitions;
			
			return;
		}
		
		if (DEBUG3) {
			final StringBuilder builder = new StringBuilder();
			builder.append("\n--- new return split from A: ");
			builder.append(a);
			builder.append("\n letter2lin2hierEcSet: ");
			builder.append(letter2lin2hierEcSet);
			builder.append("\n letter2hier2linEcSet: ");
			builder.append(letter2hier2linEcSet);
			System.err.println(builder.toString());
		}
		
		// remember all equivalence classes marked for splitting
		final HashSet<EquivalenceClass> splitEquivalenceClasses =
				new HashSet<EquivalenceClass>();
		
		// collect trivial linear splits
		splitReturnLin(letter2hier2linEcSet, splitEquivalenceClasses);
		
		// collect trivial hierarchical splits
		splitReturnHier(letter2lin2hierEcSet, splitEquivalenceClasses);
		
		// collect complicated mixed splits
		splitReturnMixed(letter2hier2linEcSet, splitEquivalenceClasses);
		
		// execute the splits
		splitReturnExecute(splitEquivalenceClasses);
	}
	
	/**
	 * This method finds all incoming return transitions given a splitter and
	 * updates the data structures accordingly.
	 * 
	 * TODO<singletons> detect singleton equivalence classes and do not add
	 *                  them to the splitting lists
	 * 
	 * @param a splitter equivalence class
	 * @param letter2lin2hierEcSet mapping for hierarchical split
	 * @param letter2hier2linEcSet mapping for linear split
	 */
	private void splitReturnFindTransitions(final EquivalenceClass a,
			final HashMap<LETTER, HashMap<STATE, HashSet<EquivalenceClass>>>
			letter2lin2hierEcSet,
			final HashMap<LETTER, HashMap<STATE, HashSet<EquivalenceClass>>>
			letter2hier2linEcSet) {
		for (final STATE succ : a.m_states) {
			for (final IncomingReturnTransition<LETTER, STATE> edge :
					m_operand.returnPredecessors(succ)) {
				final LETTER letter = edge.getLetter();
				final STATE lin = edge.getLinPred();
				final STATE hier = edge.getHierPred();
				final EquivalenceClass linEc =
						m_partition.m_state2EquivalenceClass.get(lin);
				final EquivalenceClass hierEc =
						m_partition.m_state2EquivalenceClass.get(hier);
				
				HashMap<STATE, HashSet<EquivalenceClass>> lin2hierEcSet =
						letter2lin2hierEcSet.get(letter);
				if (lin2hierEcSet == null) {
					lin2hierEcSet =
							new HashMap<STATE, HashSet<EquivalenceClass>>();
					letter2lin2hierEcSet.put(letter, lin2hierEcSet);
				}
				HashSet<EquivalenceClass> hierEcSet = lin2hierEcSet.get(lin);
				if (hierEcSet == null) {
					hierEcSet = new HashSet<EquivalenceClass>();
					lin2hierEcSet.put(lin, hierEcSet);
				}
				hierEcSet.add(hierEc);
				
				HashMap<STATE, HashSet<EquivalenceClass>> hier2linEcSet =
						letter2hier2linEcSet.get(letter);
				if (hier2linEcSet == null) {
					hier2linEcSet =
							new HashMap<STATE, HashSet<EquivalenceClass>>();
					letter2hier2linEcSet.put(letter, hier2linEcSet);
				}
				HashSet<EquivalenceClass> linEcSet = hier2linEcSet.get(hier);
				if (linEcSet == null) {
					linEcSet = new HashSet<EquivalenceClass>();
					hier2linEcSet.put(hier, linEcSet);
				}
				linEcSet.add(linEc);
			}
		}
	}
	
	/**
	 * This method performs necessary linear return splits.
	 * 
	 * For a fixed hierarchical predecessor, check all linear predecessors.
	 * Distinguish these with the reached successor equivalence classes and
	 * mark them to be split later.
	 * 
	 * For the linear predecessors only look at states in equivalence classes
	 * of which at least one state indeed is a linear predecessor leading to
	 * any state. This means down states leading to a sink state without an
	 * explicit transition are of interest iff their equivalence class is
	 * considered.
	 * 
	 * TODO<duplicateCode> this method is nearly the same as splitReturnHier().
	 *                     create abstract method and call with algorithm
	 *                     pattern object for transitions and DownStates.
	 *
	 * @param letter2hier2linEcSet mapping: letter to hierarchical state to
	 *                             set of linear equivalence classes
	 * @param splitEquivalenceClasses split equivalence classes
	 */
	private void splitReturnLin(final HashMap<LETTER, HashMap<STATE,
			HashSet<EquivalenceClass>>> letter2hier2linEcSet,
			final HashSet<EquivalenceClass> splitEquivalenceClasses) {
		if (DEBUG3)
			System.err.println("\n- starting linear split: " +
					letter2hier2linEcSet);
		
		for (final Entry<LETTER, HashMap<STATE, HashSet<EquivalenceClass>>>
				outerEntry : letter2hier2linEcSet.entrySet()) {
			final LETTER letter = outerEntry.getKey();
			final HashMap<STATE, HashSet<EquivalenceClass>> hier2linEcSet =
					outerEntry.getValue();
			
			if (DEBUG3)
				System.err.println("\nouter entry: " + outerEntry);
			
			for (final Entry<STATE, HashSet<EquivalenceClass>> innerEntry :
					hier2linEcSet.entrySet()) {
				final STATE hier = innerEntry.getKey();
				final HashSet<EquivalenceClass> linEcSet =
						innerEntry.getValue();
				
				if (DEBUG3)
					System.err.println("\n consider hier: " + hier);
				
				for (final EquivalenceClass linEc : linEcSet) {
					if (DEBUG3)
						System.err.println("\nnext linEc: " +
								linEc.toStringShort());
					
					final HashMap<HashSet<EquivalenceClass>, HashSet<STATE>>
						succEc2linSet = new HashMap<HashSet<EquivalenceClass>,
						HashSet<STATE>>();
					
					for (final STATE lin : linEc.m_states) {
						if (DEBUG3)
							System.err.println("consider " + lin);
						
						final Iterator<OutgoingReturnTransition<LETTER, STATE>>
							edges = m_operand.returnSucccessors(
									lin, hier, letter).iterator();
						/*
						 * TODO<nondeterminism> at most one transition for
						 *                      deterministic automata,
						 *                      offer improved version?
						 */
						final HashSet<EquivalenceClass> succEcs;
						if (edges.hasNext()) {
							succEcs = new HashSet<EquivalenceClass>();
							do {
								final STATE succ = edges.next().getSucc();
								final EquivalenceClass succEc = m_partition.
										m_state2EquivalenceClass.get(succ);
								succEcs.add(succEc);
								
								if (DEBUG3)
									System.err.println(" reaching " + succ +
											" in " + succEc.toStringShort());
							} while (edges.hasNext());
						}
						else {
							if (DEBUG3)
								System.err.print(" no transition, ");
							
							if (m_doubleDecker.isDoubleDecker(lin, hier)) {
								if (DEBUG3)
									System.err.println("but DS");
								
								succEcs = m_negativeSet;
							}
							else {
								if (DEBUG3)
									System.err.println("no DS");
								
								continue;
							}
						}
						
						HashSet<STATE> linSet = succEc2linSet.get(succEcs);
						if (linSet == null) {
							linSet = new HashSet<STATE>(
									computeHashSetCapacity(
											linEc.m_states.size()));
							succEc2linSet.put(succEcs, linSet);
						}
						linSet.add(lin);
						
						if (DEBUG3)
							System.err.println(" -> altogether reached " +
									succEcs);
					}
					
					if (succEc2linSet.size() > 1) {
						if (DEBUG3)
							System.err.println("\n! mark split of " +
									linEc.toStringShort() + ": " +
									succEc2linSet);
						
						linEc.markSplit(succEc2linSet.values());
						splitEquivalenceClasses.add(linEc);
					}
					else {
						assert (succEc2linSet.size() == 1);
						if (DEBUG3)
							System.err.println("ignore marking: " +
									succEc2linSet);
					}
				}
			}
		}
	}
	
	/**
	 * This method performs necessary hierarchical return splits.
	 * 
	 * For a fixed linear predecessor, check all hierarchical predecessors.
	 * Distinguish these with the reached successor equivalence classes and
	 * mark them to be split later.
	 * 
	 * For the hierarchical predecessors only look at states in equivalence
	 * classes of which at least one state indeed is a hierarchical predecessor
	 * leading to any state. This means down states leading to a sink state
	 * without an explicit transition are of interest iff their equivalence
	 * class is considered.
	 *
	 * @param letter2lin2hierEcSet mapping: letter to linear state to set of
	 *                             hierarchical equivalence classes
	 * @param splitEquivalenceClasses split equivalence classes
	 */
	private void splitReturnHier(final HashMap<LETTER, HashMap<STATE,
			HashSet<EquivalenceClass>>> letter2lin2hierEcSet,
			final HashSet<EquivalenceClass> splitEquivalenceClasses) {
		if (DEBUG3)
			System.err.println("\n- starting hierarchical split: " +
					letter2lin2hierEcSet);
		
		for (final Entry<LETTER, HashMap<STATE, HashSet<EquivalenceClass>>>
				outerEntry : letter2lin2hierEcSet.entrySet()) {
			final LETTER letter = outerEntry.getKey();
			final HashMap<STATE, HashSet<EquivalenceClass>> lin2hierEcSet =
					outerEntry.getValue();
			
			if (DEBUG3)
				System.err.println("\nouter entry: " + outerEntry);
			
			for (final Entry<STATE, HashSet<EquivalenceClass>> innerEntry :
					lin2hierEcSet.entrySet()) {
				final STATE lin = innerEntry.getKey();
				final HashSet<EquivalenceClass> hierEcSet =
						innerEntry.getValue();
				
				if (DEBUG3)
					System.err.println("\n consider lin: " + lin);
				
				for (final EquivalenceClass hierEc : hierEcSet) {
					if (DEBUG3)
						System.err.println("\nnext hierEc: " +
								hierEc.toStringShort());
					
					final HashMap<HashSet<EquivalenceClass>, HashSet<STATE>>
						succEc2hierSet = new HashMap<HashSet<EquivalenceClass>,
						HashSet<STATE>>();
					
					for (final STATE hier : hierEc.m_states) {
						if (DEBUG3)
							System.err.println("consider " + hier);
						
						final Iterator<OutgoingReturnTransition<LETTER, STATE>>
							edges = m_operand.returnSucccessors(
									lin, hier, letter).iterator();
						/*
						 * TODO<nondeterminism> at most one transition for
						 *                      deterministic automata,
						 *                      offer improved version?
						 */
						final HashSet<EquivalenceClass> succEcs;
						if (edges.hasNext()) {
							succEcs = new HashSet<EquivalenceClass>();
							do {
								final STATE succ = edges.next().getSucc();
								final EquivalenceClass succEc = m_partition.
										m_state2EquivalenceClass.get(succ);
								succEcs.add(succEc);
								
								if (DEBUG3)
									System.err.println(" reaching " + succ +
											" in " + succEc.toStringShort());
							} while (edges.hasNext());
						}
						else {
							if (DEBUG3)
								System.err.print(" no transition, ");
							
							if (m_doubleDecker.isDoubleDecker(lin, hier)) {
								if (DEBUG3)
									System.err.println("but DS");
								
								succEcs = m_negativeSet;
							}
							else {
								if (DEBUG3)
									System.err.println("no DS");
								
								continue;
							}
						}
						
						HashSet<STATE> hierSet = succEc2hierSet.get(succEcs);
						if (hierSet == null) {
							hierSet = new HashSet<STATE>(
									computeHashSetCapacity(
											hierEc.m_states.size()));
							succEc2hierSet.put(succEcs, hierSet);
						}
						hierSet.add(hier);
						
						if (DEBUG3)
							System.err.println(" -> altogether reached " +
									succEcs);
					}
					
					if (succEc2hierSet.size() > 1) {
						if (DEBUG3)
							System.err.println("\n! mark split of " +
									hierEc.toStringShort() + ": " +
									succEc2hierSet);
						
						hierEc.markSplit(succEc2hierSet.values());
						splitEquivalenceClasses.add(hierEc);
					}
					else {
						assert (succEc2hierSet.size() == 1);
						if (DEBUG3)
							System.err.println("ignore marking: " +
									succEc2hierSet);
					}
				}
			}
		}
	}
	
	/**
	 * For each pair of hierarchical and linear predecessors that is currently
	 * possible find transitions not possible in the original automaton and
	 * disable them.
	 * 
	 * TODO<mixedSplit> several options: (1) then (2)
	 * (1) linear and hierarchical splits
	 * - collect locally
	 * - execute locally
	 * - collect globally
	 * - execute globally
	 * 
	 * (2) mixed split
	 * - execute locally
	 * - collect globally
	 * 
	 * @param letter2hier2linEcSet mapping: letter to hierarchical state to
	 *                             set of linear equivalence classes
	 * @param splitEquivalenceClasses split equivalence classes
	 */
	private void splitReturnMixed(
			final HashMap<LETTER, HashMap<STATE, HashSet<EquivalenceClass>>>
			letter2hier2linEcSet,
			final HashSet<EquivalenceClass> splitEquivalenceClasses) {
		if (DEBUG3)
			System.err.println("\n- starting mixed split: " +
					letter2hier2linEcSet);
		
		for (final Entry<LETTER, HashMap<STATE, HashSet<EquivalenceClass>>>
				outerEntry : letter2hier2linEcSet.entrySet()) {
			final LETTER letter = outerEntry.getKey();
			final HashMap<STATE, HashSet<EquivalenceClass>> hier2linEcSet =
					outerEntry.getValue();
			final HashMap<EquivalenceClass, HashSet<EquivalenceClass>>
					hierEc2linEcSet =
					new HashMap<EquivalenceClass, HashSet<EquivalenceClass>>();
			
			if (DEBUG3)
				System.err.println("letter: " + letter);
			
			for (final Entry<STATE, HashSet<EquivalenceClass>> innerEntry :
					hier2linEcSet.entrySet()) {
				final EquivalenceClass hierEc =
						m_partition.m_state2EquivalenceClass.get(
								innerEntry.getKey());
				
				if (DEBUG3)
					System.err.println("checking hierEc " +
							hierEc.toStringShort());
				
				HashSet<EquivalenceClass> linEcSet =
						hierEc2linEcSet.get(hierEc);
				if (linEcSet == null) {
					linEcSet = new HashSet<EquivalenceClass>();
					hierEc2linEcSet.put(hierEc, linEcSet);
				}
				
				for (final EquivalenceClass linEc : innerEntry.getValue()) {
					// not checked yet, check now
					if (linEcSet.add(linEc)) {
						if (DEBUG3)
							System.err.println(" with linEc " +
									linEc.toStringShort());
						splitReturnMixedCheck(letter, linEc, hierEc,
								splitEquivalenceClasses);
					}
				}
			}
		}
	}
	
	/**
	 * If a return transition is found that was not possible in the original
	 * automaton, break ties on whether to split the hierarchical or the linear
	 * predecessors.
	 * 
	 * TODO<mixedSplit> choice: split hierarchical or linear predecessors
	 *                  currently: split hierarchical predecessors
	 * 
	 * TODO<mixedSplit> cache results of other splits somehow? probably many
	 *                  duplicate checks
	 *
	 * @param letter return letter
	 * @param linEc linear equivalence class
	 * @param hierEc hierarchical equivalence class
	 * @param splitEquivalenceClasses split equivalence classes
	 */
	private void splitReturnMixedCheck(final LETTER letter,
			final EquivalenceClass linEc, final EquivalenceClass hierEc,
			final HashSet<EquivalenceClass> splitEquivalenceClasses) {
		final HashMap<HashSet<EquivalenceClass>, HashSet<STATE>> succ2hier =
				new HashMap<HashSet<EquivalenceClass>, HashSet<STATE>>(
						computeHashSetCapacity(hierEc.m_states.size()));
		
		for (final STATE hier : hierEc.m_states) {
			final HashSet<EquivalenceClass> succs =
					new HashSet<EquivalenceClass>();
			
			for (final STATE lin : linEc.m_states) {
				final Iterator<OutgoingReturnTransition<LETTER, STATE>>
				edges = m_operand.returnSucccessors(
						lin, hier, letter).iterator();
				/*
				 * TODO<nondeterminism> at most one transition for
				 *                      deterministic automata,
				 *                      offer improved version?
				 */
				if (edges.hasNext()) {
					do {
						final STATE succ = edges.next().getSucc();
						final EquivalenceClass succEc = m_partition.
								m_state2EquivalenceClass.get(succ);
						succs.add(succEc);
						
						if (DEBUG3)
							System.err.println(" reaching " + succ +
									" in " + succEc.toStringShort());
					} while (edges.hasNext());
				}
				else {
					if (DEBUG3)
						System.err.print(" no transition, ");
					
					if (m_doubleDecker.isDoubleDecker(lin, hier)) {
						if (DEBUG3)
							System.err.println("but DS");
						
						succs.add(m_negativeClass);
					}
					else {
						if (DEBUG3)
							System.err.println("no DS");
					}
				}
			}
			
			if (DEBUG3)
				System.err.println(" -> altogether reached " + succs);
			
			HashSet<STATE> hiers = succ2hier.get(succs);
			if (hiers == null) {
				hiers = new HashSet<STATE>();
				succ2hier.put(succs, hiers);
			}
			hiers.add(hier);
		}
		
		if (succ2hier.size() > 1) {
			if (DEBUG3)
				System.err.println("\n! mark split of " +
						hierEc.toStringShort() + ": " +
						succ2hier);
			
			hierEc.markSplit(succ2hier.values());
			splitEquivalenceClasses.add(hierEc);
		}
		else {
			assert (succ2hier.size() == 1);
			if (DEBUG3)
				System.err.println("ignore marking: " +
						succ2hier);
		}
	}
	
	/**
	 * This method executes the return splits for all passed equivalence
	 * classes.
	 * 
	 * There are decision points for states that can be assigned to at least
	 * two equivalence classes.
	 * 
	 * TODO<returnSplit> stop when A has been split? if so, prefer A.
	 *
	 * @param splitEquivalenceClasses split equivalence classes
	 */
	@SuppressWarnings("unchecked")
	private void splitReturnExecute(
			final HashSet<EquivalenceClass> splitEquivalenceClasses) {
		if (DEBUG3)
			System.err.println("\n-- executing return splits");
		
		for (final EquivalenceClass ec : splitEquivalenceClasses) {
			final HashMap<STATE, HashSet<STATE>> state2separatedSet =
					ec.m_state2separatedSet;
			assert (state2separatedSet != null);
			
			if (DEBUG3) {
				System.err.print(ec);
				System.err.print(" : ");
				System.err.println(state2separatedSet);
			}

			// mapping: state to associated color
			final HashMap<STATE, Integer> state2color =
					new HashMap<STATE, Integer>(
							computeHashSetCapacity(ec.m_states.size()));
			// current number of colors
			int colors = 0;
			
			/*
			 * TODO<returnSplit> this is not very efficient, rather a proof of
			 *                   concept
			 */
			final Set<STATE> states = ec.m_states;
			for (final Entry<STATE, HashSet<STATE>> entry :
					state2separatedSet.entrySet()) {
				final STATE state = entry.getKey();
				final HashSet<STATE> separatedSet = entry.getValue();
				
				assert (states.contains(state)) && (separatedSet != null);
				
				// first color can be directly assigned
				if (colors == 0) {
					state2color.put(state, 0);
					++colors;
				}
				// find fitting color or use a new one
				else {
					final HashSet<Integer> blockedColors =
							new HashSet<Integer>(
									computeHashSetCapacity(colors));
					
					for (final STATE separated : separatedSet) {
						final Integer color = state2color.get(separated);
						if (color != null) {
							blockedColors.add(color);
							if (blockedColors.size() == colors) {
								break;
							}
						}
					}
					
					// no color available, use a new one
					if (blockedColors.size() == colors) {
						state2color.put(state, colors++);
					}
					// at least one color available
					else {
						assert (blockedColors.size() < colors);
						int color = 0;
						while (true) {
							assert (color <= colors);
							if (! blockedColors.contains(color)) {
								state2color.put(state, color);
								break;
							}
							++color;
						}
					}
				}
			}
			
			// index 0 is ignored
			final HashSet<STATE>[] newEcs = new HashSet[colors];
			for (int i = colors - 1; i > 0; --i) {
				newEcs[i] = new HashSet<STATE>();
			}
			for (final Entry<STATE, Integer> entry : state2color.entrySet()) {
				final int color = entry.getValue();
				if (color > 0) {
					newEcs[color].add(entry.getKey());
				}
			}
			
			if (DEBUG3)
				System.err.println("state2color: " + state2color);
			
			// finally split the equivalence class
			for (int i = newEcs.length - 1; i > 0; --i) {
				final HashSet<STATE> newStates = newEcs[i];
				final EquivalenceClass newEc =
						m_partition.addEcHelperReturn(newStates, ec);
				
				if (STATISTICS)
					++m_splitsWithChange;
				
				if (DEBUG3)
					System.err.println("new equivalence class: " +
							newEc.toStringShort());
			}
			
			// reset separation mapping
			// TODO<resetMapping> is this necessary if no split occurred?
			ec.m_state2separatedSet = null;
			
			if (STATISTICS) {
				if (newEcs.length <= 1) {
					++m_splitsWithoutChange;
				}
			}
		}
	}
	
	/**
	 * For each remaining equivalence class create a new state.
	 * Also remove all other objects references.
	 * 
	 * @param includeMapping true iff mapping old to new state is needed
	 */
	private void constructAutomaton(final boolean includeMapping) {
		if (DEBUG)
			System.out.println("finished splitting, constructing result");
		
//		TODO<noReduction> return old automaton?!
//		if (m_operand.size() == m_partition.m_equivalenceClasses.size()) {
//			return m_operand;
//		}
		m_result = new ShrinkNwaResult(includeMapping);
		
		// clean up
		if (DEBUG) {
			System.out.println("finished construction");
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
	 * This method checks that the states in each equivalence class initially
	 * passed in the constructor are all either final or non-final.
	 *
	 * @param equivalenceClasses partition passed in constructor
	 * @return true iff equivalence classes respect final status of states
	 */
	private boolean assertStatesSeparation(
			final Iterable<Set<STATE>> equivalenceClasses) {
		for (final Set<STATE> equivalenceClass : equivalenceClasses) {
			final Iterator<STATE> it = equivalenceClass.iterator();
			assert (it.hasNext()) :
				"Empty equivalence classes should be avoided.";
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
	 * Returns a Map from states of the input automaton to states of the output
	 * automaton. The image of a state oldState is the representative of 
	 * oldStates equivalence class.
	 * This method can only be used if the minimization is finished.
	 */
	public Map<STATE,STATE> getOldState2newState() {
		return m_result.m_oldState2newState;
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
		 * This method adds an equivalence class to the partition that resulted
		 * from a return split.
		 *
		 * @param parent the parent equivalence class
		 * @param states the states
		 * @return the equivalence class
		 */
		private EquivalenceClass addEcHelperReturn(final Set<STATE> states,
				final EquivalenceClass parent) {
			final EquivalenceClass ec = new EquivalenceClass(states, parent);
			m_equivalenceClasses.add(ec);
			
			// update mapping
			for (final STATE state : states) {
				assert (parent.m_states.contains(state)) &&
					(m_state2EquivalenceClass.get(state) == parent);
				
				parent.m_states.remove(state);
				m_state2EquivalenceClass.put(state, ec);
			}
			
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
					
					// reset equivalence class
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
		// mapping: state to states that are separated
		private HashMap<STATE, HashSet<STATE>> m_state2separatedSet;
		
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
		
		/**
		 * @param parent the parent equivalence class
		 */
		public EquivalenceClass(final EquivalenceClass parent) {
			this(parent.m_intersection, parent);
		}
		
		/**
		 * This constructor is reserved for the placeholder equivalence class.
		 */
		private EquivalenceClass() {
			m_states = null;
			m_intersection = null;
		}
		
		/**
		 * This constructor is used during the return split, when an
		 * equivalence class can be split into more than two new objects.
		 * 
		 * @param states the set of states for the equivalence class
		 * @param parent the parent equivalence class
		 */
		public EquivalenceClass(final Set<STATE> states,
				final EquivalenceClass parent) {
			m_states = states;
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
		 * This method marks the pairs of splits necessary for given sets of
		 * states, but does not invoke the splits yet.
		 *
		 * @param splitSets sets of states to be marked for split
		 */
		public void markSplit(Collection<HashSet<STATE>> splitSets) {
			assert (splitSets.size() > 1) : "Splits with " + splitSets.size() +
					" set are not sensible and should be caught beforehand.";
			
			if (m_state2separatedSet == null) {
				m_state2separatedSet = new HashMap<STATE, HashSet<STATE>>(
						computeHashSetCapacity(m_states.size()));
			}
			
			final HashSet<Iterable<STATE>> visited =
					new HashSet<Iterable<STATE>>();
			
			for (final Iterable<STATE> set : splitSets) {
				for (final Iterable<STATE> oldSet : visited) {
					for (final STATE oldState : oldSet) {
						for (final STATE newState : set) {
							markPair(oldState, newState);
						}
					}
				}
				visited.add(set);
			}
		}
		
		/**
		 * This method marks a pair of states to be separated.
		 *
		 * @param state1 one state
		 * @param state2 another state
		 */
		private void markPair(final STATE state1, final STATE state2) {
			if (DEBUG3)
				System.err.println("separate " + state1 + " " + state2);
			
			assert ((state1 != state2) && (m_states.contains(state1)) &&
					 (m_states.contains(state2)));
			
			HashSet<STATE> separated = m_state2separatedSet.get(state1);
			if (separated == null) {
				separated = new HashSet<STATE>();
				m_state2separatedSet.put(state1, separated);
			}
			separated.add(state2);
			
			separated = m_state2separatedSet.get(state2);
			if (separated == null) {
				separated = new HashSet<STATE>();
				m_state2separatedSet.put(state2, separated);
			}
			separated.add(state1);
		}
		

		/**
		 * This method resets the intersection set.
		 */
		private void reset() {
			m_intersection = new HashSet<STATE>(
					computeHashSetCapacity(m_states.size()));
			m_state2separatedSet = null;
		}
		
		@Override
		public String toString() {
			if (m_states == null) {
				return "negative equivalence class";
			}
			
			if (!DEBUG && DEBUG3) {
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
		private final Map<STATE, STATE> m_oldState2newState;
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
		/**
		 * @param includeMapping true iff mapping old to new state is needed
		 */
		public ShrinkNwaResult(final boolean includeMapping) {
			if (DEBUG)
				System.out.println("\n---- constructing result...");
			m_oldNwa = m_operand;
			m_finals = new HashSet<STATE>();
			m_nonfinals = new HashSet<STATE>();
			m_initialStates = new HashSet<STATE>();
			m_oldState2newState = includeMapping
					? new HashMap<STATE, STATE>(computeHashSetCapacity(
							m_oldNwa.size()))
					: null;
			
			assert (m_stateFactory != null);
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
				final STATE newState = m_stateFactory.minimize(ecStates);
				ec2state.put(ec, newState);
				if (includeMapping) {
					for (final STATE oldState : ecStates) {
						m_oldState2newState.put(oldState, newState);
					}
				}
				
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