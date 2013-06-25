package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayList;
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
 *                   also this does not work together with the "only one to WL"
 *                   policy
 * 
 * <constructAutomaton> how to do this efficiently in the end?
 * 
 * <threading> identify possibilities for threading and implement it
 * 
 * possible improvements:
 * <globalSplit> global return split analysis
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
	// return transition helper objects
	final LinHelper m_linHelper;
	final HierHelper m_hierHelper;
	// simulates the output automaton
	private ShrinkNwaResult m_result;
	
	// states indices for equivalence classes
	private final int[] m_statesInd = {0, 1, 2, 3, 4, 5, 6, 7};
	private final int[] m_internalInd = {4, 5, 6, 7};
	private final int[] m_callInd = {2, 3, 6, 7};
	private final int[] m_returnInd = {1, 3, 5, 7};
	
	// TODO<experiments>
	// global split
	private HashSet<EquivalenceClass> m_splitEcs;
	// initial outgoing split (internal and call)
	private final boolean m_splitOutgoing;
	private final OutgoingHelperInternal m_outInternal;
	private final OutgoingHelperCall m_outCall;
	
	// TODO<debug>
	private final boolean DEBUG = false;
	private final boolean DEBUG3 = false;
	private final boolean DEBUG4 = false;
	
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
		this(operand, false);
	}
	
	/**
	 * creates a copy of operand with options
	 * 
	 * @param operand preprocessed nested word automaton
	 * preprocessing: dead end and unreachable states/transitions removed
	 * @param splitOutgoing true iff states should be split initially by
	 *        outgoing transitions
	 * @throws OperationCanceledException if cancel signal is received
	 */
	public ShrinkNwa(final INestedWordAutomaton<LETTER,STATE> operand,
			final boolean splitOutgoing)
			throws OperationCanceledException {
		this(operand, null, null, false, false, splitOutgoing);
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
	 * @param splitOutgoing true iff states should be split initially by
	 *        outgoing transitions
	 * @throws OperationCanceledException if cancel signal is received
	 */
	@SuppressWarnings("unchecked")
	public ShrinkNwa(
			final INestedWordAutomaton<LETTER,STATE> operand,
			final Collection<Set<STATE>> equivalenceClasses,
			final StateFactory<STATE> stateFactory,
			final boolean includeMapping, final boolean isFiniteAutomaton,
			final boolean splitOutgoing)
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
		m_linHelper = new LinHelper();
		m_hierHelper = new HierHelper();
		
		m_splitOutgoing = splitOutgoing;
		if (m_splitOutgoing) {
			m_outInternal = new OutgoingHelperInternal();
			m_outCall = new OutgoingHelperCall();
		}
		else {
			m_outInternal = null;
			m_outCall = null;
		}
		
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
				
				if (DEBUG4) {
					System.err.println("return split: " +
							m_partition.m_equivalenceClasses.size() + " ECs");
					System.err.println(m_partition.m_equivalenceClasses);
				}
				
				// return predecessors
				if (m_workListRet.hasNext()) {
					// TODO<globalSplit>
//					m_splitEcs = new HashSet<EquivalenceClass>();
//					do {
						
						if (DEBUG)
							System.out.println("\n-- return search");
						EquivalenceClass a = m_workListRet.next();
						
						splitReturnPredecessors(a);
						
//					} while (m_workListRet.hasNext());
//					// execute the splits
//					splitReturnExecute(m_splitEcs);
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
			
			if (m_splitOutgoing) {
				splitOutgoing(finals, nonfinals);
			}
			// only separate final and non-final states
			else {
				/*
				 * TODO<trivialCases>
				 * finals.size() = 0 => empty automaton
				 * 
				 * nonfinals.size() = 0 => possibly MR(Sigma)*, easy to check:
				 * all states must have all internal and call symbols outgoing
				 * all states must have all down states as return transitions
				 * outgoing
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
		
		if (DEBUG4) {
			System.err.println("starting with " +
					m_partition.m_equivalenceClasses.size() +
					" equivalence classes");
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
		for (final STATE state : iterator.iterable(a)) {
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
		splitReturnLocal(letter2hier2linEcSet, splitEquivalenceClasses,
				m_linHelper);
		
		// collect trivial hierarchical splits
		splitReturnLocal(letter2lin2hierEcSet, splitEquivalenceClasses,
				m_hierHelper);
		
		// collect complicated mixed splits
		splitReturnMixed(letter2hier2linEcSet, splitEquivalenceClasses);
		
		// TODO<globalSplit> replace last line below
//		assert (m_splitEcs != null);
//		m_splitEcs.addAll(splitEquivalenceClasses);
		
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
		for (final STATE succ : a.returns()) {
			for (final IncomingReturnTransition<LETTER, STATE> edge :
					m_operand.returnPredecessors(succ)) {
				final LETTER letter = edge.getLetter();
				final STATE lin = edge.getLinPred();
				final STATE hier = edge.getHierPred();
				final EquivalenceClass linEc =
						m_partition.m_state2EquivalenceClass.get(lin).m_ec;
				final EquivalenceClass hierEc =
						m_partition.m_state2EquivalenceClass.get(hier).m_ec;
				
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
	 * This method performs necessary local return splits.
	 * 
	 * In order to abstract from linear and hierarchical states (since the
	 * split is complementary and the method is nearly the same), an algorithm
	 * pattern is used. That is why the explanation is rather unsatisfying.
	 * Let exactly one of A and B be the linear and the hierarchical states.
	 * 
	 * For a fixed A predecessor, check all B predecessors. Distinguish these
	 * with the reached successor equivalence classes and mark them to be split
	 * later.
	 * 
	 * For the A predecessors only look at states in equivalence classes
	 * of which at least one state indeed is an A predecessor leading to
	 * any state. This means down states leading to a sink state without an
	 * explicit transition are of interest iff their equivalence class is
	 * considered.
	 *
	 * @param letter2state2ecSet mapping: letter to state to set of equivalence
	 *                           classes
	 * @param splitEquivalenceClasses split equivalence classes
	 * @param returnHelper abstract from linear and hierarchical states
	 */
	private void splitReturnLocal(final HashMap<LETTER, HashMap<STATE,
			HashSet<EquivalenceClass>>> letter2state2ecSet,
			final HashSet<EquivalenceClass> splitEquivalenceClasses,
			final IReturnHelper<LETTER, STATE> returnHelper) {
		if (DEBUG3)
			System.err.println("\n- starting local split: " +
					letter2state2ecSet);
		
		for (final Entry<LETTER, HashMap<STATE, HashSet<EquivalenceClass>>>
				outerEntry : letter2state2ecSet.entrySet()) {
			final LETTER letter = outerEntry.getKey();
			final HashMap<STATE, HashSet<EquivalenceClass>> state2ecSet =
					outerEntry.getValue();
			
			if (DEBUG3)
				System.err.println("\nouter entry: " + outerEntry);
			
			for (final Entry<STATE, HashSet<EquivalenceClass>> innerEntry :
					state2ecSet.entrySet()) {
				final STATE first = innerEntry.getKey();
				final HashSet<EquivalenceClass> ecSet = innerEntry.getValue();
				
				if (DEBUG3)
					System.err.println("\n consider: " + first);
				
				for (final EquivalenceClass ec : ecSet) {
					if (DEBUG3)
						System.err.println("\nnext ec: " +
								ec.toStringShort());
					
					final HashMap<HashSet<EquivalenceClass>, HashSet<STATE>>
						succEcSet2stateSet = new HashMap<
							HashSet<EquivalenceClass>, HashSet<STATE>>();
					
					for (final STATE second : ec.states()) {
						if (DEBUG3)
							System.err.println("consider " + second);
						
						final Iterator<OutgoingReturnTransition<LETTER, STATE>>
							edges = returnHelper.get(first, second, letter);
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
								final EquivalenceClass succEc =
										m_partition.m_state2EquivalenceClass.
										get(succ).m_ec;
								succEcs.add(succEc);
								
								if (DEBUG3)
									System.err.println(" reaching " + succ +
											" in " + succEc.toStringShort());
							} while (edges.hasNext());
						}
						else {
							if (DEBUG3)
								System.err.print(" no transition, ");
							
							if (returnHelper.isDoubleDecker(first, second)) {
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
						
						HashSet<STATE> linSet =
								succEcSet2stateSet.get(succEcs);
						if (linSet == null) {
							linSet = new HashSet<STATE>(
									computeHashSetCapacity(
											ec.m_size));
							succEcSet2stateSet.put(succEcs, linSet);
						}
						linSet.add(second);
						
						if (DEBUG3)
							System.err.println(" -> altogether reached " +
									succEcs);
					}
					
					if (succEcSet2stateSet.size() > 1) {
						if (DEBUG3)
							System.err.println("\n! mark split of " +
									ec.toStringShort() + ": " +
									succEcSet2stateSet);
						
						ec.markSplit(succEcSet2stateSet.values());
						splitEquivalenceClasses.add(ec);
					}
					else {
						assert (succEcSet2stateSet.size() == 1);
						if (DEBUG3)
							System.err.println("ignore marking: " +
									succEcSet2stateSet);
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
								innerEntry.getKey()).m_ec;
				
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
	 * automaton, split the hierarchical predecessors.
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
						computeHashSetCapacity(hierEc.m_size));
		
		for (final STATE hier : hierEc.states()) {
			final HashSet<EquivalenceClass> succs =
					new HashSet<EquivalenceClass>();
			
			for (final STATE lin : linEc.states()) {
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
								m_state2EquivalenceClass.get(succ).m_ec;
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
							computeHashSetCapacity(ec.m_size));
			// current number of colors
			int colors = 0;
			
			/*
			 * TODO<returnSplit> this is not very efficient, rather a proof of
			 *                   concept
			 */
			for (final Entry<STATE, HashSet<STATE>> entry :
					state2separatedSet.entrySet()) {
				final STATE state = entry.getKey();
				final HashSet<STATE> separatedSet = entry.getValue();
				
				assert (separatedSet != null);
				
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
	 * This class is used for the map in the partition object. For a state both
	 * the equivalence class and the index are available.
	 */
	private class EquivalenceClassIndexTuple {
		// equivalence class
		private final EquivalenceClass m_ec;
		// incoming transitions index
		private final int m_index;
		
		/**
		 * @param ec the equivalence class
		 * @param index the index
		 */
		public EquivalenceClassIndexTuple(final EquivalenceClass ec,
				final int index) {
			m_ec = ec;
			m_index = index;
		}
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
		 * This method fetches the right iterable. 
		 * 
		 * @param ec the equivalence class
		 * @return the iterable of the equivalence class
		 */
		Iterable<STATE> iterable(
				final ShrinkNwa<LETTER, STATE>.EquivalenceClass ec);
		
		/**
		 * A new successor state is considered.
		 *
		 * @param state the successor state
		 * @return the next predecessor
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
		public Iterable<STATE> iterable(
				final ShrinkNwa<LETTER, STATE>.EquivalenceClass ec) {
			return ec.internals();
		}
		
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
		public Iterable<STATE> iterable(
				final ShrinkNwa<LETTER, STATE>.EquivalenceClass ec) {
			return ec.calls();
		}
		
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
	 * This interface is used as algorithm pattern for the local return split.
	 */
	interface IReturnHelper<LETTER, STATE> {
		/**
		 * This method gives all outgoing return transitions with respect to
		 * states and letters.
		 *
		 * @param first the first state
		 * @param second the second state
		 * @param letter the letter
		 * @return all respective outgoing return transitions
		 */
		Iterator<OutgoingReturnTransition<LETTER, STATE>> get(
				final STATE first, final STATE second, final LETTER letter);
		
		/**
		 * This method determines whether one state is the down state of
		 * another state.
		 *
		 * @param first the first state
		 * @param second the second state
		 * @return true iff the one state is a down state of the other one
		 */
		boolean isDoubleDecker(final STATE first, final STATE second);
	}
	
	/**
	 * This is the implementation for the local linear return split.
	 */
	private class LinHelper implements IReturnHelper<LETTER, STATE> {
		@Override
		public Iterator<OutgoingReturnTransition<LETTER, STATE>> get(
				final STATE hier, final STATE lin, final LETTER letter) {
			return m_operand.returnSucccessors(lin, hier, letter).iterator();
		}
		
		@Override
		public boolean isDoubleDecker(final STATE hier, final STATE lin) {
			return m_doubleDecker.isDoubleDecker(lin, hier);
		}
	}
	
	/**
	 * This is the implementation for the local hierarchical return split.
	 */
	private class HierHelper implements IReturnHelper<LETTER, STATE> {
		@Override
		public Iterator<OutgoingReturnTransition<LETTER, STATE>> get(
				final STATE lin, final STATE hier, final LETTER letter) {
			return m_operand.returnSucccessors(lin, hier, letter).iterator();
		}
		
		@Override
		public boolean isDoubleDecker(final STATE lin, final STATE hier) {
			return m_doubleDecker.isDoubleDecker(lin, hier);
		}
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
	
	/**
	 * This interface is used for an alternative internal and call split to
	 * abstract from whether internal or call symbols are considered.
	 */
	private interface IInternalCallHelper<LETTER, STATE> {
		/**
		 * This method returns all incoming letters for a states
		 *
		 * @param state the successor state
		 * @return all incoming letters
		 */
		Collection<LETTER> getLetter(final STATE state);
		
		/**
		 * This method returns an iterator of all predecessor states.
		 *
		 * @param succ the successor state
		 * @param letter the letter
		 * @return iterator of all predecessor states
		 */
		Iterator<STATE> getPred(final STATE succ, final LETTER letter);
	}
	
	/**
	 * This is the implementation for the alternative internal split helper.
	 */
	private class InternalHelper implements IInternalCallHelper<LETTER, STATE>
			{
		@Override
		public Collection<LETTER> getLetter(STATE state) {
			return m_operand.lettersInternalIncoming(state);
		}
		
		@Override
		public Iterator<STATE> getPred(final STATE succ, final LETTER letter) {
			return new Iterator<STATE>() {
				final Iterator<IncomingInternalTransition<LETTER, STATE>> it =
						m_operand.internalPredecessors(letter, succ).
						iterator();
				
				@Override
				public boolean hasNext() {
					return it.hasNext();
				}

				@Override
				public STATE next() {
					return it.next().getPred();
				}

				@Override
				public void remove() {
					throw new UnsupportedOperationException(
							"Removing is not allowed.");
				}
			};
		}
	}
	
	/**
	 * This is the implementation for the alternative call split helper.
	 */
	private class CallHelper implements IInternalCallHelper<LETTER, STATE> {
		@Override
		public Collection<LETTER> getLetter(STATE state) {
			return m_operand.lettersCallIncoming(state);
		}
		
		@Override
		public Iterator<STATE> getPred(final STATE succ, final LETTER letter) {
			return new Iterator<STATE>() {
				final Iterator<IncomingCallTransition<LETTER, STATE>> it =
						m_operand.callPredecessors(letter, succ).iterator();
				
				@Override
				public boolean hasNext() {
					return it.hasNext();
				}

				@Override
				public STATE next() {
					return it.next().getPred();
				}

				@Override
				public void remove() {
					throw new UnsupportedOperationException(
							"Removing is not allowed.");
				}
			};
		}
	}
	
	/**
	 * This is an alternative internal and call split that first collects all
	 * incoming letters and then for each letter does the respective split.
	 * 
	 * Advantage:
	 * - No mapping for the transitions is needed.
	 * 
	 * Disadvantage:
	 * - It needs a further iteration for collecting the letters.
	 * - If the splitter set is split, the method must be stopped.
	 *   In practice this drastically increases runtime, since this happens
	 *   very often.
	 *   This can be avoided by making a copy of the states, which can be much
	 *   overhead, though.
	 * 
	 * Practice results: This split behaves much worse than the other one.
	 * Even the resulting size differs, which I do not understand, but I do not
	 * want to investigate this any further.
	 *
	 * @param a the splitter equivalence class
	 * @param iterator the iterator abstracting from the letter type
	 * @param isInternal true iff split is internal
	 * @param helper the helper abstracting from the letter type
	 */
	private void splitInternalOrCallNoMap(final EquivalenceClass a,
			final ITransitionIterator<LETTER, STATE> iterator,
			final boolean isInternal,
			final IInternalCallHelper<LETTER, STATE> helper) {
		assert ((isInternal &&
				(iterator instanceof ShrinkNwa.InternalTransitionIterator) &&
				(a.m_incomingInt != EIncomingStatus.inWL)) ||
				(! isInternal) &&
				((iterator instanceof ShrinkNwa.CallTransitionIterator) &&
				(a.m_incomingCall != EIncomingStatus.inWL)));
		
		// copy splitter set for not having to stop when split
		final ArrayList<STATE> aStates =
				new ArrayList<STATE>(a.m_size);
		for (final STATE state : a.states()) {
			aStates.add(state);
		}
		
		// create a hash set for visited letters
		final HashSet<LETTER> letters = new HashSet<LETTER>();
		for (final STATE state : aStates) {
			letters.addAll(helper.getLetter(state));
		}
		
		// split states
//		final int size = a.m_size;
		for (final LETTER  letter : letters) {
			final HashSet<STATE> states = new HashSet<STATE>();
			for (final STATE succ : aStates) {
				final Iterator<STATE> preds = helper.getPred(succ, letter);
				while (preds.hasNext()) {
					states.add(preds.next());
				}
				
				if (states.size() > 0) {
					m_partition.splitEquivalenceClasses(states);
//					if (a.m_size < size) {
//						return;
//					}
				}
			}
		}
	}
	
	/**
	 * This interface is used for the outgoing split at the beginning to
	 * abstract from whether internal or call symbols are considered.
	 */
	private interface IOutgoingHelper<LETTER, STATE> {
		/**
		 * This method returns the size of the respective alphabet.
		 *
		 * @return size of the alphabet
		 */
		int size();
		
		/**
		 * This method returns a set of outgoing letters for a given state.
		 * 
		 * @param state state to consider
		 * @return all outgoing letters
		 */
		Set<LETTER> letters(final STATE state);
		
		/**
		 * This method returns a new collection. This is for efficiency reasons,
		 * since first only a list is needed, where later a set is needed.
		 *
		 * @return
		 */
		Collection<STATE> newCollection();
		
		/**
		 * This method only checks that the symbols are correctly returned by
		 * the API.
		 *
		 * @param state state to consider
		 * @return true iff symbols are correct
		 */
		boolean assertLetters(final STATE state);
	}
	
	/**
	 * This is the implementation for the outgoing internal split helper.
	 */
	private class OutgoingHelperInternal implements
			IOutgoingHelper<LETTER, STATE> {
		@Override
		public int size() {
			return m_operand.getInternalAlphabet().size();
		}
		
		@Override
		public Set<LETTER> letters(STATE state) {
			assert (assertLetters(state));
			
			return m_operand.lettersInternal(state);
		}

		@Override
		public Collection<STATE> newCollection() {
			return new HashSet<STATE>();
		}
		
		@Override
		public boolean assertLetters(STATE state) {
			final Collection<LETTER> model =
					m_operand.lettersInternal(state);
			
			final HashSet<LETTER> checker = new HashSet<LETTER>(
					computeHashSetCapacity(model.size()));
			final Iterator<OutgoingInternalTransition<LETTER, STATE>> it =
					m_operand.internalSuccessors(state).iterator();
			while (it.hasNext()) {
				checker.add(it.next().getLetter());
			}
			
			if (checker.size() != model.size()) {
				return false;
			}
			for (final LETTER letter : model) {
				if (! checker.contains(letter)) {
					return false;
				}
			}
			
			return true;
		}
	}
	
	/**
	 * This is the implementation for the alternative call split helper.
	 */
	private class OutgoingHelperCall implements
			IOutgoingHelper<LETTER, STATE> {
		@Override
		public int size() {
			return m_operand.getCallAlphabet().size();
		}
		
		@Override
		public Set<LETTER> letters(STATE state) {
			assert assertLetters(state);
			
			return m_operand.lettersCall(state);
		}
		
		@Override
		public Collection<STATE> newCollection() {
			return new LinkedList<STATE>();
		}
		
		@Override
		public boolean assertLetters(STATE state) {
			final Collection<LETTER> model =
					m_operand.lettersCall(state);
			
			final HashSet<LETTER> checker = new HashSet<LETTER>(
					computeHashSetCapacity(model.size()));
			final Iterator<OutgoingCallTransition<LETTER, STATE>> it =
					m_operand.callSuccessors(state).iterator();
			while (it.hasNext()) {
				checker.add(it.next().getLetter());
			}
			
			if (checker.size() != model.size()) {
				return false;
			}
			for (final LETTER letter : model) {
				if (! checker.contains(letter)) {
					return false;
				}
			}
			
			return true;
		}
	}
	
	/**
	 * This method does an extra split with outgoing transitions for internal
	 * and call symbols at the beginning. This is totally fine, since these
	 * splits would occur later anyway.
	 * The reason for this split overhead is that the regular splitting starts
	 * with smaller equivalence classes where less states and transitions have
	 * to be considered.
	 *
	 * @param finals the final states
	 * @param nonfinals the non-final states
	 */
	private void splitOutgoing(final HashSet<STATE> finals,
			final HashSet<STATE> nonfinals) {
		HashSet<STATE> states = finals;
		
		for (int i = 0; i < 2; ++i) {
			if (states.size() == 0) {
				continue;
			}
			
			final HashMap<Collection<LETTER>, Collection<STATE>> callSplit =
					splitOutgoingHelper(states, m_outCall);
			for (final Collection<STATE> callStates : callSplit.values()) {
				final HashMap<Collection<LETTER>, Collection<STATE>>
				internalSplit = splitOutgoingHelper(callStates, m_outInternal);
				
				// split states
				for (final Collection<STATE> newStates :
						internalSplit.values()) {
					assert (newStates.size() > 0) &&
							(newStates instanceof HashSet<?>);
					m_partition.addEc((HashSet<STATE>)newStates);
				}
			}
			
			states = nonfinals;
		}
	}
	
	/**
	 * This is a helper method that sets up data structures for splits by
	 * outgoing transitions. 
	 *
	 * @param states collection of states
	 * @param helper helper object to abstract from internal and call symbols
	 * @return map from collection of letters to states with such symbols
	 */
	private HashMap<Collection<LETTER>, Collection<STATE>> splitOutgoingHelper(
			final Collection<STATE> states,
			final IOutgoingHelper<LETTER, STATE> helper) {
		final HashMap<Collection<LETTER>, Collection<STATE>>
			letterSet2stateSet = new HashMap<Collection<LETTER>,
			Collection<STATE>>(computeHashSetCapacity(helper.size()));
		
		// set up mapping letters to states
		for (final STATE state : states) {
			final Set<LETTER> letters = helper.letters(state);
			Collection<STATE> statesSet = letterSet2stateSet.get(letters);
			if (statesSet == null) {
				statesSet = helper.newCollection();
				letterSet2stateSet.put(letters, statesSet);
			}
			statesSet.add(state);
		}
		
		return letterSet2stateSet;
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
		private final HashMap<STATE, EquivalenceClassIndexTuple>
			m_state2EquivalenceClass;
		// storage for split equivalence classes
		private List<EquivalenceClass> m_splitEquivalenceClasses;
		
		public Partition() {
			m_equivalenceClasses = new LinkedList<EquivalenceClass>();
			m_state2EquivalenceClass =
					new HashMap<STATE, EquivalenceClassIndexTuple>(
					computeHashSetCapacity(m_operand.size()));
			m_splitEquivalenceClasses = new LinkedList<EquivalenceClass>();
		}
		
		/**
		 * This method adds a new equivalence class to the partition.
		 *
		 * @param module the states in the equivalence class
		 * @return the equivalence class
		 */
		private void addEc(final Set<STATE> module) {
			final EquivalenceClass ec = new EquivalenceClass(module,
					m_state2EquivalenceClass);
			m_equivalenceClasses.add(ec);
		}
		
		/**
		 * This method adds an equivalence class to the partition that resulted
		 * from a split.
		 *
		 * @param parent the parent equivalence class
		 * @return the equivalence class
		 */
		private EquivalenceClass addEcHelper(final EquivalenceClass parent) {
			final EquivalenceClass ec =
					new EquivalenceClass(parent, m_state2EquivalenceClass);
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
			final EquivalenceClass ec = new EquivalenceClass(states,
					m_state2EquivalenceClass);
			m_equivalenceClasses.add(ec);
			
			// remove states from old equivalence class
			for (final STATE state : states) {
				final EquivalenceClassIndexTuple ecTuple =
						m_state2EquivalenceClass.get(state);
				final int index = ecTuple.m_index;
				parent.m_sets.get(index).remove(state);
			}
			
			return ec;
		}
		
		/**
		 * This method splits a state from its equivalence class.
		 * The equivalence class is remembered 
		 */
		private void splitState(final STATE state) {
			final EquivalenceClassIndexTuple tuple =
					m_state2EquivalenceClass.get(state);
			final EquivalenceClass ec = tuple.m_ec;
			final int index = tuple.m_index;
			
			// first occurrence of the equivalence class, mark it
			if (! ec.m_isSplit) {
				ec.m_isSplit = true;
				m_splitEquivalenceClasses.add(ec);
			}
			
			// move state to intersection set
			ec.m_intersections.get(index).add(state);
			
			// remove state from old set
			ec.m_sets.get(index).remove(state);
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
				if (ec.m_incomingN.isEmpty() && ec.m_incomingI.isEmpty() &&
						ec.m_incomingC.isEmpty() && ec.m_incomingR.isEmpty() &&
						ec.m_incomingIC.isEmpty() && ec.m_incomingIR.isEmpty() &&
						ec.m_incomingCR.isEmpty() && ec.m_incomingICR.isEmpty()) {
					ec.m_incomingN = ec.m_intersectionN;
					ec.m_incomingI = ec.m_intersectionI;
					ec.m_incomingC = ec.m_intersectionC;
					ec.m_incomingR = ec.m_intersectionR;
					ec.m_incomingIC = ec.m_intersectionIC;
					ec.m_incomingIR = ec.m_intersectionIR;
					ec.m_incomingCR = ec.m_intersectionCR;
					ec.m_incomingICR = ec.m_intersectionICR;
					ec.resetIncoming();
					if (DEBUG)
						System.out.println("EC was skipped " + ec);
					++m_splitsWithoutChange;
				}
				// do a split
				else {
					if (DEBUG)
						System.out.println("EC was split " + ec);
					++m_splitsWithChange;
					
					splitOccurred = true;
					addEcHelper(ec);
					
					if (DEBUG)
						System.out.println("old EC: " + ec);
					
					/*
					 * put old ec in work lists if not already in there
					 * TODO<onlyOneWL> not necessary!
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
					*/
				}
				
				// reset equivalence class
				ec.reset();
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
		private final ArrayList<Set<STATE>> m_sets;
		private Set<STATE> m_incomingN, m_incomingI, m_incomingC, m_incomingR,
			m_incomingIC, m_incomingIR, m_incomingCR, m_incomingICR;
		private ArrayList<EquivalenceClassIndexTuple> m_tuples;
		// size
		private int m_size;
		// intersection set that finally becomes a new equivalence class
		private final ArrayList<Set<STATE>> m_intersections;
		private Set<STATE> m_intersectionN, m_intersectionI, m_intersectionC,
			m_intersectionR, m_intersectionIC, m_intersectionIR,
			m_intersectionCR, m_intersectionICR;
		private boolean m_isSplit;
		// status regarding incoming transitions
		private EIncomingStatus m_incomingInt, m_incomingCall, m_incomingRet;
		// mapping: state to states that are separated
		private HashMap<STATE, HashSet<STATE>> m_state2separatedSet;
		
		/**
		 * This constructor is used for the initialization.
		 * 
		 * @param states the set of states for the equivalence class
		 */
		public EquivalenceClass(final Set<STATE> states,
				final HashMap<STATE, EquivalenceClassIndexTuple> states2ec) {
			m_size = states.size();
			final int size = computeHashSetCapacity(m_size);
			m_incomingN = new HashSet<STATE>(size);
			m_incomingI = new HashSet<STATE>(size);
			m_incomingC = new HashSet<STATE>(size);
			m_incomingR = new HashSet<STATE>(size);
			m_incomingIC = new HashSet<STATE>(size);
			m_incomingIR = new HashSet<STATE>(size);
			m_incomingCR = new HashSet<STATE>(size);
			m_incomingICR = new HashSet<STATE>(size);
			m_sets = new ArrayList<Set<STATE>>(8);
			resetIncoming();
			m_tuples = new ArrayList<EquivalenceClassIndexTuple>(8);
			for (int i = 0; i < 8; ++i) {
				m_tuples.add(i, new EquivalenceClassIndexTuple(this, i));
			}
			for (final STATE state : states) {
				int index = 0;
				if (m_operand.internalPredecessors(state).iterator().
						hasNext()) {
					index += 4;
				}
				if (m_operand.callPredecessors(state).iterator().hasNext()) {
					index += 2;
				}
				if (m_operand.returnPredecessors(state).iterator().hasNext()) {
					index += 1;
				}
				m_sets.get(index).add(state);
				states2ec.put(state, m_tuples.get(index));
			}
			m_intersections = new ArrayList<Set<STATE>>(8);
			reset();
			m_incomingInt = EIncomingStatus.inWL;
			m_incomingCall = EIncomingStatus.inWL;
			m_workListIntCall.add(this);
			m_incomingRet = EIncomingStatus.inWL;
			m_workListRet.add(this);
		}
		
		/**
		 * This constructor is used during the internal and call split.
		 * 
		 * @param parent the parent equivalence class
		 */
		public EquivalenceClass(final EquivalenceClass parent,
				final HashMap<STATE, EquivalenceClassIndexTuple> states2ec) {
			m_incomingN = parent.m_intersectionN;
			m_incomingI = parent.m_intersectionI;
			m_incomingC = parent.m_intersectionC;
			m_incomingR = parent.m_intersectionR;
			m_incomingIC = parent.m_intersectionIC;
			m_incomingIR = parent.m_intersectionIR;
			m_incomingCR = parent.m_intersectionCR;
			m_incomingICR = parent.m_intersectionICR;
			parent.resetIntersections();
			m_sets = new ArrayList<Set<STATE>>(8);
			m_sets.add(0, m_incomingN);
			m_sets.add(1, m_incomingR);
			m_sets.add(2, m_incomingC);
			m_sets.add(3, m_incomingCR);
			m_sets.add(4, m_incomingI);
			m_sets.add(5, m_incomingIR);
			m_sets.add(6, m_incomingIC);
			m_sets.add(7, m_incomingICR);
			m_tuples = new ArrayList<EquivalenceClassIndexTuple>(8);
			for (int i = 0; i < 8; ++i) {
				m_tuples.add(i, (m_sets.get(i).size() > 0)
							? new EquivalenceClassIndexTuple(this, i)
							: null);
			}
			for (int i = 0; i < 8; ++i) {
				final Set<STATE> set = m_sets.get(i);
				final EquivalenceClassIndexTuple tuple =
						new EquivalenceClassIndexTuple(this, i);
				for (final STATE state : set) {
					states2ec.put(state, tuple);
				}
			}
			m_intersections = new ArrayList<Set<STATE>>(8);
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
			m_sets = null;
			m_intersections = null;
		}
		
		/**
		 * This method returns an iterator of all states.
		 * 
		 * @return iterator of all states
		 */
		private Iterable<STATE> states() {
			return new Iterable<STATE>() {
				public Iterator<STATE> iterator() {
					return statesIterator(m_statesInd);
				}
			};
		}
		
		/**
		 * This method returns an iterator of all internal states.
		 * 
		 * @return iterator of all internal states
		 */
		private Iterable<STATE> internals() {
			return new Iterable<STATE>() {
				public Iterator<STATE> iterator() {
					return statesIterator(m_internalInd);
				}
			};
		}
		
		/**
		 * This method returns an iterator of all call states.
		 * 
		 * @return iterator of all call states
		 */
		private Iterable<STATE> calls() {
			return new Iterable<STATE>() {
				public Iterator<STATE> iterator() {
					return statesIterator(m_callInd);
				}
			};
		}
		
		/**
		 * This method returns an iterator of all return states.
		 * 
		 * @return iterator of all return states
		 */
		private Iterable<STATE> returns() {
			return new Iterable<STATE>() {
				public Iterator<STATE> iterator() {
					return statesIterator(m_returnInd);
				}
			};
		}
		
		/**
		 * This iterator abstracts from the positive sets passed as argument.
		 * 
		 * @param indices the indices of the positive sets
		 * @return an iterator of all respective states
		 */
		private Iterator<STATE> statesIterator(final int[] indices) {
			return new Iterator<STATE>() {
				// positive indices
				private final int[] m_indices = indices;
				// current index
				private int m_index = -1;
				// iterator of the current set
				private Iterator<STATE> m_it = init();
				
				private Iterator<STATE> init() {
					Iterator<STATE> it = m_sets.get(m_indices[0]).iterator();
					do {
						if (++m_index == m_indices.length) {
							return it;
						}
						it = m_sets.get(m_indices[m_index]).iterator();
					} while (! it.hasNext());
					return it;
				}
				
				@Override
				public boolean hasNext() {
					if (m_it.hasNext()) {
						return true;
					}
					
					while (++m_index < m_indices.length) {
						m_it = m_sets.get(m_indices[m_index]).iterator();
						if (m_it.hasNext()) {
							return true;
						}
					}
					
					return false;
				}
				
				@Override
				public STATE next() {
					try {
					return m_it.next();
					} catch (Exception e) {
						System.err.println("");
					}
					return null;
				}
				
				@Override
				public void remove() {
					throw new UnsupportedOperationException(
							"Removing is not allowed.");
				}
			};
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
						computeHashSetCapacity(m_size));
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
			
			assert (state1 != state2);
			
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
		private void resetIntersections() {
			m_intersectionN = new HashSet<STATE>(
					computeHashSetCapacity(m_incomingN.size()));
			m_intersectionI = new HashSet<STATE>(
					computeHashSetCapacity(m_incomingI.size()));
			m_intersectionC = new HashSet<STATE>(
					computeHashSetCapacity(m_incomingC.size()));
			m_intersectionR = new HashSet<STATE>(
					computeHashSetCapacity(m_incomingR.size()));
			m_intersectionIC = new HashSet<STATE>(
					computeHashSetCapacity(m_incomingIC.size()));
			m_intersectionIR = new HashSet<STATE>(
					computeHashSetCapacity(m_incomingIR.size()));
			m_intersectionCR = new HashSet<STATE>(
					computeHashSetCapacity(m_incomingCR.size()));
			m_intersectionICR = new HashSet<STATE>(
					computeHashSetCapacity(m_incomingICR.size()));
			m_intersections.clear();
			m_intersections.add(0, m_intersectionN);
			m_intersections.add(1, m_intersectionR);
			m_intersections.add(2, m_intersectionC);
			m_intersections.add(3, m_intersectionCR);
			m_intersections.add(4, m_intersectionI);
			m_intersections.add(5, m_intersectionIR);
			m_intersections.add(6, m_intersectionIC);
			m_intersections.add(7, m_intersectionICR);
		}
		
		private void resetIncoming() {
			m_sets.clear();
			m_sets.add(0, m_incomingN);
			m_sets.add(1, m_incomingR);
			m_sets.add(2, m_incomingC);
			m_sets.add(3, m_incomingCR);
			m_sets.add(4, m_incomingI);
			m_sets.add(5, m_incomingIR);
			m_sets.add(6, m_incomingIC);
			m_sets.add(7, m_incomingICR);
		}
		
		/**
		 * This method resets the intersection set and some other things.
		 */
		private void reset() {
			resetIntersections();
			m_state2separatedSet = null;
			m_isSplit = false;
		}
		
		@Override
		public String toString() {
			if (m_sets == null) {
				return "negative equivalence class";
			}
			
			if (!DEBUG && DEBUG3) {
				return toStringShort();
			}
			
			final StringBuilder builder = new StringBuilder();
			builder.append("<[");
			builder.append(m_incomingInt);
			builder.append(",");
			builder.append(m_incomingCall);
			builder.append(",");
			builder.append(m_incomingRet);
			builder.append("], [");
			for (int i = 0; i < 8; ++i) {
				String append = "";
				
				for (final Object state : m_sets.get(i)) {
					builder.append(append);
					append = ", ";
					builder.append(state);
				}
				builder.append("|");
			}
			builder.append("], [");
			for (int i = 0; i < 8; ++i) {
				String append = "";
				
				for (final Object state : m_intersections.get(i)) {
					builder.append(append);
					append = ", ";
					builder.append(state);
				}
				builder.append("|");
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
			if (m_sets == null) {
				return "negative equivalence class";
			}
			
			final StringBuilder builder = new StringBuilder();
			
			builder.append("<");
			for (int i = 0; i < 8; ++i) {
				String append = "";
				for (final Object state : m_sets.get(i)) {
					builder.append(append);
					append = ", ";
					builder.append(state);
				}
				builder.append("|");
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
							return ec1.m_size - ec2.m_size;
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
				initials.add(m_partition.m_state2EquivalenceClass.get(init).
						m_ec);
			}
			
			m_outInt = new HashMap<STATE,
					HashSet<OutgoingInternalTransition<LETTER, STATE>>>();
			m_outCall = new HashMap<STATE,
					HashSet<OutgoingCallTransition<LETTER, STATE>>>();
			m_outRet = new HashMap<STATE,
					HashSet<OutgoingReturnTransition<LETTER, STATE>>>();
			
			for (final EquivalenceClass ec : m_partition.m_equivalenceClasses)
					{
				final ArrayList<STATE> ecStates = new ArrayList<STATE>(ec.m_size);
				for (final STATE state : ec.states()) {
					ecStates.add(state);
				}
				
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
				
				final STATE representative = ec.states().iterator().next();
				
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
							m_state2EquivalenceClass.get(edge.getSucc()).
							m_ec));
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
							m_state2EquivalenceClass.get(edge.getSucc()).
							m_ec));
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
				for (final STATE state : ec.states()) {
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
										edge.getHierPred()).m_ec);
						HashSet<STATE> succs = hier2succs.get(hier);
						if (succs == null) {
							succs = new HashSet<STATE>();
							hier2succs.put(hier, succs);
						}
						succs.add(ec2state.get(m_partition.
								m_state2EquivalenceClass.get(edge.getSucc()).
								m_ec));
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
		public Set<LETTER> lettersInternal(STATE state) {
			final HashSet<LETTER> result = new HashSet<LETTER>();
			for (final OutgoingInternalTransition<LETTER, STATE> edge :
					m_outInt.get(state)) {
				result.add(edge.getLetter());
			}
			return result;
		}
		@Override
		public Set<LETTER> lettersCall(STATE state) {
			final HashSet<LETTER> result = new HashSet<LETTER>();
			for (final OutgoingCallTransition<LETTER, STATE> edge :
					m_outCall.get(state)) {
				result.add(edge.getLetter());
			}
			return result;
		}
		@Override
		public Set<LETTER> lettersReturn(STATE state) {
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