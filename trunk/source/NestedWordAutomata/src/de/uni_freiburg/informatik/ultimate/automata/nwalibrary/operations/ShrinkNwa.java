package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.GregorianCalendar;
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
 * <emptyResult> finals.size() = 0 => empty automaton
 * 
 * <DoubleDecker> check this?
 * 
 * <constructAutomaton> how to do this efficiently in the end?
 * 
 * <hashCode> overwrite for EquivalenceClass?
 *            only additional memory, no runtime improvement
 * 
 * possible improvements:
 * <threading> identify possibilities for threading and implement it
 * 
 * misc:
 * <statistics>/<debug>/<old> remove in the end
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
	// IDs for equivalence classes
	private int m_ids;
	// work lists
	private WorkListIntCall m_workListIntCall;
	private WorkListRet m_workListRet;
	private WorkListRetHier m_workListRetHier;
	// placeholder equivalence class
	private final HashSet<EquivalenceClass> m_negativeSet;
	private final EquivalenceClass m_negativeClass;
	private final Matrix m_singletonMatrix;
	private final DummyMap m_downStateMap;
	// storage for split equivalence classes
	private List<EquivalenceClass> m_splitEcsReturn;
	// initial outgoing split (internal and call)
	private final boolean m_splitOutgoing;
	private final OutgoingHelperInternal m_outInternal;
	private final OutgoingHelperCall m_outCall;
	// simulates the output automaton
	private ShrinkNwaResult m_result;
	
	/* optional random splits before the return split to keep matrices small */
	// true iff before the first return split some random splits are executed
	private boolean m_randomReturnSplit;
	// maximum size of equivalence classes with outgoing calls/returns
	private int g_threshold;
	
	// TODO<preprocess> currently not reasonable (too expensive, worse result)
	// true iff first return split is not finished yet
	private boolean m_firstReturnSplit;
	// map for first return split (open check)
	private HashMap<EquivalenceClass, HashSet<STATE>> m_firstReturnLin2hiers;
	
	// temporarily activate alternative return split before the first run
	private boolean m_firstReturnSplitAlternative;
	// also do the hierarchical split without a matrix
	private boolean m_firstReturnSplitHierAlternative;
	
	/* split all call predecessors to avoid one dimension in the matrix */
	private boolean m_splitAllCallPreds;
	
	/* naive return split (needs another split for correctness) */
	private boolean m_returnSplitNaive;
	private HashSet<EquivalenceClass> m_returnSplitCorrectnessEcs;
	
	// TODO<debug>
	private final boolean DEBUG = false; // general output
	private final boolean DEBUG2 = false; // general return split
	private final boolean DEBUG3 = false; // first return split
	private final boolean DEBUG4 = false; // naive return split
	
	// TODO<statistics>
	private final boolean STATISTICS = false;
	private int m_splitsWithChange = 0;
	private int m_splitsWithoutChange = 0;
	private int m_incomingTransitions = 0;
	private int m_noIncomingTransitions = 0;
	private int m_ignoredReturnSingletons1x1 = 0;
	private long m_returnTime = 0, m_matrixTime = 0, m_wholeTime = 0;
	private long m_returnSeparateTime = 0;
	private long m_returnFirstTime = 0;
	private long m_returnFirstTimeAlternative = 0;
	private long m_returnFirstTimeHierAlternative = 0;
	 // size information before return splits
	private final boolean STAT_RETURN_SIZE = false;
	private final BufferedWriter m_writer1, m_writer2;
	
	/**
	 * StateFactory used for the construction of new states. This is _NOT_ the
	 * state factory relayed to the new automaton.
	 * Necessary because the Automizer needs a special StateFactory during
	 * abstraction refinement (for computation of HoareAnnotation).
	 */
	private final StateFactory<STATE> m_stateFactory;
	
	/**
	 * This constructor creates a copy of the operand.
	 * 
	 * @param operand preprocessed nested word automaton
	 * preprocessing: dead end and unreachable states/transitions removed
	 * @throws OperationCanceledException if cancel signal is received
	 */
	public ShrinkNwa(final INestedWordAutomaton<LETTER,STATE> operand)
			throws OperationCanceledException {
		this(operand, false, 0, false, 0, false, false);
	}
	
	/**
	 * This constructor creates a copy of the operand with additional options.
	 * 
	 * @param operand preprocessed nested word automaton
	 * preprocessing: dead end and unreachable states/transitions removed
	 * @param splitOutgoing true iff states should be split initially by
	 *        outgoing transitions
	 * @param splitRandomSize size of equivalence classes before first return
	 *                    split (0 for deactivation)
	 * @param firstReturnSplit true iff before first return split there shall
	 *                         be a preprocessing
	 * @param firstReturnSplitAlternative 0 == no alternative return split
	 *                                    1 == alternative return split
	 *                                    2 == alternative hierarchical split
	 * @param returnSplitNaive true iff a naive return split is used
	 * @param splitAllCallPreds true iff all call predecessors should be
	 *                          singleton
	 * @throws OperationCanceledException if cancel signal is received
	 */
	public ShrinkNwa(final INestedWordAutomaton<LETTER,STATE> operand,
			final boolean splitOutgoing, final int splitRandomSize,
			final boolean firstReturnSplit,
			final int firstReturnSplitAlternative,
			final boolean splitAllCallPreds, final boolean returnSplitNaive)
			throws OperationCanceledException {
		this(operand, null, null, false, false, splitOutgoing,
				splitRandomSize, firstReturnSplit,
				firstReturnSplitAlternative, splitAllCallPreds,
				returnSplitNaive);
	}
	
	/**
	 * This constructor creates a copy of the operand with an initial
	 * partition.
	 * 
	 * @param operand preprocessed nested word automaton
	 * preprocessing: dead end and unreachable states/transitions removed
	 * @param equivalenceClasses represent initial equivalence classes
	 * @param stateFactory used for Hoare annotation
	 * @param includeMapping true iff mapping old to new state is needed
	 * @param isFiniteAutomaton true iff automaton is a finite automaton
	 * @param splitOutgoing true iff states should be split initially by
	 *        outgoing transitions
	 * @param splitRandomSize size of equivalence classes before first return
	 *                    split (0 for deactivation)
	 * @param firstReturnSplit true iff before first return split there shall
	 *                         be a preprocessing
	 * @param firstReturnSplitAlternative 0 == no alternative return split
	 *                                    1 == alternative return split
	 *                                    2 == alternative hierarchical split
	 * @param splitAllCallPreds true iff all call predecessors should be
	 *                          singleton
	 * @param returnSplitNaive true iff a naive return split is used
	 * @throws OperationCanceledException if cancel signal is received
	 */
	@SuppressWarnings("unchecked")
	public ShrinkNwa(
			final INestedWordAutomaton<LETTER,STATE> operand,
			final Collection<Set<STATE>> equivalenceClasses,
			final StateFactory<STATE> stateFactory,
			final boolean includeMapping, final boolean isFiniteAutomaton,
			final boolean splitOutgoing, final int splitRandomSize,
			final boolean firstReturnSplit,
			final int firstReturnSplitAlternative,
			final boolean splitAllCallPreds, final boolean returnSplitNaive)
					throws OperationCanceledException {
		if (STAT_RETURN_SIZE) {
			try {
				m_writer1 = new BufferedWriter(
						new FileWriter(new File("DEBUG-1.txt")));
				m_writer2 = new BufferedWriter(
						new FileWriter(new File("DEBUG-2.txt")));
			} catch (IOException e) {
				throw new RuntimeException(e);
			}
		}
		else {
			m_writer1 = null;
			m_writer2 = null;
		}
		
		m_operand = operand;
		// TODO<DoubleDecker> check this?
		m_doubleDecker = (IDoubleDeckerAutomaton<LETTER, STATE>)m_operand;
		m_stateFactory = (stateFactory == null)
				? m_operand.getStateFactory()
				: stateFactory;
		m_partition = new Partition();
		m_ids = 0;
		m_workListIntCall = new WorkListIntCall();
		m_workListRet = new WorkListRet();
		m_splitEcsReturn = new LinkedList<EquivalenceClass>();
		m_negativeSet = new HashSet<EquivalenceClass>();
		m_negativeClass = new EquivalenceClass();
		m_negativeSet.add(m_negativeClass);
		m_singletonMatrix = new Matrix();
		m_downStateMap = new DummyMap();
		
		/* options */
		m_splitOutgoing = splitOutgoing;
		if (m_splitOutgoing) {
			m_outInternal = new OutgoingHelperInternal();
			m_outCall = new OutgoingHelperCall();
		}
		else {
			m_outInternal = null;
			m_outCall = null;
		}
		
		g_threshold = splitRandomSize;
		m_randomReturnSplit = (splitRandomSize > 0);
		
		m_firstReturnSplit = firstReturnSplit;
		m_firstReturnLin2hiers = (m_firstReturnSplit
				? new HashMap<EquivalenceClass, HashSet<STATE>>(2)
				: null);
		
		switch (firstReturnSplitAlternative) {
			case 0:
				m_firstReturnSplitAlternative = false;
				m_firstReturnSplitHierAlternative = false;
				break;
			case 1:
				m_firstReturnSplitAlternative = true;
				m_firstReturnSplitHierAlternative = false;
				break;
			case 2:
				m_firstReturnSplitAlternative = true;
				m_firstReturnSplitHierAlternative = true;
				break;
			default:
				throw new IllegalArgumentException(
						"firstReturnSplitAlternative must be one of 0, 1, 2.");
		}
		if (m_firstReturnSplitAlternative) {
			m_workListRetHier = new WorkListRetHier();
		}
		
		m_splitAllCallPreds = splitAllCallPreds;
		
		m_returnSplitNaive = returnSplitNaive;
		if (m_returnSplitNaive) {
			m_returnSplitCorrectnessEcs = new HashSet<EquivalenceClass>();
		}
		
		// must be the last part of the constructor
		s_Logger.info(startMessage());
		minimize(isFiniteAutomaton, equivalenceClasses, includeMapping);
		s_Logger.info(exitMessage());
		
		if (STATISTICS) {
			m_wholeTime += new GregorianCalendar().getTimeInMillis();
			
			System.out.println("positive splits: " + m_splitsWithChange);
			System.out.println("negative splits: " + m_splitsWithoutChange);
			System.out.println("quota (p/n): " + (m_splitsWithoutChange == 0
					? "--"
					: (((float)m_splitsWithChange) /
							((float)m_splitsWithoutChange))));
			System.out.println("incoming transition checks : " +
					m_incomingTransitions);
			System.out.println("no incoming transitions found : " +
					m_noIncomingTransitions);
			System.out.println("quota (p/n): " + (m_noIncomingTransitions == 0
					? "--"
					: (((float)m_incomingTransitions) /
							((float)m_noIncomingTransitions))));
			System.out.println("ignored return splits due to singletons: " +
					m_ignoredReturnSingletons1x1);
			System.out.println("time consumption (ms): return separation: " +
					m_returnSeparateTime + ", matrix time: " +
					m_matrixTime + ", first return split: " +
					m_returnFirstTime + ", alternative lin " +
					m_returnFirstTimeAlternative + ", alternative hier " +
					m_returnFirstTimeHierAlternative + ", returns: " +
					m_returnTime + ", all: " + m_wholeTime);
			System.out.println("quota (ret/all): " + (m_wholeTime == 0
					? "--"
					: (((float)m_returnTime) / ((float)m_wholeTime))) +
						", without: " + (m_wholeTime - m_returnTime) + " ms");
			System.out.println("quota (mat/ret): " + (m_returnTime == 0
					? "--"
					: (((float)m_matrixTime) / ((float)m_returnTime))) +
						", without: " + (m_returnTime - m_matrixTime) + " ms");
			System.out.println("quota (mat/all): " + (m_wholeTime == 0
					? "--"
					: (((float)m_matrixTime) / ((float)m_wholeTime))) +
						", without: " + (m_wholeTime - m_matrixTime) + " ms");
			System.out.println("quota (first/all): " + (m_wholeTime == 0
					? "--"
					: (((float)m_returnFirstTime) / ((float)m_wholeTime))) +
						", without: " + (m_wholeTime - m_returnFirstTime) +
						" ms");
			System.out.println("quota (altLin/all): " + (m_wholeTime == 0
					? "--"
					: (((float)m_returnFirstTimeAlternative) /
							((float)m_wholeTime))) +
						", without: " +
						(m_wholeTime - m_returnFirstTimeAlternative) + " ms");
			System.out.println("quota (altHier/all): " + (m_wholeTime == 0
					? "--"
					: (((float)m_returnFirstTimeHierAlternative) /
							((float)m_wholeTime))) +
						", without: " +
						(m_wholeTime - m_returnFirstTimeHierAlternative) +
						" ms");
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
		if (STATISTICS) {
			m_wholeTime -= new GregorianCalendar().getTimeInMillis();
		}
		
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
						if (! m_splitAllCallPreds) {
							splitInternalOrCallPredecessors(a, callIterator,
									false);
						}
					}
				}
				
				// return predecessors
				if (m_workListRet.hasNext()) {
					
					// optional random split
					if (m_randomReturnSplit) {
						m_randomReturnSplit = false;
						final LinkedList<EquivalenceClass> bigEcs =
								new LinkedList<EquivalenceClass>();
						for (final EquivalenceClass ec :
								m_partition.m_equivalenceClasses) {
							if (ec.m_states.size() > g_threshold) {
								bigEcs.add(ec);
							}
						}
						for (final EquivalenceClass ec : bigEcs) {
							splitRandom(ec);
						}
						continue outer;
					}
					
					if (STATISTICS) {
						m_returnTime -=
								new GregorianCalendar().getTimeInMillis();
					}
					
					if (STAT_RETURN_SIZE) {
						try {
							GregorianCalendar date = new GregorianCalendar();
							m_writer1.append(
									date.get(GregorianCalendar.MINUTE) + ":" +
									date.get(GregorianCalendar.SECOND) + ":" +
									date.get(GregorianCalendar.MILLISECOND) +
									" (min:sec:ms)\n");
							m_writer1.append(
									m_partition.m_equivalenceClasses.size() +
									" ECs before return split of " +
									m_workListRet.m_queue.size() + " ECs\n");
							final int[] sizes =
									new int[m_workListRet.m_queue.size()];
							m_writer2.append("\n\nnew round with " +
									sizes.length + " ECs");
							
							int i = -1;
							for (final EquivalenceClass ec :
									m_workListRet.m_queue) {
								sizes[++i] = ec.m_states.size();
							}
							Arrays.sort(sizes);
							for (i = 0; i < sizes.length; ++i) {
								if (i % 15 == 0) {
									m_writer2.append("\n");
								}
								m_writer2.append(sizes[i] + ", ");
							}
						} catch (IOException e) {
							throw new RuntimeException(e);
						}
					}
					
					// optional first linear split
					if (m_firstReturnSplit) {
						splitReturnPredecessorsFirstTime();
					}
					else {
						if (m_firstReturnSplitAlternative) {
							m_returnFirstTimeAlternative -=
									new GregorianCalendar().getTimeInMillis();
							splitReturnLinearAlt();
							m_returnFirstTimeAlternative +=
									new GregorianCalendar().getTimeInMillis();
						}
						else if (m_returnSplitNaive) {
							splitReturnNaiveHierarchicalStates(
									m_workListRet.next());
						}
						else {
							splitReturnPredecessors();
						}
					}
					
					if (STATISTICS) {
						m_returnTime +=
								new GregorianCalendar().getTimeInMillis();
					}
					
					if (STAT_RETURN_SIZE) {
						try {
							GregorianCalendar date = new GregorianCalendar();
							m_writer1.append(
									date.get(GregorianCalendar.MINUTE) + ":" +
									date.get(GregorianCalendar.SECOND) + ":" +
									date.get(GregorianCalendar.MILLISECOND) +
									" (min:sec:ms)\n");
							m_writer1.append(
									m_partition.m_equivalenceClasses.size() +
									" ECs after return split\n");
						} catch (IOException e) {
							throw new RuntimeException(e);
						}
					}
				}
				else {
					if (m_firstReturnSplitAlternative) {
						if (m_firstReturnSplitHierAlternative) {
							if (DEBUG4)
								System.err.println("hierarchical split");
							
							if (m_workListRetHier.hasNext()) {
								m_returnFirstTimeHierAlternative -=
										new GregorianCalendar().
										getTimeInMillis();
								splitReturnHierAlt();
								m_returnFirstTimeHierAlternative +=
										new GregorianCalendar().
										getTimeInMillis();
								continue outer;
							}
							else {
								break outer;
							}
						}
						else {
							if (DEBUG4)
								System.err.println("ALTERNATIVE FINISHED");
							
							m_firstReturnSplitAlternative = false;
							m_workListRet.fillWithAll();
							continue outer;
						}
					}
					else if ((m_returnSplitCorrectnessEcs != null) &&
							(! m_returnSplitCorrectnessEcs.isEmpty())) {
						final Iterator<EquivalenceClass> iterator =
								m_returnSplitCorrectnessEcs.iterator();
						assert (iterator.hasNext());
						final EquivalenceClass linEc = iterator.next();
						iterator.remove();
						splitReturnCorrectness(linEc);
						continue outer;
					}
					else {
						break outer;
					}
				}
			}
			
			if (STAT_RETURN_SIZE) {
				try {
					m_writer1.close();
					m_writer2.close();
				} catch (IOException eWriter) {
					eWriter.printStackTrace();
				}
			}
			
			s_Logger.info("Finished analysis, constructing result of size " +
					m_partition.m_equivalenceClasses.size());
			
			// automaton construction
			constructAutomaton(includeMapping);
		}
		if (DEBUG)
			System.err.println("----------------END----------------");
	}
	
	/**
	 * This method does a naive linear return split. All states that reach the
	 * splitter class with the same hierarchical state and return letter are
	 * split from the rest.
	 * Additionally, the hierarchical states are considered. This seems to be
	 * worse for the resulting size.
	 * 
	 * @param a the splitter equivalence class
	 */
	private void splitReturnNaiveHierarchicalEcs(final EquivalenceClass a) {
		// create a hash map from letter to respective predecessor states
		final HashMap<LETTER, HashMap<EquivalenceClass, HashSet<STATE>>>
				letter2hierEc2lin = new HashMap<LETTER,
				HashMap<EquivalenceClass, HashSet<STATE>>>();
		for (final STATE state : a.m_states) {
			final Iterator<IncomingReturnTransition<LETTER, STATE>> transitions
					= m_operand.returnPredecessors(state).iterator();
			while (transitions.hasNext()) {
				final IncomingReturnTransition<LETTER, STATE> transition =
						transitions.next();
				final LETTER letter = transition.getLetter();
				HashMap<EquivalenceClass, HashSet<STATE>> hierEc2lin =
						letter2hierEc2lin.get(letter);
				if (hierEc2lin == null) {
					hierEc2lin =
							new HashMap<EquivalenceClass, HashSet<STATE>>();
					letter2hierEc2lin.put(letter, hierEc2lin);
				}
				final EquivalenceClass hierEc = m_partition.
						m_state2EquivalenceClass.get(
								transition.getHierPred());
				HashSet<STATE> lins = hierEc2lin.get(hierEc);
				if (lins == null) {
					lins = new HashSet<STATE>();
					hierEc2lin.put(hierEc, lins);
				}
				lins.add(transition.getLinPred());
			}
		}
		
		// remember that this equivalence class has no incoming transitions
		if (letter2hierEc2lin.isEmpty()) {
			a.m_incomingRet = EIncomingStatus.none;
			if (STATISTICS)
				++m_noIncomingTransitions;
		}
		else {
			if (STATISTICS)
				++m_incomingTransitions;
			
			// split each map value (set of predecessor states)
			for (final HashMap<EquivalenceClass, HashSet<STATE>> hierEc2lin :
					letter2hierEc2lin.values()) {
				for (final HashSet<STATE> lins : hierEc2lin.values()) {
					assert (! lins.isEmpty());
					m_partition.splitEquivalenceClasses(lins);
				}
			}
		}
	}
	
	/**
	 * This method does a naive linear return split. All states that reach the
	 * splitter class with the same hierarchical state and return letter are
	 * split from the rest.
	 * Additionally, the hierarchical states are considered. This seems to be
	 * worse for the resulting size.
	 * 
	 * @param a the splitter equivalence class
	 */
	private void splitReturnNaiveHierarchicalStates(final EquivalenceClass a) {
		// create a hash map from letter to respective predecessor states
		final HashMap<LETTER, HashMap<STATE, HashSet<STATE>>>
				letter2hier2lin = new HashMap<LETTER,
				HashMap<STATE, HashSet<STATE>>>();
		for (final STATE state : a.m_states) {
			final Iterator<IncomingReturnTransition<LETTER, STATE>> transitions =
					m_operand.returnPredecessors(state).iterator();
			while (transitions.hasNext()) {
				final IncomingReturnTransition<LETTER, STATE> transition =
						transitions.next();
				final LETTER letter = transition.getLetter();
				HashMap<STATE, HashSet<STATE>> hier2lin =
						letter2hier2lin.get(letter);
				if (hier2lin == null) {
					hier2lin = new HashMap<STATE, HashSet<STATE>>();
					letter2hier2lin.put(letter, hier2lin);
				}
				final STATE hier = transition.getHierPred();
				HashSet<STATE> lins = hier2lin.get(hier);
				if (lins == null) {
					lins = new HashSet<STATE>();
					hier2lin.put(hier, lins);
				}
				lins.add(transition.getLinPred());
			}
		}
		
		// remember that this equivalence class has no incoming transitions
		if (letter2hier2lin.isEmpty()) {
			a.m_incomingRet = EIncomingStatus.none;
			if (STATISTICS)
				++m_noIncomingTransitions;
		}
		else {
			if (STATISTICS)
				++m_incomingTransitions;
			
			// split each map value (set of predecessor states)
			for (final HashMap<STATE, HashSet<STATE>> hier2lin :
					letter2hier2lin.values()) {
				for (final HashSet<STATE> lins : hier2lin.values()) {
					assert (! lins.isEmpty());
					m_partition.splitEquivalenceClasses(lins);
				}
			}
		}
	}
	
	/**
	 * This method does a naive linear return split. All states that reach the
	 * splitter class with the same hierarchical state and return letter are
	 * split from the rest.
	 * Hierarchical states are ignored.
	 * 
	 * @param a the splitter equivalence class
	 */
	private void splitReturnNaive(final EquivalenceClass a) {
		// create a hash map from letter to respective predecessor states
		final HashMap<LETTER, HashSet<STATE>> letter2states =
				new HashMap<LETTER, HashSet<STATE>>();
		for (final STATE state : a.m_states) {
			final Iterator<IncomingReturnTransition<LETTER, STATE>> transitions =
					m_operand.returnPredecessors(state).iterator();
			while (transitions.hasNext()) {
				final IncomingReturnTransition<LETTER, STATE> transition =
						transitions.next();
				final LETTER letter = transition.getLetter();
				HashSet<STATE> predecessorSet =
						letter2states.get(letter);
				if (predecessorSet == null) {
					predecessorSet = new HashSet<STATE>();
					letter2states.put(letter, predecessorSet);
				}
				predecessorSet.add(transition.getLinPred());
			}
		}
		
		// remember that this equivalence class has no incoming transitions
		if (letter2states.isEmpty()) {
			a.m_incomingRet = EIncomingStatus.none;
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
	 * This method assures correctness for the naive return split.
	 * 
	 * Currently it just executes the old return split, which seems to be too
	 * expensive.
	 * 
	 * @param linEc the linear equivalence class
	 */
	private void splitReturnCorrectness(final EquivalenceClass linEc) {
		if (DEBUG2)
			System.err.println("\nNEW CORRECTNESS RETURN SPLITTING");
		
		final HashMap<STATE, HashSet<STATE>> lin2hier =
				new HashMap<STATE, HashSet<STATE>>();
		for (final STATE lin : linEc.m_states) {
			final HashSet<STATE> hiers = new HashSet<STATE>();
			final Iterator<OutgoingReturnTransition<LETTER, STATE>>
				transitions = m_operand.returnSuccessors(lin).iterator();
			if (transitions.hasNext()) {
				do {
					hiers.add(transitions.next().getHierPred());
				} while (transitions.hasNext());
				lin2hier.put(lin, hiers);
			}
		}
		
		HashMap<EquivalenceClass, HashSet<EquivalenceClass>>
				linEc2hierEc = splitReturnEcTranslation(lin2hier);
		
		splitReturnForwardsAnalysis(linEc2hierEc, true);
		
		while (m_splitEcsReturn.size() > 0) {
			assert (assertSetProperty(m_splitEcsReturn));
			splitReturnExecute(m_splitEcsReturn);
			linEc2hierEc = splitReturnEcTranslation(lin2hier);
			m_splitEcsReturn = new LinkedList<EquivalenceClass>();
			splitReturnForwardsAnalysis(linEc2hierEc, true);
		}
		
		splitReturnForwardsAnalysis(linEc2hierEc, false);
		
		if (m_splitEcsReturn.size() > 0) {
			assert (assertSetProperty(m_splitEcsReturn));
			splitReturnExecute(m_splitEcsReturn);
			m_splitEcsReturn = new LinkedList<EquivalenceClass>();
		}
	}
	
	/**
	 * This method assures correctness for the naive return split.
	 * 
	 * Currently it just executes the old return split, which seems to be too
	 * expensive. Hierarchical states are not analyzed.
	 * 
	 * @param linEc the linear equivalence class
	 */
	private void splitReturnCorrectnessNoHier(final EquivalenceClass linEc) {
		if (DEBUG2)
			System.err.println("\nNEW CORRECTNESS RETURN SPLITTING");
		
		final HashMap<STATE, HashSet<STATE>> lin2hier =
				new HashMap<STATE, HashSet<STATE>>();
		for (final STATE lin : linEc.m_states) {
			final HashSet<STATE> hiers = new HashSet<STATE>();
			final Iterator<OutgoingReturnTransition<LETTER, STATE>>
				transitions = m_operand.returnSuccessors(lin).iterator();
			if (transitions.hasNext()) {
				do {
					hiers.add(transitions.next().getHierPred());
				} while (transitions.hasNext());
				lin2hier.put(lin, hiers);
			}
		}
		
		HashMap<EquivalenceClass, HashSet<EquivalenceClass>>
				linEc2hierEc = splitReturnEcTranslation(lin2hier);
		
		splitReturnForwardsAnalysis(linEc2hierEc, false);
		
		if (m_splitEcsReturn.size() > 0) {
			assert (assertSetProperty(m_splitEcsReturn));
			splitReturnExecute(m_splitEcsReturn);
			m_splitEcsReturn = new LinkedList<EquivalenceClass>();
		}
	}
	
	/**
	 * This method assures correctness for the naive return split.
	 * No matrix is constructed.
	 * Currently, the hierarchical split is missing. The runtime indicates that
	 * this method is not reasonable.
	 * 
	 * @param linEc the linear equivalence class
	 */
	private void splitReturnCorrectnessNoMatrix(final EquivalenceClass linEc) {
		if (DEBUG2)
			System.err.println("\nNEW CORRECTNESS RETURN SPLITTING");
		
		// find all hierarchical predecessor equivalence classes
		final HashSet<EquivalenceClass> hierEcs =
				new HashSet<EquivalenceClass>();
		for (final STATE lin : linEc.m_states) {
			final Iterator<IncomingReturnTransition<LETTER, STATE>> transitions
					= m_operand.returnPredecessors(lin).iterator();
			while (transitions.hasNext()) {
				hierEcs.add(m_partition.m_state2EquivalenceClass.get(
						transitions.next().getHierPred()));
			}
		}
		
		// linear split
		for (final EquivalenceClass hierEc : hierEcs) {
			for (final STATE hier : hierEc.m_states) {
				final HashMap<LETTER, HashMap<EquivalenceClass,
						HashSet<STATE>>> letter2succEc2lins = new
						HashMap<LETTER, HashMap<EquivalenceClass,
						HashSet<STATE>>>();
				for (final STATE lin : linEc.m_states) {
					if (! m_doubleDecker.isDoubleDecker(lin, hier)) {
						continue;
					}
					final Iterator<OutgoingReturnTransition<LETTER, STATE>>
						transitions = m_operand.returnSuccessorsGivenHier(
								lin, hier).iterator();
					final HashMap<EquivalenceClass, HashSet<STATE>> succEc2lins
						= new HashMap<EquivalenceClass, HashSet<STATE>>();
					if (transitions.hasNext()) {
						do {
							final OutgoingReturnTransition<LETTER, STATE>
								transition = transitions.next();
							final EquivalenceClass succEc = m_partition.
									m_state2EquivalenceClass.get(
											transition.getSucc());
							HashSet<STATE> lins = succEc2lins.get(succEc);
							if (lins == null) {
								lins = new HashSet<STATE>();
								succEc2lins.put(succEc, lins);
							}
							lins.add(lin);
						} while (transitions.hasNext());
					}
					else {
						HashSet<STATE> lins = succEc2lins.get(m_negativeClass);
						if (lins == null) {
							lins = new HashSet<STATE>();
							succEc2lins.put(m_negativeClass, lins);
						}
						lins.add(lin);
					}
				}
				
				// split linear states
				for (final HashMap<EquivalenceClass, HashSet<STATE>>
						succEc2lins : letter2succEc2lins.values()) {
					final Collection<HashSet<STATE>> values =
							succEc2lins.values();
					if (values.size() > 1) {
						hierEc.markSplit(values);
					}
				}
				if (m_splitEcsReturn.size() > 0) {
					splitReturnExecute(m_splitEcsReturn);
					m_splitEcsReturn = new LinkedList<EquivalenceClass>();
				}
			}
		}
		
		// hierarchical split (missing)
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
				if (m_splitAllCallPreds && (m_operand.callSuccessors(state).
							iterator().hasNext())) {
					m_partition.addEcInitialization(
							Collections.singleton(state));
				}
				else if (m_operand.isFinal(state)) {
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
				// TODO<emptyResult> finals.size() = 0 => empty automaton?
				if (finals.size() > 0) {
					m_partition.addEcInitialization(finals);
				}
				if (nonfinals.size() > 0) {
					m_partition.addEcInitialization(nonfinals);
				}
			}
		}
		// predefined modules are already split with respect to final states 
		else {
			assert assertStatesSeparation(modules) :
				"The states in the initial modules are not separated with " +
				"respect to their final status.";
			for (Set<STATE> module : modules) {
				m_partition.addEcInitialization(module);
			}
		}
		
		if (m_splitAllCallPreds) {
			for (final EquivalenceClass ec :
					m_partition.m_equivalenceClasses) {
				ec.m_incomingCall= EIncomingStatus.none; 
			}
		}
		
		if (m_returnSplitCorrectnessEcs != null) {
			m_returnSplitCorrectnessEcs.addAll(
					m_partition.m_equivalenceClasses);
		}
		
		if (DEBUG) {
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
	 * (both linear and hierarchical). Then do the following first for the
	 * linear and then for the hierarchical states:
	 * Mark the simple splits, then find violations due to the neutral states
	 * and break ties on which states to split there.
	 */
	private void splitReturnPredecessors() {
		if (DEBUG2)
			System.err.println("\nNEW RETURN SPLITTING ROUND");
		
		final HashMap<STATE, HashSet<STATE>> lin2hier =
				splitReturnBackwardsAnalysis();
		
		HashMap<EquivalenceClass, HashSet<EquivalenceClass>>
				linEc2hierEc =
				splitReturnEcTranslation(lin2hier);
		
		splitReturnForwardsAnalysis(linEc2hierEc, true);
		
		while (m_splitEcsReturn.size() > 0) {
			assert (assertSetProperty(m_splitEcsReturn));
			splitReturnExecute(m_splitEcsReturn);
			linEc2hierEc = splitReturnEcTranslation(lin2hier);
			m_splitEcsReturn = new LinkedList<EquivalenceClass>();
			splitReturnForwardsAnalysis(linEc2hierEc, true);
		}
		
		splitReturnForwardsAnalysis(linEc2hierEc, false);
		
		if (m_splitEcsReturn.size() > 0) {
			assert (assertSetProperty(m_splitEcsReturn));
			splitReturnExecute(m_splitEcsReturn);
			m_splitEcsReturn = new LinkedList<EquivalenceClass>();
		}
	}
	
	/**
	 * This method finds all involved linear and hierarchical equivalence
	 * classes for all successor equivalence classes currently in the work
	 * list for the return split.
	 * 
	 * @return map linear state to hierarchical states
	 */
	private HashMap<STATE, HashSet<STATE>> splitReturnBackwardsAnalysis() {
		if (DEBUG2)
			System.err.println("analyzing backwards");
		final HashMap<STATE, HashSet<STATE>> lin2hier =
				new HashMap<STATE, HashSet<STATE>>(computeHashSetCapacity(
						m_partition.m_equivalenceClasses.size()));
		
		// find all involved linear and hierarchical states
		while (m_workListRet.hasNext()) {
			EquivalenceClass succEc = m_workListRet.next();
			boolean incomingReturns = false;
			
			for (final STATE succ : succEc.m_states) {
				final Iterator<IncomingReturnTransition<LETTER, STATE>> edges =
						m_operand.returnPredecessors(succ).iterator();
				if (edges.hasNext()) {
					incomingReturns = true;
					do {
						final IncomingReturnTransition<LETTER, STATE> edge =
								edges.next();
						final STATE lin = edge.getLinPred();
						HashSet<STATE> hiers = lin2hier.get(lin);
						if (hiers == null) {
							hiers = new HashSet<STATE>();
							lin2hier.put(lin, hiers);
						}
						hiers.add(edge.getHierPred());
					} while (edges.hasNext());
				}
			}
			
			// no return transitions found, remember that
			if (! incomingReturns) {
				succEc.m_incomingRet = EIncomingStatus.none;
				if (STATISTICS)
					++m_noIncomingTransitions;
			}
			
			if (DEBUG2)
				System.err.println(" succEc: " + succEc.toStringShort() +
						" has " + (incomingReturns ? "" : "no ") + "returns");
		}
		return lin2hier;
	}
	
	/**
	 * This method translates the mapping of linear to hierarchical states to
	 * a mapping of linear to hierarchical equivalence classes.
	 * 
	 * @param lin2hier map linear state to hierarchical states
	 * @return map linear equivalence class to hierarchical equivalence classes
	 */
	private HashMap<EquivalenceClass, HashSet<EquivalenceClass>>
			splitReturnEcTranslation(
			final HashMap<STATE, HashSet<STATE>> lin2hier) {
		if (DEBUG2)
			System.err.println("\ntranslating to ECs");
		
		final HashMap<EquivalenceClass, HashSet<EquivalenceClass>>
			linEc2hierEcs = new HashMap<EquivalenceClass,
			HashSet<EquivalenceClass>>(computeHashSetCapacity(
					lin2hier.size()));
		for (final Entry<STATE, HashSet<STATE>> entry : lin2hier.entrySet()) {
			final EquivalenceClass linEc =
					m_partition.m_state2EquivalenceClass.get(entry.getKey());
			HashSet<EquivalenceClass> hierEcs = linEc2hierEcs.get(linEc);
			if (hierEcs == null) {
				hierEcs = new HashSet<EquivalenceClass>();
				linEc2hierEcs.put(linEc, hierEcs);
			}
			for (final STATE hier : entry.getValue()) {
				hierEcs.add(m_partition.m_state2EquivalenceClass.get(hier));
			}
		}
		
		if (DEBUG2)
			System.err.println("resulting map: " + linEc2hierEcs);
		
		return linEc2hierEcs;
	}
	
	/**
	 * This method triggers for each given pair of linear and hierarchical
	 * equivalence classes the linear and the hierarchical return split.
	 * 
	 * @param linEc2hierEc map linear EC to hierarchical EC
	 * @param linearAnalysis analysis: true = linear, false = hierarchical
	 */
	private void splitReturnForwardsAnalysis(final HashMap
			<EquivalenceClass, HashSet<EquivalenceClass>> linEc2hierEc,
			final boolean linearAnalysis) {
		for (final Entry<EquivalenceClass, HashSet<EquivalenceClass>> entry :
				linEc2hierEc.entrySet()) {
			final EquivalenceClass linEc = entry.getKey();
			final boolean linEcSingleton = linEc.m_states.size() == 1;
			final HashSet<EquivalenceClass> hierEcs = entry.getValue();
			
			if (DEBUG2)
				System.err.println("\nlinEc: " + linEc.toStringShort());
			
			// get matrix
			Matrix matrix = linEc.m_matrix;
			if (matrix == null) {
				linEc.initializeMatrix(hierEcs);
				matrix = linEc.m_matrix;
			}
			if (matrix == m_singletonMatrix) {
				if (DEBUG2) {
					System.err.println(" ignoring matrix: " + matrix);
				}
				
				continue;
			}
			
			if (DEBUG2)
				System.err.println("matrix: " + matrix);
			
			final HashMap<STATE, HashMap<STATE, HashMap<LETTER,
				HashSet<STATE>>>> hier2lin2letter2succ =
				matrix.m_hier2lin2letter2succ;
			
			for (final EquivalenceClass hierEc : hierEcs) {
				if (DEBUG2)
					System.err.println(" hierEc: " + hierEc.toStringShort());
				
				if (linEcSingleton && hierEc.m_states.size() == 1) {
					if (DEBUG2)
						System.err.println("  ignoring singletons");
					
					if (STATISTICS)
						++m_ignoredReturnSingletons1x1;
					
					continue;
				}
				
				/*
				 * find relevant rows
				 * (avoids duplicate computations for the hierarchical split)
				 */
				final ArrayList<MatrixRow> relevantRows =
					new ArrayList<MatrixRow>(hierEc.m_states.size());
				for (final STATE hier : hierEc.m_states) {
					final HashMap<STATE, HashMap<LETTER, HashSet<STATE>>> map =
							hier2lin2letter2succ.get(hier);
					if ((map != null) && (map.size() > 0)) {
						relevantRows.add(new MatrixRow(hier, map));
					}
					else {
						if (DEBUG2)
							System.err.println(" ignoring hier " + hier);
					}
				}
				
				if (DEBUG2)
					System.err.println(" relevant rows: " + relevantRows);
				
				// linear states analysis
				if (linearAnalysis) {
					if (! linEcSingleton) {
						SplitReturnAnalyzeLinear(hier2lin2letter2succ, linEc,
								relevantRows);
					}
				}
				// hierarchical states analysis
				else {
					if (relevantRows.size() > 1) {
						splitReturnAnalyzeHierarchical(hier2lin2letter2succ,
								hierEc, relevantRows);
					}
				}
			}
		}
	}
	
	/**
	 * This method checks and potentially triggers a linear return split.
	 *
	 * TODO<nondeterminism> at most one successor for deterministic automata,
	 *                      offer improved version
	 *                      (no Set<STATE>, no Set<EquivalenceClass>)?
	 * 
	 * TODO<ignoreMarked> ignore already marked pairs
	 * 
	 * @param hier2lin2letter2succ map hier. to lin. to letter to succ. state
	 * @param linEc linear equivalence class
	 * @param rows matrix rows (hierarchical states)
	 */
	private void SplitReturnAnalyzeLinear(final HashMap<STATE, HashMap<STATE,
			HashMap<LETTER, HashSet<STATE>>>> hier2lin2letter2succ,
			final EquivalenceClass linEc,
			final ArrayList<MatrixRow> rows) {
		if (DEBUG2)
			System.err.println("-linear analysis");
		
		for (final MatrixRow row : rows) {
			final HashMap<STATE, HashMap<LETTER, HashSet<STATE>>>
				lin2letter2succ = row.m_lin2letter2succ;
			if (DEBUG2)
				System.err.println(" hier " + row.m_hier + " -> " +
						lin2letter2succ);
			
			if (lin2letter2succ.size() == 1) {
				if (DEBUG2)
					System.err.println("  only one entry, ignore");
				
				continue;
			}
			
			final int size = computeHashSetCapacity(lin2letter2succ.size());
			final HashMap<HashMap<LETTER, HashSet<EquivalenceClass>>,
				HashSet<STATE>> letter2succEc2lin =
				new HashMap<HashMap<LETTER, HashSet<EquivalenceClass>>,
				HashSet<STATE>>(size);
			final HashSet<STATE> noTransitions = new HashSet<STATE>(size);
			for (final Entry<STATE, HashMap<LETTER, HashSet<STATE>>> entry :
					lin2letter2succ.entrySet()) {
				final STATE lin = entry.getKey();
				assert (linEc.m_states.contains(lin));
				final HashMap<LETTER, HashSet<STATE>> letter2succ =
						entry.getValue();
				
				if (DEBUG2)
					System.err.println("   lin: " + lin);
				
				if (letter2succ == m_downStateMap) {
					if (DEBUG2)
						System.err.println("   no transition, but DS");
					
					noTransitions.add(lin);
					continue;
				}
				
				final HashMap<LETTER, HashSet<EquivalenceClass>>
						letter2succEc = new HashMap<LETTER,
						HashSet<EquivalenceClass>>(
								computeHashSetCapacity(letter2succ.size()));
				for (final Entry<LETTER, HashSet<STATE>> innerEntry :
						letter2succ.entrySet()) {
					final LETTER letter = innerEntry.getKey();
					final HashSet<STATE> succs = innerEntry.getValue();
					
					final HashSet<EquivalenceClass> succEcs =
							new HashSet<EquivalenceClass>(
									computeHashSetCapacity(succs.size()));
					
					if (DEBUG2)
						System.err.println("   letter: " + letter +
								", succs: " + succs);
					
					for (final STATE succ : succs) {
						succEcs.add(m_partition.m_state2EquivalenceClass.
								get(succ));
					}
					
					letter2succEc.put(letter, succEcs);
				}
				
				HashSet<STATE> lins = letter2succEc2lin.get(letter2succEc);
				if (lins == null) {
					lins = new HashSet<STATE>();
					letter2succEc2lin.put(letter2succEc, lins);
				}
				lins.add(lin);
				
				if (DEBUG2)
					System.err.println("   adding: " + lin + " to " +
							letter2succEc);
			}
			
			if (DEBUG2)
				System.err.println("    receiving: " + letter2succEc2lin +
						" and {{DS}=" + noTransitions + "}");
			
			if (noTransitions.size() > 0) {
				letter2succEc2lin.put(null, noTransitions);
			}
			
			if (letter2succEc2lin.size() <= 1) {
				if (DEBUG2)
					System.err.println("    no linear split");
			}
			else {
				if (DEBUG2)
					System.err.println("    mark linear split of " +
							linEc.toStringShort() + ": " +
							letter2succEc2lin.values());
				
				linEc.markSplit(letter2succEc2lin.values());
			}
		}
	}
	
	/**
	 * This method checks and potentially triggers a hierarchical return split.
	 * 
	 * TODO<nondeterminism> at most one successor for deterministic automata,
	 *                      offer improved version
	 *                      (no Set<STATE>, no Set<EquivalenceClass>)?
	 * 
	 * @param hier2lin2letter2succ map hier. to lin. to letter to succ. state
	 * @param hierEc hierarchical equivalence class
	 * @param rows matrix rows (hierarchical states)
	 */
	private void splitReturnAnalyzeHierarchical(final HashMap<STATE,
			HashMap<STATE, HashMap<LETTER, HashSet<STATE>>>>
			hier2lin2letter2succ,
			final EquivalenceClass hierEc, final ArrayList<MatrixRow> rows) {
		if (DEBUG2)
			System.err.println("-hierarchical analysis");
		
		final int size = rows.size();
		
		if (DEBUG2)
			System.err.println("  rows remaining: " + size);
		
		if (size <= 1) {
			if (DEBUG2)
				System.err.println("   ignore");
			
			return;
		}
		
		final int modSize = computeHashSetCapacity(size);
		final HashMap<HashMap<LETTER, HashSet<EquivalenceClass>>,
			HashSet<STATE>> letter2succEc2hier =
			new HashMap<HashMap<LETTER, HashSet<EquivalenceClass>>,
			HashSet<STATE>>(modSize);
		final HashSet<STATE> noTransitions = new HashSet<STATE>(modSize);
		final int hierEcModSize =
				computeHashSetCapacity(hierEc.m_states.size());
		
		// go through rows (each entry per row behaves the same)
		for (int i = 0; i < size; ++i) {
			final MatrixRow row = rows.get(i);
			final STATE hier = row.m_hier;
			// choose the first entry in this row
			final HashMap<LETTER, HashSet<STATE>> letter2succ =
					row.m_lin2letter2succ.values().iterator().next();
			
			if (DEBUG2)
				System.err.println(" hier " + hier + " -> " + letter2succ);
			
			if (letter2succ == m_downStateMap) {
				noTransitions.add(hier);
				continue;
			}
			
			// translate to map with equivalence class
			final HashMap<LETTER, HashSet<EquivalenceClass>> letter2succEc =
					new HashMap<LETTER, HashSet<EquivalenceClass>>(
							computeHashSetCapacity(letter2succ.size()));
			for (final Entry<LETTER, HashSet<STATE>> entry :
					letter2succ.entrySet()) {
				final LETTER letter = entry.getKey();
				final HashSet<STATE> succs = entry.getValue();
				final HashSet<EquivalenceClass> succEcs =
						new HashSet<EquivalenceClass>(
								computeHashSetCapacity(succs.size()));
				for (final STATE succ : succs) {
					succEcs.add(m_partition.m_state2EquivalenceClass.
							get(succ));
				}
				letter2succEc.put(letter, succEcs);
			}
			if (DEBUG2)
				System.err.println("  letter2succEc: " + letter2succEc);
			
			HashSet<STATE> hiers = letter2succEc2hier.get(letter2succEc);
			if (hiers == null) {
				hiers = new HashSet<STATE>(hierEcModSize);
				letter2succEc2hier.put(letter2succEc, hiers);
			}
			hiers.add(hier);
		}
		
		if (DEBUG2)
			System.err.println("    receiving: " + letter2succEc2hier +
					" and {{DS}=" + noTransitions + "}");
		
		if (noTransitions.size() > 0) {
			letter2succEc2hier.put(null, noTransitions);
		}
		
		if (letter2succEc2hier.size() > 1) {
			if (DEBUG2)
				System.err.println("    mark hierarchical split of " +
						hierEc.toStringShort() + ": " +
						letter2succEc2hier.values());
			
			hierEc.markSplit(letter2succEc2hier.values());
		}
	}
	
	/**
	 * This method executes the return splits for all passed equivalence
	 * classes. The input has information of which states must be separated.
	 * The goal is to come up with a splitting that satisfies the separations.
	 * 
	 * The general solution is algorithmically hard, so here the following
	 * heuristic is used:
	 * The general rule is to assign a state to an existing group of states if
	 * possible. If there is more than one possible group, the first one found
	 * is chosen.
	 *
	 * @param splitEquivalenceClasses split equivalence classes
	 */
	private void splitReturnExecute(
			final Collection<EquivalenceClass> splitEquivalenceClasses) {
		if (DEBUG2)
			System.err.println("\n-- executing return splits");
		
		if (STATISTICS) {
			m_returnSeparateTime -= new GregorianCalendar().getTimeInMillis();
		}
		
		for (final EquivalenceClass oldEc : splitEquivalenceClasses) {
			final HashMap<STATE, HashSet<STATE>> state2separatedSet =
					oldEc.m_state2separatedSet;
			assert (state2separatedSet != null);
			
			if (DEBUG2) {
				System.err.print(oldEc);
				System.err.print(" : ");
				System.err.println(state2separatedSet);
			}
			
			// map: color to associated states and blocked states
			int statesRemaining = oldEc.m_states.size();
			final ArrayList<ColorSet> colorSets =
					new ArrayList<ColorSet>(statesRemaining);
			
			// for each state find a color
			outer: for (final Entry<STATE, HashSet<STATE>> stateEntry :
					state2separatedSet.entrySet()) {
				final STATE state = stateEntry.getKey();
				final HashSet<STATE> separatedSet = stateEntry.getValue();
				
				assert (oldEc.m_states.contains(state)) &&
						(separatedSet != null);
				
				// find fitting color
				for (int i = 0; i < colorSets.size(); ++i) {
					// found a fitting color
					final ColorSet colorSet = colorSets.get(i);
					if (! colorSet.m_blocked.contains(state)) {
						colorSet.m_content.add(state);
						colorSet.m_blocked.addAll(separatedSet);
						--statesRemaining;
						continue outer;
					}
				}
				
				// no color available, use a new one
				colorSets.add(new ColorSet(statesRemaining, state,
						separatedSet));
				--statesRemaining;
			}
			
			/*
			 * States without any separation information behave like the states
			 * in the group that remains without a split.
			 */
			assert (statesRemaining >= 0);
			
			if (DEBUG2)
				System.err.println("colorSets: " + colorSets);
			
			/*
			 * If there are no states without any group preference, keep
			 * the biggest set from splitting.
			 * Else keep the smallest set from splitting, since those states
			 * will stay there.
			 * This is to reduce the size of the equivalence classes.
			 * 
			 * NOTE: This typically has nearly no practical influence.
			 */
			int remainingColor = 0;
			if (statesRemaining == 0) {
				// find maximum set
				int maxSize = colorSets.get(0).m_content.size();
				for (int i = colorSets.size() - 1; i > 0; --i) {
					final int size = colorSets.get(i).m_content.size();
					if (size > maxSize) {
						maxSize = size;
						remainingColor = i;
					}
				}
			}
			else {
				// find minimum set
				int minSize = colorSets.get(0).m_content.size();
				for (int i = colorSets.size() - 1; i > 0; --i) {
					final int size = colorSets.get(i).m_content.size();
					if (size < minSize) {
						minSize = size;
						remainingColor = i;
					}
				}
			}
			
			// finally split the equivalence class
			int i = colorSets.size();
			while (true) {
				if (--i == remainingColor) {
					--i;
				}
				if (i < 0) {
					break;
				}
				
				final EquivalenceClass newEc =
						m_partition.addEcReturn(colorSets.get(i).m_content,
								oldEc);
				
				if (STATISTICS)
					++m_splitsWithChange;
				
				if (DEBUG2)
					System.err.println("new equivalence class: " +
							newEc.toStringShort());
			}
			
			// reset separation mapping
			oldEc.m_state2separatedSet = null;
		}
		
		if (STATISTICS) {
			m_returnSeparateTime += new GregorianCalendar().getTimeInMillis();
		}
	}
	
	/**
	 * This method is an alternative linear return split.
	 */
	private void splitReturnLinearAlt() {
		final EquivalenceClass succEc = m_workListRet.next();
		
		if (DEBUG4)
			System.err.println("L succEc " + succEc.toStringShort());
		
		final HashMap<EquivalenceClass,
			HashSet<IncomingReturnTransition<LETTER, STATE>>>
			linEc2trans = splitReturnFindTransitionsAlt(succEc);
		
		if (linEc2trans.isEmpty()) {
			succEc.m_incomingRet = EIncomingStatus.none;
			return;
		}
		
		if (DEBUG4)
			System.err.println("linEc2trans " + linEc2trans);
		
		for (final Entry<EquivalenceClass, HashSet<IncomingReturnTransition
				<LETTER, STATE>>> entry : linEc2trans.entrySet()) {
			splitReturnLinearAltHelper(entry.getKey(), entry.getValue());
		
		}
	}
	
	/**
	 * This method finds the transitions for the alternative linear return
	 * split.
	 * 
	 * @param succEc successor equivalence class
	 * @return map linear equivalence class to return transitions
	 */
	private HashMap<EquivalenceClass, HashSet<IncomingReturnTransition<LETTER,
			STATE>>> splitReturnFindTransitionsAlt(
			final EquivalenceClass succEc) {
		final HashMap<EquivalenceClass, HashSet<IncomingReturnTransition
				<LETTER, STATE>>> linEc2trans = new HashMap<EquivalenceClass,
				HashSet<IncomingReturnTransition<LETTER,STATE>>>();
		final HashMap<STATE, EquivalenceClass> state2ec =
				m_partition.m_state2EquivalenceClass;
		
		for (final STATE succ : succEc.m_states) {
			for (final IncomingReturnTransition<LETTER, STATE> edge :
				m_operand.returnPredecessors(succ)) {
				final EquivalenceClass linEc = state2ec.get(edge.getLinPred());
				HashSet<IncomingReturnTransition <LETTER, STATE>> edges =
						linEc2trans.get(linEc);
				if (edges == null) {
					edges = new HashSet<IncomingReturnTransition<LETTER,
							STATE>>();
					linEc2trans.put(linEc, edges);
				}
				edges.add(edge);
			}
		}
		return linEc2trans;
	}
	
	/**
	 * This method helps the alternative linear return split.
	 * 
	 * @param linEc linear equivalence class
	 * @param transitions return transitions
	 */
	private void splitReturnLinearAltHelper(final EquivalenceClass linEc,
			final Collection<IncomingReturnTransition<LETTER, STATE>>
			transitions) {
		if (DEBUG4)
			System.err.println("linEc " + linEc + ", transitions " +
					transitions);
		
		final Set<STATE> linStates = linEc.m_states;
		final int linEcSize = linStates.size();
		if (linEcSize == 1) {
			return;
		}
		
		final HashSet<STATE> linsVisited = new HashSet<STATE>(
				computeHashSetCapacity(linEcSize));
		final HashMap<STATE, HashMap<LETTER, HashSet<STATE>>>
				hier2letters2lins = new HashMap<STATE, HashMap<LETTER,
				HashSet<STATE>>>(computeHashSetCapacity(transitions.size()));
		
		linEc.m_state2separatedSet = new HashMap<STATE, HashSet<STATE>>(
				computeHashSetCapacity(linEcSize));
		
		// find all linear predecessors
		for (final IncomingReturnTransition<LETTER, STATE> trans :
				transitions) {
			final STATE hier = trans.getHierPred();
			HashMap<LETTER, HashSet<STATE>> letter2lins =
					hier2letters2lins.get(hier);
			if (letter2lins == null) {
				letter2lins = new HashMap<LETTER, HashSet<STATE>>();
				hier2letters2lins.put(hier, letter2lins);
			}
			final LETTER letter = trans.getLetter();
			HashSet<STATE> lins = letter2lins.get(letter);
			if (lins == null) {
				lins = new HashSet<STATE>();
				letter2lins.put(letter, lins);
			}
			final STATE lin = trans.getLinPred();
			lins.add(lin);
			linsVisited.add(lin);
		}
		
		if (DEBUG4) {
			System.err.println(" hier2letters2lins " + hier2letters2lins);
			System.err.println(" linsVisited " + linsVisited);
		}
		
		// (linear) states not visited
		final ArrayList<STATE> linsUnvisited =
				new ArrayList<STATE>(linEcSize - linsVisited.size());
		for (final STATE lin : linStates) {
			if (! linsVisited.contains(lin)) {
				linsUnvisited.add(lin);
			}
		}
		
		// mark: all visited from each other and from all non-visited with DS
		for (final Entry<STATE, HashMap<LETTER, HashSet<STATE>>> outerEntry :
				hier2letters2lins.entrySet()) {
			final STATE hier = outerEntry.getKey();
			
			if (DEBUG4)
				System.err.println("  hier " + hier);
			
			// compute sets of DS/no DS states
			// TODO<improve> could be saved for further runs
			final int modSize = computeHashSetCapacity(
					linEcSize - linsVisited.size());
			final HashSet<STATE> noDsStates = new HashSet<STATE>(modSize);
			final HashSet<STATE> dsStates = new HashSet<STATE>(modSize);
			for (final STATE lin : linsUnvisited) {
				if (m_doubleDecker.isDoubleDecker(lin, hier)) {
					dsStates.add(lin);
					
					// mark returns from non-returns
					for (final STATE linPos : linsVisited) {
						linEc.markPair(lin, linPos);
					}
				}
				else {
					noDsStates.add(lin);
				}
			}
			
			if (DEBUG4) {
				System.err.println("  dsStates " + dsStates);
				System.err.println("  noDsStates " + noDsStates);
			}
			
			for (final Entry<LETTER, HashSet<STATE>> innerEntry :
					outerEntry.getValue().entrySet()) {
				final HashSet<STATE> lins = innerEntry.getValue();
				
				if (DEBUG4)
					System.err.println("  lins " + lins);
				
				if (lins.size() == linsVisited.size()) {
					if (DEBUG4)
						System.err.println("   ignore");
					
					continue;
				}
				
				for (final STATE lin : linsVisited) {
					if ((! lins.contains(lin)) &&
							(m_doubleDecker.isDoubleDecker(lin, hier))) {
						if (DEBUG4)
							System.err.println("   later split");
						
						// mark different returns
						for (final STATE linPos : lins) {
							linEc.markPair(lin, linPos);
						}
					}
				}
			}
		}
		
		if (linEc.m_state2separatedSet.size() > 0) {
			if (DEBUG4)
				System.err.println(" SPLIT");
			
			m_splitEcsReturn.add(linEc);
			splitReturnExecute(m_splitEcsReturn);
			m_splitEcsReturn = new LinkedList<EquivalenceClass>();
		}
		else {
			if (DEBUG4)
				System.err.println(" NO SPLIT");
		}
		linEc.m_state2separatedSet = null;
	}
	
	/**
	 * This method is an alternative hierarchical return split.
	 */
	private void splitReturnHierAlt() {
		EquivalenceClass succEc;
		while (true) {
			succEc = m_workListRetHier.next();
			if (succEc.m_incomingRet == EIncomingStatus.none) {
				if (! m_workListRetHier.hasNext()) {
					return;
				}
			}
			else {
				break;
			}
		}
		
		if (DEBUG4)
			System.err.println("H succEc " + succEc.toStringShort());
		
		final HashMap<EquivalenceClass, HashSet<EquivalenceClass>>
			hierEc2linEcs = splitReturnFindOutgoingTransitions(succEc);
		
		if (hierEc2linEcs.isEmpty()) {
			succEc.m_incomingRet = EIncomingStatus.none;
			return;
		}
		
		if (DEBUG4)
			System.err.println("linEc2hierEcs " + hierEc2linEcs);
		
		for (final Entry<EquivalenceClass, HashSet<EquivalenceClass>> entry :
				hierEc2linEcs.entrySet()) {
			splitReturnHierAltHelper(entry.getKey(), entry.getValue());
		}
	}
	
	/**
	 * This method finds the transitions for the alternative hierarchical
	 * return split.
	 * 
	 * @param succEc successor equivalence class
	 * @return map hierarchical equivalence class to linear equivalence class
	 */
	private HashMap<EquivalenceClass, HashSet<EquivalenceClass>>
			splitReturnFindOutgoingTransitions(final EquivalenceClass succEc) {
		final HashMap<EquivalenceClass, HashSet<EquivalenceClass>>
				hierEc2linEcs = new HashMap<EquivalenceClass,
				HashSet<EquivalenceClass>>();
		final HashMap<STATE, EquivalenceClass> state2ec =
				m_partition.m_state2EquivalenceClass;
		
		for (final STATE succ : succEc.m_states) {
			for (final IncomingReturnTransition<LETTER, STATE> edge :
				m_operand.returnPredecessors(succ)) {
				final EquivalenceClass hierEc =
						state2ec.get(edge.getHierPred());
				HashSet<EquivalenceClass> linEcs = hierEc2linEcs.get(hierEc);
				if (linEcs == null) {
					linEcs = new HashSet<EquivalenceClass>();
					hierEc2linEcs.put(hierEc, linEcs);
				}
				linEcs.add(state2ec.get(edge.getLinPred()));
			}
		}
		return hierEc2linEcs;
	}
	
	/**
	 * This method helps the alternative hierarchical return split.
	 * 
	 * @param hierEc hierarchical equivalence class
	 * @param linEcs linear equivalence classes
	 */
	private void splitReturnHierAltHelper(final EquivalenceClass hierEc,
			final HashSet<EquivalenceClass> linEcs) {
		if (DEBUG4)
			System.err.println("hierEc " + hierEc + ", linEcs " + linEcs);
		
		final Set<STATE> hierStates = hierEc.m_states;
		final int hierEcSize = hierStates.size();
		if (hierEcSize == 1) {
			if (DEBUG4)
				System.err.println("   ignore");
			
			return;
		}
		
		hierEc.m_state2separatedSet = new HashMap<STATE, HashSet<STATE>>(
				computeHashSetCapacity(hierEcSize));
		final HashMap<STATE, EquivalenceClass> state2ec =
				m_partition.m_state2EquivalenceClass;
		
		for (final EquivalenceClass linEc : linEcs) {
			final HashMap<HashMap<EquivalenceClass, HashSet<LETTER>>,
				HashSet<STATE>> succEc2letter2hiers =
				new HashMap<HashMap<EquivalenceClass, HashSet<LETTER>>,
				HashSet<STATE>>();
			
			for (final STATE hier : hierStates) {
				final HashMap<EquivalenceClass, HashSet<LETTER>>
					succEc2letters = new HashMap<EquivalenceClass,
					HashSet<LETTER>>(computeHashSetCapacity(hierEcSize));
				
				inner: for (final STATE lin : linEc.m_states) {
					if (m_doubleDecker.isDoubleDecker(lin, hier)) {
						final Iterator<OutgoingReturnTransition<LETTER, STATE>>
							edges = m_operand.returnSuccessorsGivenHier(lin,
									hier).iterator();
						if (edges.hasNext()) {
							do {
								final OutgoingReturnTransition<LETTER, STATE>
								edge = edges.next();
								final EquivalenceClass succEc =
										state2ec.get(edge.getSucc());
								HashSet<LETTER> letters =
										succEc2letters.get(succEc);
								if (letters == null) {
									letters = new HashSet<LETTER>();
									succEc2letters.put(succEc, letters);
								}
								letters.add(edge.getLetter());
							} while (edges.hasNext());
							break inner;
						}
						else {
							succEc2letters.put(m_negativeClass, null);
							break inner;
						}
					}
				}
				
				assert (! succEc2letters.isEmpty());
				HashSet<STATE> hiers = succEc2letter2hiers.get(succEc2letters);
				if (hiers == null) {
					hiers = new HashSet<STATE>();
					succEc2letter2hiers.put(succEc2letters, hiers);
				}
				hiers.add(hier);
			}
			
			if (succEc2letter2hiers.size() > 1) {
				hierEc.markSplit(succEc2letter2hiers.values());
			}
		}
		
		if (hierEc.m_state2separatedSet.size() > 0) {
			if (DEBUG4)
				System.err.println(" SPLIT");
			
			m_splitEcsReturn.add(hierEc);
			splitReturnExecute(m_splitEcsReturn);
			m_splitEcsReturn = new LinkedList<EquivalenceClass>();
		}
		else {
			if (DEBUG4)
				System.err.println(" NO SPLIT");
		}
		hierEc.m_state2separatedSet = null;
	}
	
	/**
	 * This method implements an optional first linear return split before
	 * considering the real return split.
	 * 
	 * NOTE: The split is not perfect in the sense that once an equivalence
	 * class has been split, its return predecessors are not reconsidered.
	 * This could be added, but is currently not the case, since this is only
	 * meant as a preprocessing step.
	 */
	private void splitReturnPredecessorsFirstTime() {
		if (DEBUG2)
			System.err.println("\nNEW RETURN SPLITTING ROUND");
		
		if (DEBUG3) {
			if (m_partition.m_equivalenceClasses.size() ==
					m_workListRet.m_queue.size()) {
				System.err.println("first return split, starting with " +
						m_partition.m_equivalenceClasses.size() + " ECs");
			}
		}
		
		if (STATISTICS) {
			m_returnFirstTime -= new GregorianCalendar().getTimeInMillis();
		}
		
		EquivalenceClass linEc;
		HashSet<STATE> hiers;
		final Set<Entry<EquivalenceClass, HashSet<STATE>>> entrySet =
				m_firstReturnLin2hiers.entrySet();
		
		while (true) {
			// continue from last time
			if (! entrySet.isEmpty()) {
				assert (entrySet.size() == 1);
				final Entry<EquivalenceClass, HashSet<STATE>> entry =
						entrySet.iterator().next();
				linEc = entry.getKey();
				hiers = entry.getValue();
			}
			else if (m_workListRet.hasNext()) {
				linEc = m_workListRet.next();
			}
			else {
				break;
			}
			
			if (DEBUG3)
				System.err.println("linEc size: " + linEc.m_states.size());
			
			// singleton equivalence classes are ignored
			if (linEc.m_states.size() == 1) {
				if (DEBUG3)
					System.err.println(" ignoring");
				
				continue;
			}
			
			// analyse linear equivalence class
			hiers = splitReturnPredecessorsFirstTimeRepeat(linEc,
					new HashSet<STATE>());
			
			while ((hiers != null) && (! hiers.isEmpty())) {
				// new internal and call splits available, prefer them
				if (m_workListIntCall.hasNext()) {
					m_firstReturnLin2hiers =
							new HashMap<EquivalenceClass, HashSet<STATE>>(2);
					m_firstReturnLin2hiers.put(linEc, hiers);
					break;
				}
				
				// singleton equivalence classes are ignored
				if (linEc.m_states.size() == 1) {
					if (DEBUG3)
						System.err.println(" ignoring");
					
					continue;
				}
				
				// analyse linear equivalence class
				hiers = splitReturnPredecessorsFirstTimeRepeat(linEc, hiers);
			}
		}
		
		// no equivalence classes left, switch to normal return split
		m_firstReturnSplit = false;
		m_workListRet.fillWithAll();
		
		if (STATISTICS) {
			m_returnFirstTime += new GregorianCalendar().getTimeInMillis();
		}
		
		if (DEBUG3)
			System.err.println("first return split executed, now having " +
					m_partition.m_equivalenceClasses.size() + " ECs");
	}
	
	/**
	 * This method is repeated in the loop of the optional first return split.
	 * 
	 * @param linEc the linear equivalence class
	 * @param oldHiers old hierarchical predecessors
	 * @return hierarchical states visited so far
	 */
	private HashSet<STATE> splitReturnPredecessorsFirstTimeRepeat(
			final EquivalenceClass linEc, HashSet<STATE> oldHiers) {
		// analyse linear equivalence class
		oldHiers = splitReturnPredecessorsFirstTimeAnalyze(linEc, oldHiers);
		
		// if there are reasons for a split, execute it
		if (m_splitEcsReturn.size() == 1) {
			if (DEBUG3)
				System.err.println("splitting EC of size " +
						linEc.m_states.size());
			
			assert (m_splitEcsReturn.get(0) == linEc);
			splitReturnExecute(m_splitEcsReturn);
			m_splitEcsReturn.clear();
		}
		else {
			assert (m_splitEcsReturn.size() == 0);
		}
		return oldHiers;
	}
	
	/**
	 * This method checks whether the given equivalence class must be split
	 * linearly. If so, the states are marked.
	 * 
	 * This is a mixture of a full and a random split, since only a fixed
	 * number of hierarchical predecessor states is considered at one time.
	 * If there are more of them, they are considered in a later iteration.
	 * 
	 * @param linEc the linear equivalence class
	 * @param oldHiers old hierarchical predecessors
	 * @return hierarchical states visited so far
	 */
	private HashSet<STATE> splitReturnPredecessorsFirstTimeAnalyze(
			final EquivalenceClass linEc, HashSet<STATE> oldHiers) {
		final Set<STATE> lins = linEc.m_states;
		
		// collect all relevant hierarchical predecessors
		final HashSet<STATE> newHiers = new HashSet<STATE>();
		boolean broke = (oldHiers.size() == 0);
		outer: for (final STATE lin : lins) {
			for (final OutgoingReturnTransition<LETTER, STATE> edge :
					m_operand.returnSuccessors(lin)) {
				final STATE hier = edge.getHierPred();
				if (oldHiers.add(hier)) {
					newHiers.add(hier);
					// fixed number: 150
					if (newHiers.size() == 150) {
						broke = true;
						break outer;
					}
				}
			}
		}
		if (! broke) {
			oldHiers = null;
		}
		
		final int modSize = computeHashSetCapacity(lins.size());
		for (final STATE hier : newHiers) {
			final HashMap<HashMap<LETTER, HashSet<STATE>>, HashSet<STATE>>
					trans2lin = new HashMap<HashMap<LETTER, HashSet<STATE>>,
					HashSet<STATE>>(modSize);
			final HashSet<STATE> noTransitions = new HashSet<STATE>(modSize);
			for (final STATE lin : lins) {
				if (! m_doubleDecker.isDoubleDecker(lin, hier)) {
					continue;
				}
				
				final Iterator<OutgoingReturnTransition<LETTER, STATE>> edges =
						m_operand.returnSuccessorsGivenHier(lin, hier).
						iterator();
				if (edges.hasNext()) {
					final HashMap<LETTER, HashSet<STATE>> transitions =
							new HashMap<LETTER, HashSet<STATE>>();
					do {
						final OutgoingReturnTransition<LETTER, STATE> edge =
								edges.next();
						final LETTER letter = edge.getLetter();
						HashSet<STATE> succs = transitions.get(letter);
						if (succs == null) {
							succs = new HashSet<STATE>();
							transitions.put(letter, succs);
						}
						succs.add(edge.getSucc());
					} while (edges.hasNext());
					
					HashSet<STATE> otherLins = trans2lin.get(transitions);
					if (otherLins == null) {
						otherLins = new HashSet<STATE>();
						trans2lin.put(transitions, otherLins);
					}
					otherLins.add(lin);
				}
				else {
					noTransitions.add(lin);
				}
			}
			
			if (noTransitions.size() > 0) {
				trans2lin.put(null, noTransitions);
			}
			if (trans2lin.size() > 1) {
				linEc.markSplit(trans2lin.values());
			}
		}
		
		return oldHiers;
	}
	
	/**
	 * TODO<old>
	 */
	@SuppressWarnings("unchecked")
	private void splitReturnExecuteOld(
			final Collection<EquivalenceClass> splitEquivalenceClasses) {
		if (DEBUG2)
			System.err.println("\n-- executing return splits");
		
		long time;
		if (STATISTICS) {
			time = new GregorianCalendar().getTimeInMillis();
		}
		
		for (final EquivalenceClass oldEc : splitEquivalenceClasses) {
			final HashMap<STATE, HashSet<STATE>> state2separatedSet =
					oldEc.m_state2separatedSet;
			assert (state2separatedSet != null);
			
			if (DEBUG2) {
				System.err.print(oldEc);
				System.err.print(" : ");
				System.err.println(state2separatedSet);
			}
			
			// mapping: state to associated color
			final HashMap<STATE, Integer> state2color =
					new HashMap<STATE, Integer>(
							computeHashSetCapacity(oldEc.m_states.size()));
			// current number of colors
			int colors = 0;
			
			for (final Entry<STATE, HashSet<STATE>> entry :
					state2separatedSet.entrySet()) {
				final STATE state = entry.getKey();
				final HashSet<STATE> separatedSet = entry.getValue();
				
				assert (oldEc.m_states.contains(state)) &&
					(separatedSet != null);
				
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
			assert (colors > 1);
			
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
			
			if (DEBUG2)
				System.err.println("state2color: " + state2color);
			
			// finally split the equivalence class
			for (int i = newEcs.length - 1; i > 0; --i) {
				final HashSet<STATE> newStates = newEcs[i];
				final EquivalenceClass newEc =
						m_partition.addEcReturn(newStates, oldEc);
				
				if (STATISTICS)
					++m_splitsWithChange;
				
				if (DEBUG2)
					System.err.println("new equivalence class: " +
							newEc.toStringShort());
			}
			
			// reset separation mapping
			oldEc.m_state2separatedSet = null;
		}
		
		if (STATISTICS) {
			time = new GregorianCalendar().getTimeInMillis() - time;
			m_returnSeparateTime += time;
		}
	}
	
	/**
	 * This method randomly splits the given equivalence class.
	 * 
	 * If it has outgoing call transitions, it is split into equally sized
	 * blocks of states.
	 * 
	 * Otherwise (without any outgoing call transitions) it keeps states with
	 * no outgoing return transitions together, since these states will never
	 * take part in any matrix and hence can be kept together.
	 * 
	 * @param ec the equivalence class
	 */
	private void splitRandom(EquivalenceClass ec) {
		if (m_operand.callSuccessors(ec.m_states.iterator().next()).
				iterator().hasNext()) {
			splitRandomEqual(ec);
		}
		else {
			splitRandomReturns(ec);
		}
	}
	
	/**
	 * This method randomly splits an equivalence class into equally sized
	 * blocks of states.
	 * 
	 * @param ec the equivalence class
	 */
	private void splitRandomEqual(EquivalenceClass ec) {
		final Set<STATE> oldStates = ec.m_states;
		final int size = computeHashSetCapacity(g_threshold);
		while (oldStates.size() > g_threshold) {
			final HashSet<STATE> newStates = new HashSet<STATE>(size);
			int i = g_threshold;
			for (final STATE state : oldStates) {
				newStates.add(state);
				if (--i == 0) {
					m_partition.addEcReturn(newStates, ec);
					break;
				}
			}
		}
	}
	
	/**
	 * This method randomly splits an equivalence class into equally sized
	 * blocks of states, with one exception: It keeps states without any
	 * outgoing return transitions together.
	 * 
	 * @param ec the equivalence class
	 */
	private void splitRandomReturns(EquivalenceClass ec) {
		final Set<STATE> oldStates = ec.m_states;
		final int size = computeHashSetCapacity(g_threshold);
		final LinkedList<HashSet<STATE>> newClasses =
				new LinkedList<HashSet<STATE>>();
		
		HashSet<STATE> returns = new HashSet<STATE>(size);
		for (final STATE state : oldStates) {
			if (m_operand.returnSuccessors(state).iterator().hasNext()) {
				returns.add(state);
				if (returns.size() == g_threshold) {
					newClasses.add(returns);
					returns = new HashSet<STATE>(size);
				}
			}
		}
		if (returns.size() > 0) {
			newClasses.add(returns);
		}
		else if (newClasses.isEmpty()) {
			return;
		}
		
		int numberOfStates = oldStates.size();
		for (final HashSet<STATE> states : newClasses) {
			assert (states.size() > 0);
			numberOfStates -= states.size();
			
			// no state without return transitions, do not split last class
			if (numberOfStates == 0) {
				break;
			}
			
			m_partition.addEcReturn(states, ec);
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
	 * This is only reasonable if the maximum size is already known.
	 * Java standard sets the load factor to 0.75.
	 * 
	 * @param size maximum number of elements in the hash set
	 * @return hash set size
	 */
	private int computeHashSetCapacity(final int size) {
		return (int) (size * 1.5 + 1);
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
	 * This method checks the assertion that a given list contains an element
	 * only once.
	 * 
	 * @param <T> type parameter
	 * @param list the list
	 * @return true iff each element is contained only once
	 */
	private <T> boolean assertSetProperty(final List<T> list) {
		final HashSet<T> set = new HashSet<T>(
				computeHashSetCapacity(list.size()));
		set.addAll(list);
		return (set.size() == list.size());
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
		 * This method returns a new collection. This is for efficiency
		 * reasons, since first only a list is needed, where later a set is
		 * needed.
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
					m_partition.addEcInitialization((HashSet<STATE>)newStates);
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
	
	/**
	 * This class represents a return split matrix. The columns are the linear
	 * and the rows are the hierarchical predecessor states.
	 * The implementation is not really a matrix, but rather a hash map, since
	 * the matrix would be very sparse.
	 */
	private class Matrix {
		final HashMap<STATE, HashMap<STATE,
			HashMap<LETTER, HashSet<STATE>>>> m_hier2lin2letter2succ;
		
		/**
		 * @param size number of non-singleton 
		 */
		public Matrix(final int size) {
			m_hier2lin2letter2succ = new HashMap<STATE, HashMap<STATE,
					HashMap<LETTER, HashSet<STATE>>>>(
							computeHashSetCapacity(size));
		}
		
		/**
		 * This constructor is only used for the useless 1x1-matrix.
		 */
		private Matrix() {
			m_hier2lin2letter2succ = null;
		}

		@Override
		public String toString() {
			return (m_hier2lin2letter2succ == null)
					? "{1x1-matrix}"
					: m_hier2lin2letter2succ.toString();
		}
	}
	
	/**
	 * This class represents a matrix row. It knows its associated hierarchical
	 * predecessor state and the matrix entries of this row.
	 */
	private class MatrixRow {
		private final STATE m_hier;
		private final HashMap<STATE, HashMap<LETTER, HashSet<STATE>>>
			m_lin2letter2succ;
		
		/**
		 * @param hier the hierarchical state
		 * @param lin2letter2succ the map (matrix row entries)
		 */
		public MatrixRow(final STATE hier, final HashMap<STATE, HashMap<LETTER,
				HashSet<STATE>>> lin2letter2succ) {
			m_hier = hier;
			assert (! lin2letter2succ.isEmpty());
			m_lin2letter2succ = lin2letter2succ;
		}
		
		@Override
		public String toString() {
			return m_hier + " -> " + m_lin2letter2succ;
		}
	}
	
	/**
	 * This class is a dummy map. It is currently used for the empty return
	 * split matrix row.
	 */
	@SuppressWarnings({ "serial", "rawtypes" })
	private class DummyMap extends HashMap {
		@Override
		public HashSet<STATE> get(final Object key) {
			return null;
		}
		
		@Override
		public String toString() {
			return "{dummy map}";
		}
	}
	
	/**
	 * This class stores all states for a certain color and all states that are
	 * blocked for this color.
	 */
	private class ColorSet {
		// associated states
		final HashSet<STATE> m_content;
		final HashSet<STATE> m_blocked;
		
		/**
		 * @param size size of the equivalence class
		 * @param state the first state
		 * @param blocked the set of blocked states
		 */
		public ColorSet(final int size, final STATE state,
				final HashSet<STATE> blocked) {
			m_content = new HashSet<STATE>(computeHashSetCapacity(size));
			m_content.add(state);
			m_blocked = blocked;
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
		
		public Partition() {
			m_equivalenceClasses = new LinkedList<EquivalenceClass>();
			m_state2EquivalenceClass = new HashMap<STATE, EquivalenceClass>(
					computeHashSetCapacity(m_operand.size()));
		}
		
		/**
		 * This method adds an equivalence class (also to the work list)
		 * during the initialization phase.
		 *
		 * @param module the states in the equivalence class
		 */
		private void addEcInitialization(final Set<STATE> module) {
			final EquivalenceClass ec = new EquivalenceClass(module);
			m_equivalenceClasses.add(ec);
			for (STATE state : module) {
				m_state2EquivalenceClass.put(state, ec);
			}
		}
		
		/**
		 * This method adds an equivalence class to the partition that resulted
		 * from an internal or call split.
		 *
		 * @param parent the parent equivalence class
		 * @return the equivalence class
		 */
		private EquivalenceClass addEcIntCall(final EquivalenceClass parent) {
			Set<STATE> newStates = parent.m_intersection;
			if (newStates.size() > parent.m_states.size()) {
				newStates = parent.m_states;
				parent.m_states = parent.m_intersection;
			}
			final EquivalenceClass ec =
					new EquivalenceClass(newStates, parent);
			m_equivalenceClasses.add(ec);
			for (STATE state : ec.m_states) {
				m_state2EquivalenceClass.put(state, ec);
			}
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
		private EquivalenceClass addEcReturn(final Set<STATE> states,
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
		 * This method splits a state from its equivalence class during the
		 * internal and call split. The equivalence class is remembered.
		 * 
		 * @param state the state
		 * @param splitEcs the list of split equivalence classes
		 */
		private void splitState(final STATE state,
				final LinkedList<EquivalenceClass> splitEcs) {
			final EquivalenceClass ec = m_state2EquivalenceClass.get(state);
			
			// first occurrence of the equivalence class, mark it
			if (ec.m_intersection.size() == 0) {
				assert (! splitEcs.contains(ec));
				splitEcs.add(ec);
			}
			else {
				assert (splitEcs.contains(ec));
			}
			
			// move state to intersection set
			ec.m_intersection.add(state);
			
			// remove state from old set
			ec.m_states.remove(state);
		}
		
		/**
		 * This method finally splits the marked equivalence classes into two
		 * (for the internal and call split).
		 * The states have already been split in the equivalence class before.
		 * Only if there are states remaining the split is executed, otherwise
		 * the old equivalence class is restored.
		 * 
		 * @param states set of states to split
		 * @return true iff a split occurred
		 */
		public boolean splitEquivalenceClasses(final Iterable<STATE> states) {
			boolean splitOccurred = false;
			final LinkedList<EquivalenceClass> splitEcs =
					new LinkedList<EquivalenceClass>();
			
			// process splits
			for (final STATE state : states) {
				if (DEBUG)
					System.out.println("splitting state " + state);
				splitState(state, splitEcs);
			}
			
			// check and finalize splits
			for (final EquivalenceClass ec : splitEcs) {
				// split removed every state, restore equivalence class
				if (ec.m_states.isEmpty()) {
					ec.m_states = ec.m_intersection;
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
					addEcIntCall(ec);
				}
				
				// reset equivalence class
				ec.reset();
			}
			
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
	 */
	private class EquivalenceClass {
		// unique ID (useful for hashCode and so for deterministic runs)
		private final int m_id;
		// the states
		private Set<STATE> m_states;
		// intersection set that finally becomes a new equivalence class
		private Set<STATE> m_intersection;
		// status regarding incoming transitions
		private EIncomingStatus m_incomingInt, m_incomingCall, m_incomingRet;
		// mapping: state to states that are separated
		private HashMap<STATE, HashSet<STATE>> m_state2separatedSet;
		// matrix with return transition information
		private Matrix m_matrix;
		
		// TODO<alternative>
		private EIncomingStatus m_outgoingRet;
		
		/**
		 * This is a partial constructor which is used for both initialization
		 * and splitting.
		 * 
		 * @param states the set of states for the equivalence class
		 * @param fromSplit flag currently ignored (necessary for overloading)
		 */
		private EquivalenceClass(final Set<STATE> states,
				final boolean fromSplit) {
			assert (states.size() > 0);
			m_id = ++m_ids;
			m_states = states;
			reset();
		}
		
		/**
		 * This constructor is reserved for the placeholder equivalence class.
		 */
		private EquivalenceClass() {
			m_id = 0;
			m_states = null;
			m_intersection = null;
		}
		
		/**
		 * This constructor is used for the initialization. 
		 * 
		 * @param states the set of states for the equivalence class
		 */
		public EquivalenceClass(final Set<STATE> states) {
			this(states, false);
			m_incomingInt = EIncomingStatus.inWL;
			m_incomingCall = EIncomingStatus.inWL;
			m_workListIntCall.add(this);
			m_incomingRet = EIncomingStatus.inWL;
			m_workListRet.add(this);
			if (m_firstReturnSplitAlternative) {
				m_outgoingRet = EIncomingStatus.inWL;
				m_workListRetHier.add(this);
			}
			m_matrix = null;
		}
		
		/**
		 * This constructor is used during a split.
		 * 
		 * @param states the set of states for the equivalence class
		 * @param parent the parent equivalence class
		 */
		public EquivalenceClass(final Set<STATE> states,
				final EquivalenceClass parent) {
			this(states, true);
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
			if (m_firstReturnSplitAlternative) {
				switch (parent.m_outgoingRet) {
					case unknown:
					case inWL:
						m_outgoingRet = EIncomingStatus.inWL;
						m_workListRetHier.add(this);
						break;
					case none:
						m_outgoingRet = EIncomingStatus.none;
						break;
				}
			}
			if (m_returnSplitCorrectnessEcs != null) {
				// own predecessors
				for (final STATE state : m_states) {
					for (final IncomingReturnTransition<LETTER, STATE>
							transition : m_operand.returnPredecessors(state)) {
						m_returnSplitCorrectnessEcs.add(
								m_partition.m_state2EquivalenceClass.get(
										transition.getLinPred()));
					}
				}
				// parent predecessors
				for (final STATE state : parent.m_states) {
					for (final IncomingReturnTransition<LETTER, STATE>
							transition : m_operand.returnPredecessors(state)) {
						m_returnSplitCorrectnessEcs.add(
								m_partition.m_state2EquivalenceClass.get(
										transition.getLinPred()));
					}
				}
				// inherit from parent
				if (m_returnSplitCorrectnessEcs.contains(parent)) {
					m_returnSplitCorrectnessEcs.add(this);
				}
			}
			resetMatrix(parent);
		}
		
		@Override
		public int hashCode() {
			return m_id;
		}
		
		/**
		 * This method initializes the matrix. This is not done at the
		 * beginning to avoid creating a huge but sparse matrix, since other
		 * splits can be executed first.
		 * 
		 * @param hierEcs hierarchical predecessor equivalence classes
		 */
		@SuppressWarnings("unchecked")
		public void initializeMatrix(HashSet<EquivalenceClass> hierEcs) {
			if (STATISTICS) {
				m_matrixTime -= new GregorianCalendar().getTimeInMillis();
			}
			
			final Collection<EquivalenceClass> hierEcsUsed;
			
			// ignore singletons
			if (m_states.size() == 1) {
				hierEcsUsed =
						new ArrayList<EquivalenceClass>(hierEcs.size());
				for (final EquivalenceClass hierEc : hierEcs) {
					if (hierEc.m_states.size() > 1) {
						hierEcsUsed.add(hierEc);
					}
				}
			}
			// add all
			else {
				hierEcsUsed = hierEcs;
			}
			final int size = hierEcsUsed.size();
			
			/*
			 * The matrix has only one column and only one-liners for each
			 * hierarchical equivalence class - ignore that.
			 */
			if (size == 0) {
				if (DEBUG2)
					System.err.println("--creating 1x1 dummy matrix");
				
				m_matrix = m_singletonMatrix;
				
				if (STATISTICS) {
					m_matrixTime += new GregorianCalendar().getTimeInMillis();
				}
				return;
			}
			
			m_matrix = new Matrix(size);
			final HashMap<STATE, HashMap<STATE,
				HashMap<LETTER, HashSet<STATE>>>> hier2lin2letter2succ =
				m_matrix.m_hier2lin2letter2succ;
			
			if (DEBUG2)
				System.err.println("--adding entries");
			
			// add entries
			final int mapSize = computeHashSetCapacity(m_states.size());
			
			for (final EquivalenceClass hierEc : hierEcsUsed) {
				for (final STATE hier : hierEc.m_states) {
					final HashMap<STATE, HashMap<LETTER,
						HashSet<STATE>>> lin2letter2succ =
						new HashMap<STATE, HashMap<LETTER,
						HashSet<STATE>>>(mapSize);
					
					if (DEBUG2)
						System.err.println(" consider hier: " + hier);
					
					for (final STATE lin : m_states) {
						if (DEBUG2)
							System.err.println("  and lin: " + lin);
						
						// first check whether hier is a down state
						if (! m_doubleDecker.isDoubleDecker(lin, hier))
								{
							if (DEBUG2)
								System.err.println("  no DS");
							
							continue;
						}
						
						final Iterator<OutgoingReturnTransition
							<LETTER, STATE>> edges = m_operand.
							returnSuccessorsGivenHier(lin, hier).
							iterator();
						if (edges.hasNext()) {
							/*
							 * TODO<nondeterminism> at most one successor
							 *   for deterministic automata, offer improved
							 *   version (no Set<STATE>, no "if" in loop)?
							 */
							final HashMap<LETTER, HashSet<STATE>>
								return2succ = new HashMap<LETTER,
								HashSet<STATE>>();
							lin2letter2succ.put(lin, return2succ);
							do {
								final OutgoingReturnTransition
									<LETTER, STATE> edge = edges.next();
								final LETTER letter = edge.getLetter();
								HashSet<STATE> succs =
										return2succ.get(letter);
								if (succs == null) {
									succs = new HashSet<STATE>();
									return2succ.put(letter, succs);
								}
								succs.add(edge.getSucc());
							} while (edges.hasNext());
							
							if (DEBUG2)
								System.err.println("  transitions: " +
										return2succ);
						}
						else {
							if (DEBUG2)
								System.err.println("  DS");
							
							lin2letter2succ.put(lin, m_downStateMap);
						}
					}
					
					if (lin2letter2succ.size() > 0) {
						hier2lin2letter2succ.put(hier, lin2letter2succ);
					}
				}
				assert (hier2lin2letter2succ.size() > 0);
			}
			if (STATISTICS) {
				m_matrixTime += new GregorianCalendar().getTimeInMillis();
			}
			
			if (DEBUG2)
				System.err.println("--finished creating matrix");
		}
		
		/**
		 * This method checks whether a parent equivalence class (after a
		 * split) had a matrix. If so, the split states are shifted to the
		 * new child equivalence class.
		 * 
		 * TODO<matrix> maybe store known hierarchical states with entries?
		 * 
		 * @param parent parent equivalenceClass class
		 */
		private void resetMatrix(final EquivalenceClass parent) {
			final Matrix oldMatrix = parent.m_matrix;
			if ((oldMatrix == null) || (oldMatrix == m_singletonMatrix)) {
				return;
			}
			
			if (DEBUG2)
				System.err.println("shifting matrix from " +
						parent.toStringShort() + "(" + oldMatrix + ") to " +
						toStringShort());

			final HashMap<STATE, HashMap<STATE, HashMap<LETTER,
				HashSet<STATE>>>> oldHier2lin2letter2succ =
				oldMatrix.m_hier2lin2letter2succ;
			final LinkedList<STATE> removeHiers = new LinkedList<STATE>();
			final Set<STATE> states = m_states;
			m_matrix = new Matrix(
					oldHier2lin2letter2succ.size());
			final HashMap<STATE, HashMap<STATE, HashMap<LETTER,
					HashSet<STATE>>>> hier2lin2letter2succ =
					m_matrix.m_hier2lin2letter2succ;
			for (final Entry<STATE, HashMap<STATE, HashMap<LETTER,
					HashSet<STATE>>>> outerEntry :
					oldHier2lin2letter2succ.entrySet()) {
				final HashMap<STATE, HashMap<LETTER, HashSet<STATE>>>
						oldLin2letter2succ = outerEntry.getValue();
				final Iterator<Entry<STATE, HashMap<LETTER, HashSet<STATE>>>>
						it = oldLin2letter2succ.entrySet().iterator();
				final LinkedList<STATE> removeLins = new LinkedList<STATE>();
				while (it.hasNext()) {
					Entry<STATE, HashMap<LETTER, HashSet<STATE>>>
							innerEntry = it.next();
					STATE lin = innerEntry.getKey();
					if (states.contains(lin)) {
						final HashMap<STATE, HashMap<LETTER, HashSet<STATE>>>
							newLin2letter2succ = new HashMap<STATE,
							HashMap<LETTER,HashSet<STATE>>>(
							computeHashSetCapacity(
							oldLin2letter2succ.size()));
						newLin2letter2succ.put(lin, innerEntry.getValue());
						removeLins.add(lin);
						
						while (it.hasNext()) {
							innerEntry = it.next();
							lin = innerEntry.getKey();
							if (states.contains(lin)) {
								newLin2letter2succ.put(lin,
										innerEntry.getValue());
								removeLins.add(lin);
							}
						}
						
						final STATE hier = outerEntry.getKey();
						hier2lin2letter2succ.put(
								hier, newLin2letter2succ);
						if (oldLin2letter2succ.size() == 0) {
							removeHiers.add(hier);
						}
						break;
					}
				}
				for (final STATE lin : removeLins) {
					oldLin2letter2succ.remove(lin);
					if (oldHier2lin2letter2succ.size() == 0) {
						/*
						 * can result in the state being twice in the list,
						 * but this is acceptable
						 */
						removeHiers.add(outerEntry.getKey());
					}
				}
			}
			
			for (final STATE hier : removeHiers) {
				oldHier2lin2letter2succ.remove(hier);
			}
			
			if (oldHier2lin2letter2succ.size() <= 1) {
				if (oldHier2lin2letter2succ.size() == 0) {
					parent.m_matrix = null;
				}
				else if (parent.m_states.size() - m_states.size() == 1) {
					parent.m_matrix = m_singletonMatrix;
				}
			}
			
			if (hier2lin2letter2succ.size() <= 1) {
				if (hier2lin2letter2succ.size() == 0) {
					m_matrix = null;
				}
				else if (m_states.size() == 1) {
					m_matrix = m_singletonMatrix;
				}
			}
			
			if (DEBUG2)
				System.err.println("resulting in matrices: parent: " +
						parent.m_matrix + ", child: " +
						m_matrix);
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
				m_splitEcsReturn.add(this);
			}
			else {
				assert (m_splitEcsReturn.contains(this));
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
			if (DEBUG2)
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
			
			if (!DEBUG && (DEBUG2 || DEBUG3 || DEBUG4)) {
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
			if (m_firstReturnSplitAlternative) {
				builder.append(",");
				builder.append(m_outgoingRet);
			}
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
		
		/**
		 * This method fills the queue with all equivalence classes so far.
		 * It is used exactly once when the first return split has finished.
		 */
		public void fillWithAll() {
			for (final EquivalenceClass ec :
					m_partition.m_equivalenceClasses) {
				if (ec.m_incomingRet != EIncomingStatus.none) {
					ec.m_incomingRet = EIncomingStatus.inWL;
					m_queue.add(ec);
				}
			}
		}
	}
	
	/**
	 * This class implements the work list for predecessor return splits.
	 */
	private class WorkListRetHier extends AWorkList {
		@Override
		public EquivalenceClass next() {
			final EquivalenceClass ec = m_queue.poll();
			ec.m_outgoingRet = EIncomingStatus.unknown;
			if (DEBUG)
				System.out.println("\npopping from return hier WL: " + ec);
			return ec;
		}
		
		@Override
		public void add(final EquivalenceClass ec) {
			assert (ec.m_outgoingRet == EIncomingStatus.inWL);
			if (DEBUG)
				System.out.println("adding of return hier WL: " + ec);
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