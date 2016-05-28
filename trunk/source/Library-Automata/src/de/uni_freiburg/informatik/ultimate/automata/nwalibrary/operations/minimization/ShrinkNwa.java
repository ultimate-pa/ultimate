/*
 * Copyright (C) 2013-2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Christian Schilling <schillic@informatik.uni-freiburg.de>
 * Copyright (C) 2009-2015 University of Freiburg
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
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.util.IBlock;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.util.IPartition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;

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
public class ShrinkNwa<LETTER, STATE> extends AMinimizeNwa<LETTER, STATE>  
										implements IOperation<LETTER,STATE> {
	// old automaton
	private IDoubleDeckerAutomaton<LETTER, STATE> mDoubleDecker;
	// partition object
	private Partition mPartition;
	// IDs for equivalence classes
	private int mIds;
	// work lists
	private WorkListIntCall mWorkListIntCall;
	private WorkListRet mWorkListRet;
	private WorkListRetHier mWorkListRetHier;
	// placeholder equivalence class
	private final HashSet<EquivalenceClass> mNegativeSet;
	private final EquivalenceClass mNegativeClass;
	private final Matrix mSingletonMatrix;
	private final DummyMap mDownStateMap;
	// storage for split equivalence classes
	private List<EquivalenceClass> mSplitEcsReturn;
	// initial outgoing split (internal and call)
	private final boolean mSplitOutgoing;
	private final OutgoingHelperInternal mOutInternal;
	private final OutgoingHelperCall mOutCall;
	// output automaton
	private final NestedWordAutomaton<LETTER, STATE> mResult;
	// map old state -> new state
	private final Map<STATE, STATE> mOldState2newState;
	
	/* optional random splits before the return split to keep matrices small */
	// true iff before the first return split some random splits are executed
	private boolean mRandomReturnSplit;
	// maximum size of equivalence classes with outgoing calls/returns
	private final int THRESHOLD;
	
	// true iff first return split is not finished yet
	private boolean mFirstReturnSplit;
	// map for first return split (open check)
	private HashMap<EquivalenceClass, HashSet<STATE>> mFirstReturnLin2hiers;
	
	// temporarily activate alternative return split before the first run
	private boolean mFirstReturnSplitAlternative;
	// also do the hierarchical split without a matrix
	private boolean mFirstReturnSplitHierAlternative;
	
	/* split all call predecessors to avoid one dimension in the matrix */
	private boolean mSplitAllCallPreds;
	
	/* naive return split (needs another split for correctness) */
	private boolean mReturnSplitNaive;
	private HashSet<EquivalenceClass> mReturnSplitCorrectnessEcs;
	
	// TODO<debug>
	private final boolean DEBUG = false; // general output
	private final boolean DEBUG2 = false; // general return split
	private final boolean DEBUG3 = false; // first return split
	private final boolean DEBUG4 = false; // naive return split
	
	// TODO<statistics>
	private final boolean STATISTICS = false;
	private int mSplitsWithChange = 0;
	private int mSplitsWithoutChange = 0;
	private int mIncomingTransitions = 0;
	private int mNoIncomingTransitions = 0;
	private int mIgnoredReturnSingletons1x1 = 0;
	private long mReturnTime = 0, mMatrixTime = 0, mWholeTime = 0;
	private long mReturnSeparateTime = 0;
	private long mReturnFirstTime = 0;
	private long mReturnFirstTimeAlternative = 0;
	private long mReturnFirstTimeHierAlternative = 0;
	 // size information before return splits
	private final boolean STAT_RETURN_SIZE = false;
	private final BufferedWriter mWriter1, mWriter2;
	
	/**
	 * StateFactory used for the construction of new states. This is _NOT_ the
	 * state factory relayed to the new automaton.
	 * Necessary because the Automizer needs a special StateFactory during
	 * abstraction refinement (for computation of HoareAnnotation).
	 */
	private final StateFactory<STATE> mstateFactory;
	
	/**
	 * This constructor creates a copy of the operand.
	 * 
	 * @param operand preprocessed nested word automaton
	 * preprocessing: dead end and unreachable states/transitions removed
	 * @throws AutomataOperationCanceledException if cancel signal is received
	 */
	public ShrinkNwa(final AutomataLibraryServices services,
			final StateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER,STATE> operand)
			throws AutomataLibraryException {
		this(services, stateFactory, operand, false, 0, false, 0, false, false);
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
	 * @throws AutomataOperationCanceledException if cancel signal is received
	 */
	public ShrinkNwa(final AutomataLibraryServices services,
			final StateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER,STATE> operand,
			final boolean splitOutgoing, final int splitRandomSize,
			final boolean firstReturnSplit,
			final int firstReturnSplitAlternative,
			final boolean splitAllCallPreds, final boolean returnSplitNaive)
			throws AutomataLibraryException {
		this(services, stateFactory, operand, null, false, false, splitOutgoing,
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
	 * @throws AutomataOperationCanceledException if cancel signal is received
	 */
	public ShrinkNwa(
			final AutomataLibraryServices services,
			final StateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER,STATE> operand,
			final Collection<Set<STATE>> equivalenceClasses,
			final boolean includeMapping, final boolean isFiniteAutomaton,
			final boolean splitOutgoing, final int splitRandomSize,
			final boolean firstReturnSplit,
			final int firstReturnSplitAlternative,
			final boolean splitAllCallPreds, final boolean returnSplitNaive)
					throws AutomataLibraryException {
		super(services, stateFactory, "shrinkNwa", operand);
		if (STAT_RETURN_SIZE) {
			try {
				mWriter1 = new BufferedWriter(
						new FileWriter(new File("DEBUG-1.txt")));
				mWriter2 = new BufferedWriter(
						new FileWriter(new File("DEBUG-2.txt")));
			} catch (final IOException e) {
				throw new RuntimeException(e);
			}
		}
		else {
			mWriter1 = null;
			mWriter2 = null;
		}
		
		if (mOperand instanceof IDoubleDeckerAutomaton) {
			mDoubleDecker = (IDoubleDeckerAutomaton<LETTER, STATE>)mOperand;
		} else {
			mDoubleDecker = null;
		}
		mstateFactory = (stateFactory == null)
				? mOperand.getStateFactory()
				: stateFactory;
		mPartition = new Partition();
		mIds = 0;
		mWorkListIntCall = new WorkListIntCall();
		mWorkListRet = new WorkListRet();
		mSplitEcsReturn = new LinkedList<EquivalenceClass>();
		mNegativeSet = new HashSet<EquivalenceClass>();
		mNegativeClass = new EquivalenceClass();
		mNegativeSet.add(mNegativeClass);
		mSingletonMatrix = new Matrix();
		mDownStateMap = new DummyMap();
		
		/* options */
		mSplitOutgoing = splitOutgoing;
		if (mSplitOutgoing) {
			mOutInternal = new OutgoingHelperInternal();
			mOutCall = new OutgoingHelperCall();
		}
		else {
			mOutInternal = null;
			mOutCall = null;
		}
		
		THRESHOLD = splitRandomSize;
		mRandomReturnSplit = (splitRandomSize > 0);
		
		mFirstReturnSplit = firstReturnSplit;
		mFirstReturnLin2hiers = (mFirstReturnSplit
				? new HashMap<EquivalenceClass, HashSet<STATE>>(2)
				: null);
		
		switch (firstReturnSplitAlternative) {
			case 0:
				mFirstReturnSplitAlternative = false;
				mFirstReturnSplitHierAlternative = false;
				break;
			case 1:
				mFirstReturnSplitAlternative = true;
				mFirstReturnSplitHierAlternative = false;
				break;
			case 2:
				mFirstReturnSplitAlternative = true;
				mFirstReturnSplitHierAlternative = true;
				break;
			default:
				throw new IllegalArgumentException(
						"firstReturnSplitAlternative must be one of 0, 1, 2.");
		}
		if (mFirstReturnSplitAlternative) {
			mWorkListRetHier = new WorkListRetHier();
		}
		
		mSplitAllCallPreds = splitAllCallPreds;
		
		mReturnSplitNaive = returnSplitNaive;
		if (mReturnSplitNaive) {
			mReturnSplitCorrectnessEcs = new HashSet<EquivalenceClass>();
		}
		
		// must be the last part of the constructor
		mLogger.info(startMessage());
		minimize(isFiniteAutomaton, equivalenceClasses, includeMapping);
		final QuotientNwaConstructor<LETTER, STATE> quotientNwaConstructor =
				constructAutomaton(includeMapping);
		mResult = quotientNwaConstructor.getResult();
		mOldState2newState = (includeMapping
				? quotientNwaConstructor.getOldState2newState()
				: null);
		
		mLogger.info(exitMessage());
		
		if (STATISTICS) {
			mWholeTime += new GregorianCalendar().getTimeInMillis();
			
			System.out.println("positive splits: " + mSplitsWithChange);
			System.out.println("negative splits: " + mSplitsWithoutChange);
			System.out.println("quota (p/n): " + (mSplitsWithoutChange == 0
					? "--"
					: (((float)mSplitsWithChange) /
							((float)mSplitsWithoutChange))));
			System.out.println("incoming transition checks : " +
					mIncomingTransitions);
			System.out.println("no incoming transitions found : " +
					mNoIncomingTransitions);
			System.out.println("quota (p/n): " + (mNoIncomingTransitions == 0
					? "--"
					: (((float)mIncomingTransitions) /
							((float)mNoIncomingTransitions))));
			System.out.println("ignored return splits due to singletons: " +
					mIgnoredReturnSingletons1x1);
			System.out.println("time consumption (ms): return separation: " +
					mReturnSeparateTime + ", matrix time: " +
					mMatrixTime + ", first return split: " +
					mReturnFirstTime + ", alternative lin " +
					mReturnFirstTimeAlternative + ", alternative hier " +
					mReturnFirstTimeHierAlternative + ", returns: " +
					mReturnTime + ", all: " + mWholeTime);
			System.out.println("quota (ret/all): " + (mWholeTime == 0
					? "--"
					: (((float)mReturnTime) / ((float)mWholeTime))) +
						", without: " + (mWholeTime - mReturnTime) + " ms");
			System.out.println("quota (mat/ret): " + (mReturnTime == 0
					? "--"
					: (((float)mMatrixTime) / ((float)mReturnTime))) +
						", without: " + (mReturnTime - mMatrixTime) + " ms");
			System.out.println("quota (mat/all): " + (mWholeTime == 0
					? "--"
					: (((float)mMatrixTime) / ((float)mWholeTime))) +
						", without: " + (mWholeTime - mMatrixTime) + " ms");
			System.out.println("quota (first/all): " + (mWholeTime == 0
					? "--"
					: (((float)mReturnFirstTime) / ((float)mWholeTime))) +
						", without: " + (mWholeTime - mReturnFirstTime) +
						" ms");
			System.out.println("quota (altLin/all): " + (mWholeTime == 0
					? "--"
					: (((float)mReturnFirstTimeAlternative) /
							((float)mWholeTime))) +
						", without: " +
						(mWholeTime - mReturnFirstTimeAlternative) + " ms");
			System.out.println("quota (altHier/all): " + (mWholeTime == 0
					? "--"
					: (((float)mReturnFirstTimeHierAlternative) /
							((float)mWholeTime))) +
						", without: " +
						(mWholeTime - mReturnFirstTimeHierAlternative) +
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
	 * @throws AutomataOperationCanceledException if cancel signal is received
	 */
	private void minimize(final boolean isFiniteAutomaton,
			final Iterable<Set<STATE>> modules, final boolean includeMapping)
			throws AutomataLibraryException {
		if (STATISTICS) {
			mWholeTime -= new GregorianCalendar().getTimeInMillis();
		}
		
		if (DEBUG) {
			System.err.println("---------------START---------------");
		}
		// initialize the partition object
		initialize(modules);
		
		final InternalTransitionIterator internalIterator =
				new InternalTransitionIterator();
		
		// for DFAs only the internal split is both necessary and sufficient
		if (isFiniteAutomaton) {
			// iterative refinement
			while (mWorkListIntCall.hasNext()) {
				// cancel if signal is received
				if (!mServices.getProgressMonitorService().continueProcessing()) {
					throw new AutomataOperationCanceledException(this.getClass());
				}
				
				final EquivalenceClass a = mWorkListIntCall.next();
				
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
				if (!mServices.getProgressMonitorService().continueProcessing()) {
					throw new AutomataOperationCanceledException(this.getClass());
				}
				
				// internals and calls
				while (mWorkListIntCall.hasNext()) {
					// cancel if signal is received
					if (!mServices.getProgressMonitorService().continueProcessing())
							{
						throw new AutomataOperationCanceledException(this.getClass());
					}
					
					final EquivalenceClass a = mWorkListIntCall.next();
					
					// internal split
					if (a.mincomingInt == EIncomingStatus.inWL) {
						a.mincomingInt = EIncomingStatus.unknown;
						if (DEBUG) {
							System.out.println("\n-- internal search");
						}
						splitInternalOrCallPredecessors(a, internalIterator,
								true);
					}
					
					// call split
					if (a.mincomingCall == EIncomingStatus.inWL) {
						a.mincomingCall = EIncomingStatus.unknown;
						if (DEBUG) {
							System.out.println("\n-- call search");
						}
						if (! mSplitAllCallPreds) {
							splitInternalOrCallPredecessors(a, callIterator,
									false);
						}
					}
				}
				
				// return predecessors
				if (mWorkListRet.hasNext()) {
					
					// optional random split
					if (mRandomReturnSplit) {
						mRandomReturnSplit = false;
						final LinkedList<EquivalenceClass> bigEcs =
								new LinkedList<EquivalenceClass>();
						for (final EquivalenceClass ec :
								mPartition.mequivalenceClasses) {
							if (ec.mstates.size() > THRESHOLD) {
								bigEcs.add(ec);
							}
						}
						for (final EquivalenceClass ec : bigEcs) {
							splitRandom(ec);
						}
						continue outer;
					}
					
					if (STATISTICS) {
						mReturnTime -=
								new GregorianCalendar().getTimeInMillis();
					}
					
					if (STAT_RETURN_SIZE) {
						try {
							final GregorianCalendar date = new GregorianCalendar();
							mWriter1.append(
									date.get(GregorianCalendar.MINUTE) + ":" +
									date.get(GregorianCalendar.SECOND) + ":" +
									date.get(GregorianCalendar.MILLISECOND) +
									" (min:sec:ms)\n");
							mWriter1.append(
									mPartition.mequivalenceClasses.size() +
									" ECs before return split of " +
									mWorkListRet.mqueue.size() + " ECs\n");
							final int[] sizes =
									new int[mWorkListRet.mqueue.size()];
							mWriter2.append("\n\nnew round with " +
									sizes.length + " ECs");
							
							int i = -1;
							for (final EquivalenceClass ec :
									mWorkListRet.mqueue) {
								sizes[++i] = ec.mstates.size();
							}
							Arrays.sort(sizes);
							for (i = 0; i < sizes.length; ++i) {
								if (i % 15 == 0) {
									mWriter2.append("\n");
								}
								mWriter2.append(sizes[i] + ", ");
							}
						} catch (final IOException e) {
							throw new RuntimeException(e);
						}
					}
					
					// optional first linear split
					if (mFirstReturnSplit) {
						splitReturnPredecessorsFirstTime();
					}
					else {
						if (mFirstReturnSplitAlternative) {
							mReturnFirstTimeAlternative -=
									new GregorianCalendar().getTimeInMillis();
							splitReturnLinearAlt();
							mReturnFirstTimeAlternative +=
									new GregorianCalendar().getTimeInMillis();
						}
						else if (mReturnSplitNaive) {
							splitReturnNaiveHierarchicalStates(
									mWorkListRet.next());
						}
						else {
							splitReturnPredecessors();
						}
					}
					
					if (STATISTICS) {
						mReturnTime +=
								new GregorianCalendar().getTimeInMillis();
					}
					
					if (STAT_RETURN_SIZE) {
						try {
							final GregorianCalendar date = new GregorianCalendar();
							mWriter1.append(
									date.get(GregorianCalendar.MINUTE) + ":" +
									date.get(GregorianCalendar.SECOND) + ":" +
									date.get(GregorianCalendar.MILLISECOND) +
									" (min:sec:ms)\n");
							mWriter1.append(
									mPartition.mequivalenceClasses.size() +
									" ECs after return split\n");
						} catch (final IOException e) {
							throw new RuntimeException(e);
						}
					}
				}
				else {
					if (mFirstReturnSplitAlternative) {
						if (mFirstReturnSplitHierAlternative) {
							if (DEBUG4) {
								System.err.println("hierarchical split");
							}
							
							if (mWorkListRetHier.hasNext()) {
								mReturnFirstTimeHierAlternative -=
										new GregorianCalendar().
										getTimeInMillis();
								splitReturnHierAlt();
								mReturnFirstTimeHierAlternative +=
										new GregorianCalendar().
										getTimeInMillis();
								continue outer;
							}
							else {
								break outer;
							}
						}
						else {
							if (DEBUG4) {
								System.err.println("ALTERNATIVE FINISHED");
							}
							
							mFirstReturnSplitAlternative = false;
							mWorkListRet.fillWithAll();
							continue outer;
						}
					}
					else if ((mReturnSplitCorrectnessEcs != null) &&
							(! mReturnSplitCorrectnessEcs.isEmpty())) {
						final Iterator<EquivalenceClass> iterator =
								mReturnSplitCorrectnessEcs.iterator();
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
					mWriter1.close();
					mWriter2.close();
				} catch (final IOException eWriter) {
					eWriter.printStackTrace();
				}
			}
		}
		if (DEBUG) {
			System.err.println("----------------END----------------");
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
	private void splitReturnNaiveHierarchicalEcs(final EquivalenceClass a) {
		// create a hash map from letter to respective predecessor states
		final HashMap<LETTER, HashMap<EquivalenceClass, HashSet<STATE>>>
				letter2hierEc2lin = new HashMap<LETTER,
				HashMap<EquivalenceClass, HashSet<STATE>>>();
		for (final STATE state : a.mstates) {
			final Iterator<IncomingReturnTransition<LETTER, STATE>> transitions
					= mOperand.returnPredecessors(state).iterator();
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
				final EquivalenceClass hierEc = mPartition.
						mstate2EquivalenceClass.get(
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
			a.mincomingRet = EIncomingStatus.none;
			if (STATISTICS) {
				++mNoIncomingTransitions;
			}
		}
		else {
			if (STATISTICS) {
				++mIncomingTransitions;
			}
			
			// split each map value (set of predecessor states)
			for (final HashMap<EquivalenceClass, HashSet<STATE>> hierEc2lin :
					letter2hierEc2lin.values()) {
				for (final HashSet<STATE> lins : hierEc2lin.values()) {
					assert (! lins.isEmpty());
					mPartition.splitEquivalenceClasses(lins);
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
		for (final STATE state : a.mstates) {
			final Iterator<IncomingReturnTransition<LETTER, STATE>> transitions =
					mOperand.returnPredecessors(state).iterator();
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
			a.mincomingRet = EIncomingStatus.none;
			if (STATISTICS) {
				++mNoIncomingTransitions;
			}
		}
		else {
			if (STATISTICS) {
				++mIncomingTransitions;
			}
			
			// split each map value (set of predecessor states)
			for (final HashMap<STATE, HashSet<STATE>> hier2lin :
					letter2hier2lin.values()) {
				for (final HashSet<STATE> lins : hier2lin.values()) {
					assert (! lins.isEmpty());
					mPartition.splitEquivalenceClasses(lins);
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
		for (final STATE state : a.mstates) {
			final Iterator<IncomingReturnTransition<LETTER, STATE>> transitions =
					mOperand.returnPredecessors(state).iterator();
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
			a.mincomingRet = EIncomingStatus.none;
			if (STATISTICS) {
				++mNoIncomingTransitions;
			}
		}
		else {
			if (STATISTICS) {
				++mIncomingTransitions;
			}
			
			// split each map value (set of predecessor states)
			for (final HashSet<STATE> predecessorSet :
					letter2states.values()) {
				assert (! predecessorSet.isEmpty());
				mPartition.splitEquivalenceClasses(predecessorSet);
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
		if (DEBUG2) {
			System.err.println("\nNEW CORRECTNESS RETURN SPLITTING");
		}
		
		final HashMap<STATE, HashSet<STATE>> lin2hier =
				new HashMap<STATE, HashSet<STATE>>();
		for (final STATE lin : linEc.mstates) {
			final HashSet<STATE> hiers = new HashSet<STATE>();
			final Iterator<OutgoingReturnTransition<LETTER, STATE>>
				transitions = mOperand.returnSuccessors(lin).iterator();
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
		
		while (mSplitEcsReturn.size() > 0) {
			assert (assertSetProperty(mSplitEcsReturn));
			splitReturnExecute(mSplitEcsReturn);
			linEc2hierEc = splitReturnEcTranslation(lin2hier);
			mSplitEcsReturn = new LinkedList<EquivalenceClass>();
			splitReturnForwardsAnalysis(linEc2hierEc, true);
		}
		
		splitReturnForwardsAnalysis(linEc2hierEc, false);
		
		if (mSplitEcsReturn.size() > 0) {
			assert (assertSetProperty(mSplitEcsReturn));
			splitReturnExecute(mSplitEcsReturn);
			mSplitEcsReturn = new LinkedList<EquivalenceClass>();
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
		if (DEBUG2) {
			System.err.println("\nNEW CORRECTNESS RETURN SPLITTING");
		}
		
		final HashMap<STATE, HashSet<STATE>> lin2hier =
				new HashMap<STATE, HashSet<STATE>>();
		for (final STATE lin : linEc.mstates) {
			final HashSet<STATE> hiers = new HashSet<STATE>();
			final Iterator<OutgoingReturnTransition<LETTER, STATE>>
				transitions = mOperand.returnSuccessors(lin).iterator();
			if (transitions.hasNext()) {
				do {
					hiers.add(transitions.next().getHierPred());
				} while (transitions.hasNext());
				lin2hier.put(lin, hiers);
			}
		}
		
		final HashMap<EquivalenceClass, HashSet<EquivalenceClass>>
				linEc2hierEc = splitReturnEcTranslation(lin2hier);
		
		splitReturnForwardsAnalysis(linEc2hierEc, false);
		
		if (mSplitEcsReturn.size() > 0) {
			assert (assertSetProperty(mSplitEcsReturn));
			splitReturnExecute(mSplitEcsReturn);
			mSplitEcsReturn = new LinkedList<EquivalenceClass>();
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
		if (DEBUG2) {
			System.err.println("\nNEW CORRECTNESS RETURN SPLITTING");
		}
		
		// find all hierarchical predecessor equivalence classes
		final HashSet<EquivalenceClass> hierEcs =
				new HashSet<EquivalenceClass>();
		for (final STATE lin : linEc.mstates) {
			final Iterator<IncomingReturnTransition<LETTER, STATE>> transitions
					= mOperand.returnPredecessors(lin).iterator();
			while (transitions.hasNext()) {
				hierEcs.add(mPartition.mstate2EquivalenceClass.get(
						transitions.next().getHierPred()));
			}
		}
		
		// linear split
		for (final EquivalenceClass hierEc : hierEcs) {
			for (final STATE hier : hierEc.mstates) {
				final HashMap<LETTER, HashMap<EquivalenceClass,
						HashSet<STATE>>> letter2succEc2lins = new
						HashMap<LETTER, HashMap<EquivalenceClass,
						HashSet<STATE>>>();
				for (final STATE lin : linEc.mstates) {
					if (! mDoubleDecker.isDoubleDecker(lin, hier)) {
						continue;
					}
					final Iterator<OutgoingReturnTransition<LETTER, STATE>>
						transitions = mOperand.returnSuccessorsGivenHier(
								lin, hier).iterator();
					final HashMap<EquivalenceClass, HashSet<STATE>> succEc2lins
						= new HashMap<EquivalenceClass, HashSet<STATE>>();
					if (transitions.hasNext()) {
						do {
							final OutgoingReturnTransition<LETTER, STATE>
								transition = transitions.next();
							final EquivalenceClass succEc = mPartition.
									mstate2EquivalenceClass.get(
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
						HashSet<STATE> lins = succEc2lins.get(mNegativeClass);
						if (lins == null) {
							lins = new HashSet<STATE>();
							succEc2lins.put(mNegativeClass, lins);
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
				if (mSplitEcsReturn.size() > 0) {
					splitReturnExecute(mSplitEcsReturn);
					mSplitEcsReturn = new LinkedList<EquivalenceClass>();
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
			
			for (final STATE state : mOperand.getStates()) {
				if (mSplitAllCallPreds && (mOperand.callSuccessors(state).
							iterator().hasNext())) {
					mPartition.addEcInitialization(
							Collections.singleton(state));
				}
				else if (mOperand.isFinal(state)) {
					finals.add(state);
				}
				else {
					nonfinals.add(state);
				}
			}
			
			if (mSplitOutgoing) {
				splitOutgoing(finals, nonfinals);
			}
			// only separate final and non-final states
			else {
				if (finals.size() > 0) {
					mPartition.addEcInitialization(finals);
				}
				if (nonfinals.size() > 0) {
					mPartition.addEcInitialization(nonfinals);
				}
			}
		}
		// predefined modules are already split with respect to final states 
		else {
			assert assertStatesSeparation(modules) :
				"The states in the initial modules are not separated with " +
				"respect to their final status.";
			for (final Set<STATE> module : modules) {
				mPartition.addEcInitialization(module);
			}
		}
		
		if (mSplitAllCallPreds) {
			for (final EquivalenceClass ec :
					mPartition.mequivalenceClasses) {
				ec.mincomingCall= EIncomingStatus.none; 
			}
		}
		
		if (mReturnSplitCorrectnessEcs != null) {
			mReturnSplitCorrectnessEcs.addAll(
					mPartition.mequivalenceClasses);
		}
		
		if (DEBUG) {
			System.err.println("starting with " +
					mPartition.mequivalenceClasses.size() +
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
				(a.mincomingInt != EIncomingStatus.inWL)) ||
				(! isInternal) &&
				((iterator instanceof ShrinkNwa.CallTransitionIterator) &&
				(a.mincomingCall != EIncomingStatus.inWL)));
		
		// create a hash map from letter to respective predecessor states
		final HashMap<LETTER, HashSet<STATE>> letter2states =
				new HashMap<LETTER, HashSet<STATE>>();
		for (final STATE state : a.mstates) {
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
				a.mincomingInt = EIncomingStatus.none;
			}
			else {
				a.mincomingCall = EIncomingStatus.none;
			}
			if (STATISTICS) {
				++mNoIncomingTransitions;
			}
		}
		else {
			if (STATISTICS) {
				++mIncomingTransitions;
			}
			
			// split each map value (set of predecessor states)
			for (final HashSet<STATE> predecessorSet :
					letter2states.values()) {
				assert (! predecessorSet.isEmpty());
				mPartition.splitEquivalenceClasses(predecessorSet);
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
		if (DEBUG2) {
			System.err.println("\nNEW RETURN SPLITTING ROUND");
		}
		
		final HashMap<STATE, HashSet<STATE>> lin2hier =
				splitReturnBackwardsAnalysis();
		
		HashMap<EquivalenceClass, HashSet<EquivalenceClass>>
				linEc2hierEc =
				splitReturnEcTranslation(lin2hier);
		
		splitReturnForwardsAnalysis(linEc2hierEc, true);
		
		while (mSplitEcsReturn.size() > 0) {
			assert (assertSetProperty(mSplitEcsReturn));
			splitReturnExecute(mSplitEcsReturn);
			linEc2hierEc = splitReturnEcTranslation(lin2hier);
			mSplitEcsReturn = new LinkedList<EquivalenceClass>();
			splitReturnForwardsAnalysis(linEc2hierEc, true);
		}
		
		splitReturnForwardsAnalysis(linEc2hierEc, false);
		
		if (mSplitEcsReturn.size() > 0) {
			assert (assertSetProperty(mSplitEcsReturn));
			splitReturnExecute(mSplitEcsReturn);
			mSplitEcsReturn = new LinkedList<EquivalenceClass>();
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
		if (DEBUG2) {
			System.err.println("analyzing backwards");
		}
		final HashMap<STATE, HashSet<STATE>> lin2hier =
				new HashMap<STATE, HashSet<STATE>>(computeHashSetCapacity(
						mPartition.mequivalenceClasses.size()));
		
		// find all involved linear and hierarchical states
		while (mWorkListRet.hasNext()) {
			final EquivalenceClass succEc = mWorkListRet.next();
			boolean incomingReturns = false;
			
			for (final STATE succ : succEc.mstates) {
				final Iterator<IncomingReturnTransition<LETTER, STATE>> edges =
						mOperand.returnPredecessors(succ).iterator();
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
				succEc.mincomingRet = EIncomingStatus.none;
				if (STATISTICS) {
					++mNoIncomingTransitions;
				}
			}
			
			if (DEBUG2) {
				System.err.println(" succEc: " + succEc.toStringShort() +
						" has " + (incomingReturns ? "" : "no ") + "returns");
			}
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
		if (DEBUG2) {
			System.err.println("\ntranslating to ECs");
		}
		
		final HashMap<EquivalenceClass, HashSet<EquivalenceClass>>
			linEc2hierEcs = new HashMap<EquivalenceClass,
			HashSet<EquivalenceClass>>(computeHashSetCapacity(
					lin2hier.size()));
		for (final Entry<STATE, HashSet<STATE>> entry : lin2hier.entrySet()) {
			final EquivalenceClass linEc =
					mPartition.mstate2EquivalenceClass.get(entry.getKey());
			HashSet<EquivalenceClass> hierEcs = linEc2hierEcs.get(linEc);
			if (hierEcs == null) {
				hierEcs = new HashSet<EquivalenceClass>();
				linEc2hierEcs.put(linEc, hierEcs);
			}
			for (final STATE hier : entry.getValue()) {
				hierEcs.add(mPartition.mstate2EquivalenceClass.get(hier));
			}
		}
		
		if (DEBUG2) {
			System.err.println("resulting map: " + linEc2hierEcs);
		}
		
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
			final boolean linEcSingleton = linEc.mstates.size() == 1;
			final HashSet<EquivalenceClass> hierEcs = entry.getValue();
			
			if (DEBUG2) {
				System.err.println("\nlinEc: " + linEc.toStringShort());
			}
			
			// get matrix
			Matrix matrix = linEc.mmatrix;
			if (matrix == null) {
				linEc.initializeMatrix(hierEcs);
				matrix = linEc.mmatrix;
			}
			if (matrix == mSingletonMatrix) {
				if (DEBUG2) {
					System.err.println(" ignoring matrix: " + matrix);
				}
				
				continue;
			}
			
			if (DEBUG2) {
				System.err.println("matrix: " + matrix);
			}
			
			final HashMap<STATE, HashMap<STATE, HashMap<LETTER,
				HashSet<STATE>>>> hier2lin2letter2succ =
				matrix.mhier2lin2letter2succ;
			
			for (final EquivalenceClass hierEc : hierEcs) {
				if (DEBUG2) {
					System.err.println(" hierEc: " + hierEc.toStringShort());
				}
				
				if (linEcSingleton && hierEc.mstates.size() == 1) {
					if (DEBUG2) {
						System.err.println("  ignoring singletons");
					}
					
					if (STATISTICS) {
						++mIgnoredReturnSingletons1x1;
					}
					
					continue;
				}
				
				/*
				 * find relevant rows
				 * (avoids duplicate computations for the hierarchical split)
				 */
				final ArrayList<MatrixRow> relevantRows =
					new ArrayList<MatrixRow>(hierEc.mstates.size());
				for (final STATE hier : hierEc.mstates) {
					final HashMap<STATE, HashMap<LETTER, HashSet<STATE>>> map =
							hier2lin2letter2succ.get(hier);
					if ((map != null) && (map.size() > 0)) {
						relevantRows.add(new MatrixRow(hier, map));
					}
					else {
						if (DEBUG2) {
							System.err.println(" ignoring hier " + hier);
						}
					}
				}
				
				if (DEBUG2) {
					System.err.println(" relevant rows: " + relevantRows);
				}
				
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
		if (DEBUG2) {
			System.err.println("-linear analysis");
		}
		
		for (final MatrixRow row : rows) {
			final HashMap<STATE, HashMap<LETTER, HashSet<STATE>>>
				lin2letter2succ = row.mlin2letter2succ;
			if (DEBUG2) {
				System.err.println(" hier " + row.mhier + " -> " +
						lin2letter2succ);
			}
			
			if (lin2letter2succ.size() == 1) {
				if (DEBUG2) {
					System.err.println("  only one entry, ignore");
				}
				
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
				assert (linEc.mstates.contains(lin));
				final HashMap<LETTER, HashSet<STATE>> letter2succ =
						entry.getValue();
				
				if (DEBUG2) {
					System.err.println("   lin: " + lin);
				}
				
				if (letter2succ == mDownStateMap) {
					if (DEBUG2) {
						System.err.println("   no transition, but DS");
					}
					
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
					
					if (DEBUG2) {
						System.err.println("   letter: " + letter +
								", succs: " + succs);
					}
					
					for (final STATE succ : succs) {
						succEcs.add(mPartition.mstate2EquivalenceClass.
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
				
				if (DEBUG2) {
					System.err.println("   adding: " + lin + " to " +
							letter2succEc);
				}
			}
			
			if (DEBUG2) {
				System.err.println("    receiving: " + letter2succEc2lin +
						" and {{DS}=" + noTransitions + "}");
			}
			
			if (noTransitions.size() > 0) {
				letter2succEc2lin.put(null, noTransitions);
			}
			
			if (letter2succEc2lin.size() <= 1) {
				if (DEBUG2) {
					System.err.println("    no linear split");
				}
			}
			else {
				if (DEBUG2) {
					System.err.println("    mark linear split of " +
							linEc.toStringShort() + ": " +
							letter2succEc2lin.values());
				}
				
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
		if (DEBUG2) {
			System.err.println("-hierarchical analysis");
		}
		
		final int size = rows.size();
		
		if (DEBUG2) {
			System.err.println("  rows remaining: " + size);
		}
		
		if (size <= 1) {
			if (DEBUG2) {
				System.err.println("   ignore");
			}
			
			return;
		}
		
		final int modSize = computeHashSetCapacity(size);
		final HashMap<HashMap<LETTER, HashSet<EquivalenceClass>>,
			HashSet<STATE>> letter2succEc2hier =
			new HashMap<HashMap<LETTER, HashSet<EquivalenceClass>>,
			HashSet<STATE>>(modSize);
		final HashSet<STATE> noTransitions = new HashSet<STATE>(modSize);
		final int hierEcModSize =
				computeHashSetCapacity(hierEc.mstates.size());
		
		// go through rows (each entry per row behaves the same)
		for (int i = 0; i < size; ++i) {
			final MatrixRow row = rows.get(i);
			final STATE hier = row.mhier;
			// choose the first entry in this row
			final HashMap<LETTER, HashSet<STATE>> letter2succ =
					row.mlin2letter2succ.values().iterator().next();
			
			if (DEBUG2) {
				System.err.println(" hier " + hier + " -> " + letter2succ);
			}
			
			if (letter2succ == mDownStateMap) {
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
					succEcs.add(mPartition.mstate2EquivalenceClass.
							get(succ));
				}
				letter2succEc.put(letter, succEcs);
			}
			if (DEBUG2) {
				System.err.println("  letter2succEc: " + letter2succEc);
			}
			
			HashSet<STATE> hiers = letter2succEc2hier.get(letter2succEc);
			if (hiers == null) {
				hiers = new HashSet<STATE>(hierEcModSize);
				letter2succEc2hier.put(letter2succEc, hiers);
			}
			hiers.add(hier);
		}
		
		if (DEBUG2) {
			System.err.println("    receiving: " + letter2succEc2hier +
					" and {{DS}=" + noTransitions + "}");
		}
		
		if (noTransitions.size() > 0) {
			letter2succEc2hier.put(null, noTransitions);
		}
		
		if (letter2succEc2hier.size() > 1) {
			if (DEBUG2) {
				System.err.println("    mark hierarchical split of " +
						hierEc.toStringShort() + ": " +
						letter2succEc2hier.values());
			}
			
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
		if (DEBUG2) {
			System.err.println("\n-- executing return splits");
		}
		
		if (STATISTICS) {
			mReturnSeparateTime -= new GregorianCalendar().getTimeInMillis();
		}
		
		for (final EquivalenceClass oldEc : splitEquivalenceClasses) {
			final HashMap<STATE, HashSet<STATE>> state2separatedSet =
					oldEc.mstate2separatedSet;
			assert (state2separatedSet != null);
			
			if (DEBUG2) {
				System.err.print(oldEc);
				System.err.print(" : ");
				System.err.println(state2separatedSet);
			}
			
			// map: color to associated states and blocked states
			int statesRemaining = oldEc.mstates.size();
			final ArrayList<ColorSet> colorSets =
					new ArrayList<ColorSet>(statesRemaining);
			
			// for each state find a color
			outer: for (final Entry<STATE, HashSet<STATE>> stateEntry :
					state2separatedSet.entrySet()) {
				final STATE state = stateEntry.getKey();
				final HashSet<STATE> separatedSet = stateEntry.getValue();
				
				assert (oldEc.mstates.contains(state)) &&
						(separatedSet != null);
				
				// find fitting color
				for (int i = 0; i < colorSets.size(); ++i) {
					// found a fitting color
					final ColorSet colorSet = colorSets.get(i);
					if (! colorSet.mblocked.contains(state)) {
						colorSet.mcontent.add(state);
						colorSet.mblocked.addAll(separatedSet);
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
			
			if (DEBUG2) {
				System.err.println("colorSets: " + colorSets);
			}
			
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
				int maxSize = colorSets.get(0).mcontent.size();
				for (int i = colorSets.size() - 1; i > 0; --i) {
					final int size = colorSets.get(i).mcontent.size();
					if (size > maxSize) {
						maxSize = size;
						remainingColor = i;
					}
				}
			}
			else {
				// find minimum set
				int minSize = colorSets.get(0).mcontent.size();
				for (int i = colorSets.size() - 1; i > 0; --i) {
					final int size = colorSets.get(i).mcontent.size();
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
						mPartition.addEcReturn(colorSets.get(i).mcontent,
								oldEc);
				
				if (STATISTICS) {
					++mSplitsWithChange;
				}
				
				if (DEBUG2) {
					System.err.println("new equivalence class: " +
							newEc.toStringShort());
				}
			}
			
			// reset separation mapping
			oldEc.mstate2separatedSet = null;
		}
		
		if (STATISTICS) {
			mReturnSeparateTime += new GregorianCalendar().getTimeInMillis();
		}
	}
	
	/**
	 * This method is an alternative linear return split.
	 */
	private void splitReturnLinearAlt() {
		final EquivalenceClass succEc = mWorkListRet.next();
		
		if (DEBUG4) {
			System.err.println("L succEc " + succEc.toStringShort());
		}
		
		final HashMap<EquivalenceClass,
			HashSet<IncomingReturnTransition<LETTER, STATE>>>
			linEc2trans = splitReturnFindTransitionsAlt(succEc);
		
		if (linEc2trans.isEmpty()) {
			succEc.mincomingRet = EIncomingStatus.none;
			return;
		}
		
		if (DEBUG4) {
			System.err.println("linEc2trans " + linEc2trans);
		}
		
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
				mPartition.mstate2EquivalenceClass;
		
		for (final STATE succ : succEc.mstates) {
			for (final IncomingReturnTransition<LETTER, STATE> edge :
				mOperand.returnPredecessors(succ)) {
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
		if (DEBUG4) {
			System.err.println("linEc " + linEc + ", transitions " +
					transitions);
		}
		
		final Set<STATE> linStates = linEc.mstates;
		final int linEcSize = linStates.size();
		if (linEcSize == 1) {
			return;
		}
		
		final HashSet<STATE> linsVisited = new HashSet<STATE>(
				computeHashSetCapacity(linEcSize));
		final HashMap<STATE, HashMap<LETTER, HashSet<STATE>>>
				hier2letters2lins = new HashMap<STATE, HashMap<LETTER,
				HashSet<STATE>>>(computeHashSetCapacity(transitions.size()));
		
		linEc.mstate2separatedSet = new HashMap<STATE, HashSet<STATE>>(
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
			
			if (DEBUG4) {
				System.err.println("  hier " + hier);
			}
			
			// compute sets of DS/no DS states
			final int modSize = computeHashSetCapacity(
					linEcSize - linsVisited.size());
			final HashSet<STATE> noDsStates = new HashSet<STATE>(modSize);
			final HashSet<STATE> dsStates = new HashSet<STATE>(modSize);
			for (final STATE lin : linsUnvisited) {
				if (mDoubleDecker.isDoubleDecker(lin, hier)) {
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
				
				if (DEBUG4) {
					System.err.println("  lins " + lins);
				}
				
				if (lins.size() == linsVisited.size()) {
					if (DEBUG4) {
						System.err.println("   ignore");
					}
					
					continue;
				}
				
				for (final STATE lin : linsVisited) {
					if ((! lins.contains(lin)) &&
							(mDoubleDecker.isDoubleDecker(lin, hier))) {
						if (DEBUG4) {
							System.err.println("   later split");
						}
						
						// mark different returns
						for (final STATE linPos : lins) {
							linEc.markPair(lin, linPos);
						}
					}
				}
			}
		}
		
		if (linEc.mstate2separatedSet.size() > 0) {
			if (DEBUG4) {
				System.err.println(" SPLIT");
			}
			
			mSplitEcsReturn.add(linEc);
			splitReturnExecute(mSplitEcsReturn);
			mSplitEcsReturn = new LinkedList<EquivalenceClass>();
		}
		else {
			if (DEBUG4) {
				System.err.println(" NO SPLIT");
			}
		}
		linEc.mstate2separatedSet = null;
	}
	
	/**
	 * This method is an alternative hierarchical return split.
	 */
	private void splitReturnHierAlt() {
		EquivalenceClass succEc;
		while (true) {
			succEc = mWorkListRetHier.next();
			if (succEc.mincomingRet == EIncomingStatus.none) {
				if (! mWorkListRetHier.hasNext()) {
					return;
				}
			}
			else {
				break;
			}
		}
		
		if (DEBUG4) {
			System.err.println("H succEc " + succEc.toStringShort());
		}
		
		final HashMap<EquivalenceClass, HashSet<EquivalenceClass>>
			hierEc2linEcs = splitReturnFindOutgoingTransitions(succEc);
		
		if (hierEc2linEcs.isEmpty()) {
			succEc.mincomingRet = EIncomingStatus.none;
			return;
		}
		
		if (DEBUG4) {
			System.err.println("linEc2hierEcs " + hierEc2linEcs);
		}
		
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
				mPartition.mstate2EquivalenceClass;
		
		for (final STATE succ : succEc.mstates) {
			for (final IncomingReturnTransition<LETTER, STATE> edge :
				mOperand.returnPredecessors(succ)) {
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
		if (DEBUG4) {
			System.err.println("hierEc " + hierEc + ", linEcs " + linEcs);
		}
		
		final Set<STATE> hierStates = hierEc.mstates;
		final int hierEcSize = hierStates.size();
		if (hierEcSize == 1) {
			if (DEBUG4) {
				System.err.println("   ignore");
			}
			
			return;
		}
		
		hierEc.mstate2separatedSet = new HashMap<STATE, HashSet<STATE>>(
				computeHashSetCapacity(hierEcSize));
		final HashMap<STATE, EquivalenceClass> state2ec =
				mPartition.mstate2EquivalenceClass;
		
		for (final EquivalenceClass linEc : linEcs) {
			final HashMap<HashMap<EquivalenceClass, HashSet<LETTER>>,
				HashSet<STATE>> succEc2letter2hiers =
				new HashMap<HashMap<EquivalenceClass, HashSet<LETTER>>,
				HashSet<STATE>>();
			
			for (final STATE hier : hierStates) {
				final HashMap<EquivalenceClass, HashSet<LETTER>>
					succEc2letters = new HashMap<EquivalenceClass,
					HashSet<LETTER>>(computeHashSetCapacity(hierEcSize));
				
				inner: for (final STATE lin : linEc.mstates) {
					if (mDoubleDecker.isDoubleDecker(lin, hier)) {
						final Iterator<OutgoingReturnTransition<LETTER, STATE>>
							edges = mOperand.returnSuccessorsGivenHier(lin,
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
							succEc2letters.put(mNegativeClass, null);
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
		
		if (hierEc.mstate2separatedSet.size() > 0) {
			if (DEBUG4) {
				System.err.println(" SPLIT");
			}
			
			mSplitEcsReturn.add(hierEc);
			splitReturnExecute(mSplitEcsReturn);
			mSplitEcsReturn = new LinkedList<EquivalenceClass>();
		}
		else {
			if (DEBUG4) {
				System.err.println(" NO SPLIT");
			}
		}
		hierEc.mstate2separatedSet = null;
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
		if (DEBUG2) {
			System.err.println("\nNEW RETURN SPLITTING ROUND");
		}
		
		if (DEBUG3) {
			if (mPartition.mequivalenceClasses.size() ==
					mWorkListRet.mqueue.size()) {
				System.err.println("first return split, starting with " +
						mPartition.mequivalenceClasses.size() + " ECs");
			}
		}
		
		if (STATISTICS) {
			mReturnFirstTime -= new GregorianCalendar().getTimeInMillis();
		}
		
		EquivalenceClass linEc;
		HashSet<STATE> hiers;
		final Set<Entry<EquivalenceClass, HashSet<STATE>>> entrySet =
				mFirstReturnLin2hiers.entrySet();
		
		while (true) {
			// continue from last time
			if (! entrySet.isEmpty()) {
				assert (entrySet.size() == 1);
				final Entry<EquivalenceClass, HashSet<STATE>> entry =
						entrySet.iterator().next();
				linEc = entry.getKey();
				hiers = entry.getValue();
			}
			else if (mWorkListRet.hasNext()) {
				linEc = mWorkListRet.next();
			}
			else {
				break;
			}
			
			if (DEBUG3) {
				System.err.println("linEc size: " + linEc.mstates.size());
			}
			
			// singleton equivalence classes are ignored
			if (linEc.mstates.size() == 1) {
				if (DEBUG3) {
					System.err.println(" ignoring");
				}
				
				continue;
			}
			
			// analyse linear equivalence class
			hiers = splitReturnPredecessorsFirstTimeRepeat(linEc,
					new HashSet<STATE>());
			
			while ((hiers != null) && (! hiers.isEmpty())) {
				// new internal and call splits available, prefer them
				if (mWorkListIntCall.hasNext()) {
					mFirstReturnLin2hiers =
							new HashMap<EquivalenceClass, HashSet<STATE>>(2);
					mFirstReturnLin2hiers.put(linEc, hiers);
					break;
				}
				
				// singleton equivalence classes are ignored
				if (linEc.mstates.size() == 1) {
					if (DEBUG3) {
						System.err.println(" ignoring");
					}
					
					continue;
				}
				
				// analyse linear equivalence class
				hiers = splitReturnPredecessorsFirstTimeRepeat(linEc, hiers);
			}
		}
		
		// no equivalence classes left, switch to normal return split
		mFirstReturnSplit = false;
		mWorkListRet.fillWithAll();
		
		if (STATISTICS) {
			mReturnFirstTime += new GregorianCalendar().getTimeInMillis();
		}
		
		if (DEBUG3) {
			System.err.println("first return split executed, now having " +
					mPartition.mequivalenceClasses.size() + " ECs");
		}
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
		if (mSplitEcsReturn.size() == 1) {
			if (DEBUG3) {
				System.err.println("splitting EC of size " +
						linEc.mstates.size());
			}
			
			assert (mSplitEcsReturn.get(0) == linEc);
			splitReturnExecute(mSplitEcsReturn);
			mSplitEcsReturn.clear();
		}
		else {
			assert (mSplitEcsReturn.size() == 0);
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
		final Set<STATE> lins = linEc.mstates;
		
		// collect all relevant hierarchical predecessors
		final HashSet<STATE> newHiers = new HashSet<STATE>();
		boolean broke = (oldHiers.size() == 0);
		outer: for (final STATE lin : lins) {
			for (final OutgoingReturnTransition<LETTER, STATE> edge :
					mOperand.returnSuccessors(lin)) {
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
				if (! mDoubleDecker.isDoubleDecker(lin, hier)) {
					continue;
				}
				
				final Iterator<OutgoingReturnTransition<LETTER, STATE>> edges =
						mOperand.returnSuccessorsGivenHier(lin, hier).
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
	
	@SuppressWarnings("unchecked")
	private void splitReturnExecuteOld(
			final Collection<EquivalenceClass> splitEquivalenceClasses) {
		if (DEBUG2) {
			System.err.println("\n-- executing return splits");
		}
		
		long time;
		if (STATISTICS) {
			time = new GregorianCalendar().getTimeInMillis();
		}
		
		for (final EquivalenceClass oldEc : splitEquivalenceClasses) {
			final HashMap<STATE, HashSet<STATE>> state2separatedSet =
					oldEc.mstate2separatedSet;
			assert (state2separatedSet != null);
			
			if (DEBUG2) {
				System.err.print(oldEc);
				System.err.print(" : ");
				System.err.println(state2separatedSet);
			}
			
			// mapping: state to associated color
			final HashMap<STATE, Integer> state2color =
					new HashMap<STATE, Integer>(
							computeHashSetCapacity(oldEc.mstates.size()));
			// current number of colors
			int colors = 0;
			
			for (final Entry<STATE, HashSet<STATE>> entry :
					state2separatedSet.entrySet()) {
				final STATE state = entry.getKey();
				final HashSet<STATE> separatedSet = entry.getValue();
				
				assert (oldEc.mstates.contains(state)) &&
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
			
			if (DEBUG2) {
				System.err.println("state2color: " + state2color);
			}
			
			// finally split the equivalence class
			for (int i = newEcs.length - 1; i > 0; --i) {
				final HashSet<STATE> newStates = newEcs[i];
				final EquivalenceClass newEc =
						mPartition.addEcReturn(newStates, oldEc);
				
				if (STATISTICS) {
					++mSplitsWithChange;
				}
				
				if (DEBUG2) {
					System.err.println("new equivalence class: " +
							newEc.toStringShort());
				}
			}
			
			// reset separation mapping
			oldEc.mstate2separatedSet = null;
		}
		
		if (STATISTICS) {
			time = new GregorianCalendar().getTimeInMillis() - time;
			mReturnSeparateTime += time;
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
		if (mOperand.callSuccessors(ec.mstates.iterator().next()).
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
		final Set<STATE> oldStates = ec.mstates;
		final int size = computeHashSetCapacity(THRESHOLD);
		while (oldStates.size() > THRESHOLD) {
			final HashSet<STATE> newStates = new HashSet<STATE>(size);
			int i = THRESHOLD;
			for (final STATE state : oldStates) {
				newStates.add(state);
				if (--i == 0) {
					mPartition.addEcReturn(newStates, ec);
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
		final Set<STATE> oldStates = ec.mstates;
		final int size = computeHashSetCapacity(THRESHOLD);
		final LinkedList<HashSet<STATE>> newClasses =
				new LinkedList<HashSet<STATE>>();
		
		HashSet<STATE> returns = new HashSet<STATE>(size);
		for (final STATE state : oldStates) {
			if (mOperand.returnSuccessors(state).iterator().hasNext()) {
				returns.add(state);
				if (returns.size() == THRESHOLD) {
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
			
			mPartition.addEcReturn(states, ec);
		}
	}
	
	/**
	 * For each remaining equivalence class create a new state.
	 * Also remove all other objects references.
	 * 
	 * @param includeMapping true iff mapping old to new state is needed
	 * @return quotient automaton
	 */
	private QuotientNwaConstructor<LETTER, STATE> constructAutomaton(
			final boolean includeMapping) {
		if (DEBUG) {
			System.out.println("finished splitting, constructing result");
		}
		
		mPartition.markInitials();
		
		// construct result with library method
		final QuotientNwaConstructor<LETTER, STATE> quotientNwaConstructor =
				new QuotientNwaConstructor<>(mServices, mStateFactory,
						mDoubleDecker, mPartition, includeMapping);
		
		// clean up
		if (DEBUG) {
			System.out.println("finished construction");
			System.out.println(mPartition);
		}
		mPartition = null;
		mWorkListIntCall = null;
		mWorkListRet = null;
		
		return quotientNwaConstructor;
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
		private Iterator<IncomingInternalTransition<LETTER, STATE>> miterator;
		// current transition
		private IncomingInternalTransition<LETTER, STATE> mtransition;
		
		@Override
		public void nextState(final STATE state) {
			miterator = mOperand.internalPredecessors(state).iterator();
		}
		
		@Override
		public STATE getPred() {
			return mtransition.getPred();
		}
		
		@Override
		public LETTER nextAndLetter() {
			mtransition = miterator.next();
			return mtransition.getLetter();
		}
		
		@Override
		public boolean hasNext() {
			return miterator.hasNext();
		}
	}
	
	/**
	 * This is the implementation for call transitions.
	 */
	private class CallTransitionIterator implements
			ITransitionIterator<LETTER, STATE> {
		// iterator of the operand
		private Iterator<IncomingCallTransition<LETTER, STATE>> miterator;
		// current transition
		private IncomingCallTransition<LETTER, STATE> mtransition;
		
		@Override
		public void nextState(final STATE state) {
			miterator = mOperand.callPredecessors(state).iterator();
		}
		
		@Override
		public LETTER nextAndLetter() {
			mtransition = miterator.next();
			return mtransition.getLetter();
		}
		
		@Override
		public STATE getPred() {
			return mtransition.getPred();
		}
		
		@Override
		public boolean hasNext() {
			return miterator.hasNext();
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
			final boolean isFinal = mOperand.isFinal(it.next());
			while (it.hasNext()) {
				if (isFinal != mOperand.isFinal(it.next())) {
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
			return mOperand.getInternalAlphabet().size();
		}
		
		@Override
		public Set<LETTER> letters(STATE state) {
			assert (assertLetters(state));
			
			return mOperand.lettersInternal(state);
		}

		@Override
		public Collection<STATE> newCollection() {
			return new HashSet<STATE>();
		}
		
		@Override
		public boolean assertLetters(STATE state) {
			final Collection<LETTER> model =
					mOperand.lettersInternal(state);
			
			final HashSet<LETTER> checker = new HashSet<LETTER>(
					computeHashSetCapacity(model.size()));
			final Iterator<OutgoingInternalTransition<LETTER, STATE>> it =
					mOperand.internalSuccessors(state).iterator();
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
			return mOperand.getCallAlphabet().size();
		}
		
		@Override
		public Set<LETTER> letters(STATE state) {
			assert assertLetters(state);
			
			return mOperand.lettersCall(state);
		}
		
		@Override
		public Collection<STATE> newCollection() {
			return new LinkedList<STATE>();
		}
		
		@Override
		public boolean assertLetters(STATE state) {
			final Collection<LETTER> model =
					mOperand.lettersCall(state);
			
			final HashSet<LETTER> checker = new HashSet<LETTER>(
					computeHashSetCapacity(model.size()));
			final Iterator<OutgoingCallTransition<LETTER, STATE>> it =
					mOperand.callSuccessors(state).iterator();
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
					splitOutgoingHelper(states, mOutCall);
			for (final Collection<STATE> callStates : callSplit.values()) {
				final HashMap<Collection<LETTER>, Collection<STATE>>
				internalSplit = splitOutgoingHelper(callStates, mOutInternal);
				
				// split states
				for (final Collection<STATE> newStates :
						internalSplit.values()) {
					assert (newStates.size() > 0) &&
							(newStates instanceof HashSet<?>);
					mPartition.addEcInitialization((HashSet<STATE>)newStates);
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
			HashMap<LETTER, HashSet<STATE>>>> mhier2lin2letter2succ;
		
		/**
		 * @param size number of non-singleton 
		 */
		public Matrix(final int size) {
			mhier2lin2letter2succ = new HashMap<STATE, HashMap<STATE,
					HashMap<LETTER, HashSet<STATE>>>>(
							computeHashSetCapacity(size));
		}
		
		/**
		 * This constructor is only used for the useless 1x1-matrix.
		 */
		private Matrix() {
			mhier2lin2letter2succ = null;
		}

		@Override
		public String toString() {
			return (mhier2lin2letter2succ == null)
					? "{1x1-matrix}"
					: mhier2lin2letter2succ.toString();
		}
	}
	
	/**
	 * This class represents a matrix row. It knows its associated hierarchical
	 * predecessor state and the matrix entries of this row.
	 */
	private class MatrixRow {
		private final STATE mhier;
		private final HashMap<STATE, HashMap<LETTER, HashSet<STATE>>>
			mlin2letter2succ;
		
		/**
		 * @param hier the hierarchical state
		 * @param lin2letter2succ the map (matrix row entries)
		 */
		public MatrixRow(final STATE hier, final HashMap<STATE, HashMap<LETTER,
				HashSet<STATE>>> lin2letter2succ) {
			mhier = hier;
			assert (! lin2letter2succ.isEmpty());
			mlin2letter2succ = lin2letter2succ;
		}
		
		@Override
		public String toString() {
			return mhier + " -> " + mlin2letter2succ;
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
		final HashSet<STATE> mcontent;
		final HashSet<STATE> mblocked;
		
		/**
		 * @param size size of the equivalence class
		 * @param state the first state
		 * @param blocked the set of blocked states
		 */
		public ColorSet(final int size, final STATE state,
				final HashSet<STATE> blocked) {
			mcontent = new HashSet<STATE>(computeHashSetCapacity(size));
			mcontent.add(state);
			mblocked = blocked;
		}
	}
	
	// --- [end] helper methods and classes --- //
	
	// --- [start] important inner classes --- //
	
	/**
	 * The partition is the main object of the procedure.
	 * It contains and handles the equivalence classes and works as the
	 * resulting automaton.
	 */
	public class Partition implements IPartition<STATE> {
		// equivalence classes
		private final Collection<EquivalenceClass> mequivalenceClasses;
		// mapping 'state -> equivalence class'
		private final HashMap<STATE,EquivalenceClass> mstate2EquivalenceClass;
		
		public Partition() {
			mequivalenceClasses = new LinkedList<EquivalenceClass>();
			mstate2EquivalenceClass = new HashMap<STATE, EquivalenceClass>(
					computeHashSetCapacity(mOperand.size()));
		}
		
		/**
		 * marks all respective equivalence classes as initial
		 */
		public void markInitials() {
			/*
			 * if an equivalence class contains an initial state,
			 * the whole equivalence class should be initial
			 */
			for (final STATE state : mOperand.getInitialStates()) {
				final EquivalenceClass ec = mstate2EquivalenceClass.get(state);
				ec.markAsInitial();
			}
		}

		/**
		 * This method adds an equivalence class (also to the work list)
		 * during the initialization phase.
		 *
		 * @param module the states in the equivalence class
		 */
		private void addEcInitialization(final Set<STATE> module) {
			final EquivalenceClass ec = new EquivalenceClass(module);
			mequivalenceClasses.add(ec);
			for (final STATE state : module) {
				mstate2EquivalenceClass.put(state, ec);
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
			Set<STATE> newStates = parent.mintersection;
			if (newStates.size() > parent.mstates.size()) {
				newStates = parent.mstates;
				parent.mstates = parent.mintersection;
			}
			final EquivalenceClass ec =
					new EquivalenceClass(newStates, parent);
			mequivalenceClasses.add(ec);
			for (final STATE state : ec.mstates) {
				mstate2EquivalenceClass.put(state, ec);
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
			mequivalenceClasses.add(ec);
			
			// update mapping
			for (final STATE state : states) {
				assert (parent.mstates.contains(state)) &&
					(mstate2EquivalenceClass.get(state) == parent);
				
				parent.mstates.remove(state);
				mstate2EquivalenceClass.put(state, ec);
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
			final EquivalenceClass ec = mstate2EquivalenceClass.get(state);
			
			// first occurrence of the equivalence class, mark it
			if (ec.mintersection.size() == 0) {
				assert (! splitEcs.contains(ec));
				splitEcs.add(ec);
			}
			else {
				assert (splitEcs.contains(ec));
			}
			
			// move state to intersection set
			ec.mintersection.add(state);
			
			// remove state from old set
			ec.mstates.remove(state);
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
				if (DEBUG) {
					System.out.println("splitting state " + state);
				}
				splitState(state, splitEcs);
			}
			
			// check and finalize splits
			for (final EquivalenceClass ec : splitEcs) {
				// split removed every state, restore equivalence class
				if (ec.mstates.isEmpty()) {
					ec.mstates = ec.mintersection;
					if (DEBUG) {
						System.out.println("EC was skipped " + ec);
					}
					++mSplitsWithoutChange;
				}
				// do a split
				else {
					if (DEBUG) {
						System.out.println("EC was split " + ec);
					}
					++mSplitsWithChange;
					
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
			for (final EquivalenceClass ec : mequivalenceClasses) {
				builder.append(append);
				append = ", ";
				builder.append(ec);
			}
			builder.append("}");
			return builder.toString();
		}

		@Override
		public IBlock<STATE> getBlock(final STATE state) {
			return mstate2EquivalenceClass.get(state);
		}

		@Override
		public int size() {
			return mequivalenceClasses.size();
		}

		@Override
		public Iterator<IBlock<STATE>> blocksIterator() {
			return new Iterator<IBlock<STATE>>() {
				final Iterator<EquivalenceClass> mIt =
						mequivalenceClasses.iterator();
				
				@Override
				public boolean hasNext() {
					return mIt.hasNext();
				}
				
				@Override
				public IBlock<STATE> next() {
					return mIt.next();
				}
			};
		}
	}
	
	/**
	 * An equivalence class contains states and knows whether it is in the
	 * work list.
	 * 
	 * Two equivalence class objects are equal iff they share the same pointer.
	 */
	private class EquivalenceClass implements IBlock<STATE> {
		// unique ID (useful for hashCode and so for deterministic runs)
		private final int mid;
		// the states
		private Set<STATE> mstates;
		// intersection set that finally becomes a new equivalence class
		private Set<STATE> mintersection;
		// status regarding incoming transitions
		private EIncomingStatus mincomingInt, mincomingCall, mincomingRet;
		// mapping: state to states that are separated
		private HashMap<STATE, HashSet<STATE>> mstate2separatedSet;
		// matrix with return transition information
		private Matrix mmatrix;
		// status regarding outgoing return transitions
		private EIncomingStatus moutgoingRet;
		// does the equivalence class contain an initial state?
		private boolean misInitial;
		
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
			mid = ++mIds;
			mstates = states;
			reset();
		}
		
		/**
		 * sets the equivalence class as initial
		 */
		void markAsInitial() {
			misInitial = true;
		}
		
		/**
		 * This constructor is reserved for the placeholder equivalence class.
		 */
		private EquivalenceClass() {
			mid = 0;
			mstates = null;
			mintersection = null;
		}
		
		/**
		 * This constructor is used for the initialization. 
		 * 
		 * @param states the set of states for the equivalence class
		 */
		public EquivalenceClass(final Set<STATE> states) {
			this(states, false);
			mincomingInt = EIncomingStatus.inWL;
			mincomingCall = EIncomingStatus.inWL;
			mWorkListIntCall.add(this);
			mincomingRet = EIncomingStatus.inWL;
			mWorkListRet.add(this);
			if (mFirstReturnSplitAlternative) {
				moutgoingRet = EIncomingStatus.inWL;
				mWorkListRetHier.add(this);
			}
			mmatrix = null;
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
			switch (parent.mincomingInt) {
				case unknown:
				case inWL:
					mincomingInt = EIncomingStatus.inWL;
					mWorkListIntCall.add(this);
					break;
				case none:
					mincomingInt = EIncomingStatus.none;
			}
			switch (parent.mincomingCall) {
				case unknown:
				case inWL:
					mincomingCall = EIncomingStatus.inWL;
					if (mincomingInt != EIncomingStatus.inWL) {
						mWorkListIntCall.add(this);
					}
					break;
				case none:
					mincomingCall = EIncomingStatus.none;
			}
			switch (parent.mincomingRet) {
				case unknown:
				case inWL:
					mincomingRet = EIncomingStatus.inWL;
					mWorkListRet.add(this);
					break;
				case none:
					mincomingRet = EIncomingStatus.none;
					break;
			}
			if (mFirstReturnSplitAlternative) {
				switch (parent.moutgoingRet) {
					case unknown:
					case inWL:
						moutgoingRet = EIncomingStatus.inWL;
						mWorkListRetHier.add(this);
						break;
					case none:
						moutgoingRet = EIncomingStatus.none;
						break;
				}
			}
			if (mReturnSplitCorrectnessEcs != null) {
				// own predecessors
				for (final STATE state : mstates) {
					for (final IncomingReturnTransition<LETTER, STATE>
							transition : mOperand.returnPredecessors(state)) {
						mReturnSplitCorrectnessEcs.add(
								mPartition.mstate2EquivalenceClass.get(
										transition.getLinPred()));
					}
				}
				// parent predecessors
				for (final STATE state : parent.mstates) {
					for (final IncomingReturnTransition<LETTER, STATE>
							transition : mOperand.returnPredecessors(state)) {
						mReturnSplitCorrectnessEcs.add(
								mPartition.mstate2EquivalenceClass.get(
										transition.getLinPred()));
					}
				}
				// inherit from parent
				if (mReturnSplitCorrectnessEcs.contains(parent)) {
					mReturnSplitCorrectnessEcs.add(this);
				}
			}
			resetMatrix(parent);
		}
		
		@Override
		public int hashCode() {
			return mid;
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
				mMatrixTime -= new GregorianCalendar().getTimeInMillis();
			}
			
			final Collection<EquivalenceClass> hierEcsUsed;
			
			// ignore singletons
			if (mstates.size() == 1) {
				hierEcsUsed =
						new ArrayList<EquivalenceClass>(hierEcs.size());
				for (final EquivalenceClass hierEc : hierEcs) {
					if (hierEc.mstates.size() > 1) {
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
				if (DEBUG2) {
					System.err.println("--creating 1x1 dummy matrix");
				}
				
				mmatrix = mSingletonMatrix;
				
				if (STATISTICS) {
					mMatrixTime += new GregorianCalendar().getTimeInMillis();
				}
				return;
			}
			
			mmatrix = new Matrix(size);
			final HashMap<STATE, HashMap<STATE,
				HashMap<LETTER, HashSet<STATE>>>> hier2lin2letter2succ =
				mmatrix.mhier2lin2letter2succ;
			
			if (DEBUG2) {
				System.err.println("--adding entries");
			}
			
			// add entries
			final int mapSize = computeHashSetCapacity(mstates.size());
			
			for (final EquivalenceClass hierEc : hierEcsUsed) {
				for (final STATE hier : hierEc.mstates) {
					final HashMap<STATE, HashMap<LETTER,
						HashSet<STATE>>> lin2letter2succ =
						new HashMap<STATE, HashMap<LETTER,
						HashSet<STATE>>>(mapSize);
					
					if (DEBUG2) {
						System.err.println(" consider hier: " + hier);
					}
					
					for (final STATE lin : mstates) {
						if (DEBUG2) {
							System.err.println("  and lin: " + lin);
						}
						
						// first check whether hier is a down state
						if (! mDoubleDecker.isDoubleDecker(lin, hier))
								{
							if (DEBUG2) {
								System.err.println("  no DS");
							}
							
							continue;
						}
						
						final Iterator<OutgoingReturnTransition
							<LETTER, STATE>> edges = mOperand.
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
							
							if (DEBUG2) {
								System.err.println("  transitions: " +
										return2succ);
							}
						}
						else {
							if (DEBUG2) {
								System.err.println("  DS");
							}
							
							lin2letter2succ.put(lin, mDownStateMap);
						}
					}
					
					if (lin2letter2succ.size() > 0) {
						hier2lin2letter2succ.put(hier, lin2letter2succ);
					}
				}
				assert (hier2lin2letter2succ.size() > 0);
			}
			if (STATISTICS) {
				mMatrixTime += new GregorianCalendar().getTimeInMillis();
			}
			
			if (DEBUG2) {
				System.err.println("--finished creating matrix");
			}
		}
		
		/**
		 * This method checks whether a parent equivalence class (after a
		 * split) had a matrix. If so, the split states are shifted to the
		 * new child equivalence class.
		 * 
		 * @param parent parent equivalenceClass class
		 */
		private void resetMatrix(final EquivalenceClass parent) {
			final Matrix oldMatrix = parent.mmatrix;
			if ((oldMatrix == null) || (oldMatrix == mSingletonMatrix)) {
				return;
			}
			
			if (DEBUG2) {
				System.err.println("shifting matrix from " +
						parent.toStringShort() + "(" + oldMatrix + ") to " +
						toStringShort());
			}

			final HashMap<STATE, HashMap<STATE, HashMap<LETTER,
				HashSet<STATE>>>> oldHier2lin2letter2succ =
				oldMatrix.mhier2lin2letter2succ;
			final LinkedList<STATE> removeHiers = new LinkedList<STATE>();
			final Set<STATE> states = mstates;
			mmatrix = new Matrix(
					oldHier2lin2letter2succ.size());
			final HashMap<STATE, HashMap<STATE, HashMap<LETTER,
					HashSet<STATE>>>> hier2lin2letter2succ =
					mmatrix.mhier2lin2letter2succ;
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
					parent.mmatrix = null;
				}
				else if (parent.mstates.size() - mstates.size() == 1) {
					parent.mmatrix = mSingletonMatrix;
				}
			}
			
			if (hier2lin2letter2succ.size() <= 1) {
				if (hier2lin2letter2succ.size() == 0) {
					mmatrix = null;
				}
				else if (mstates.size() == 1) {
					mmatrix = mSingletonMatrix;
				}
			}
			
			if (DEBUG2) {
				System.err.println("resulting in matrices: parent: " +
						parent.mmatrix + ", child: " +
						mmatrix);
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
			
			if (mstate2separatedSet == null) {
				mstate2separatedSet = new HashMap<STATE, HashSet<STATE>>(
						computeHashSetCapacity(mstates.size()));
				mSplitEcsReturn.add(this);
			}
			else {
				assert (mSplitEcsReturn.contains(this));
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
			if (DEBUG2) {
				System.err.println("separate " + state1 + " " + state2);
			}
			
			assert ((state1 != state2) && (mstates.contains(state1)) &&
					 (mstates.contains(state2)));
			
			HashSet<STATE> separated = mstate2separatedSet.get(state1);
			if (separated == null) {
				separated = new HashSet<STATE>();
				mstate2separatedSet.put(state1, separated);
			}
			separated.add(state2);
			
			separated = mstate2separatedSet.get(state2);
			if (separated == null) {
				separated = new HashSet<STATE>();
				mstate2separatedSet.put(state2, separated);
			}
			separated.add(state1);
		}
		
		/**
		 * This method resets the intersection set.
		 */
		private void reset() {
			mintersection = new HashSet<STATE>(
					computeHashSetCapacity(mstates.size()));
			mstate2separatedSet = null;
		}
		
		@Override
		public String toString() {
			if (mstates == null) {
				return "negative equivalence class";
			}
			
			if (!DEBUG && (DEBUG2 || DEBUG3 || DEBUG4)) {
				return toStringShort();
			}
			
			final StringBuilder builder = new StringBuilder();
			String append = "";
			
			builder.append("<[");
			builder.append(mincomingInt);
			builder.append(",");
			builder.append(mincomingCall);
			builder.append(",");
			builder.append(mincomingRet);
			if (mFirstReturnSplitAlternative) {
				builder.append(",");
				builder.append(moutgoingRet);
			}
			builder.append("], [");
			for (final STATE state : mstates) {
				builder.append(append);
				append = ", ";
				builder.append(state);
			}
			builder.append("], [");
			append = "";
			for (final STATE state : mintersection) {
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
			if (mstates == null) {
				return "negative equivalence class";
			}
			
			final StringBuilder builder = new StringBuilder();
			String append = "";
			
			builder.append("<");
			for (final STATE state : mstates) {
				builder.append(append);
				append = ", ";
				builder.append(state);
			}
			builder.append(">");
			
			return builder.toString();
		}
		
		@Override
		public boolean isInitial() {
			return misInitial;
		}
		
		@Override
		public boolean isFinal() {
			return mOperand.isFinal(mstates.iterator().next());
		}
		
		@Override
		public STATE minimize(final StateFactory<STATE> stateFactory) {
			return stateFactory.minimize(mstates);
		}
		
		@Override
		public Iterator<STATE> statesIterator() {
			return mstates.iterator();
		}
		
		@Override
		public boolean isRepresentativeIndependentInternalsCalls() {
			return true;
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
		protected final PriorityQueue<EquivalenceClass> mqueue;
		
		public AWorkList() {
			mqueue = new PriorityQueue<EquivalenceClass>(
					Math.max(mOperand.size(), 1),
					new Comparator<EquivalenceClass>() {
						@Override
						public int compare(EquivalenceClass ec1,
								EquivalenceClass ec2) {
							return ec1.mstates.size() - ec2.mstates.size();
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
			assert (! mqueue.contains(ec));
			mqueue.add(ec);
		}
		
		@Override
		public boolean hasNext() {
			return (! mqueue.isEmpty());
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
			for (final EquivalenceClass ec : mqueue) {
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
			final EquivalenceClass ec = mqueue.poll();
			if (DEBUG) {
				System.out.println("\npopping from IntCall WL: " + ec);
			}
			return ec;
		}
		
		@Override
		public void add(final EquivalenceClass ec) {
			assert ((ec.mincomingInt == EIncomingStatus.inWL) ||
					(ec.mincomingCall == EIncomingStatus.inWL));
			if (DEBUG) {
				System.out.println("adding of IntCall WL: " + ec);
			}
			super.add(ec);
		}
	}
	
	/**
	 * This class implements the work list for predecessor return splits.
	 */
	private class WorkListRet extends AWorkList {
		@Override
		public EquivalenceClass next() {
			final EquivalenceClass ec = mqueue.poll();
			ec.mincomingRet = EIncomingStatus.unknown;
			if (DEBUG) {
				System.out.println("\npopping from return WL: " + ec);
			}
			return ec;
		}
		
		@Override
		public void add(final EquivalenceClass ec) {
			assert (ec.mincomingRet == EIncomingStatus.inWL);
			if (DEBUG) {
				System.out.println("adding of return WL: " + ec);
			}
			super.add(ec);
		}
		
		/**
		 * This method fills the queue with all equivalence classes so far.
		 * It is used exactly once when the first return split has finished.
		 */
		public void fillWithAll() {
			for (final EquivalenceClass ec :
					mPartition.mequivalenceClasses) {
				if (ec.mincomingRet != EIncomingStatus.none) {
					ec.mincomingRet = EIncomingStatus.inWL;
					mqueue.add(ec);
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
			final EquivalenceClass ec = mqueue.poll();
			ec.moutgoingRet = EIncomingStatus.unknown;
			if (DEBUG) {
				System.out.println("\npopping from return hier WL: " + ec);
			}
			return ec;
		}
		
		@Override
		public void add(final EquivalenceClass ec) {
			assert (ec.moutgoingRet == EIncomingStatus.inWL);
			if (DEBUG) {
				System.out.println("adding of return hier WL: " + ec);
			}
			super.add(ec);
		}
	}
	
	// --- [end] important inner classes --- //
	
	// --- [start] framework methods --- //
	
	@Override
	public INestedWordAutomatonSimple<LETTER,STATE> getResult() {
		assert mResult != null;
		return mResult;
	}
	
	/**
	 * @return map from input automaton states to output automaton states
	 */
	public Map<STATE, STATE> getOldState2newState() {
		return mOldState2newState;
	}
	
	// --- [end] framework methods --- //
}
