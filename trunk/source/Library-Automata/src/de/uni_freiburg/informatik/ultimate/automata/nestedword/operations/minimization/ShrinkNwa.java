/*
 * Copyright (C) 2013-2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization;

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
import java.util.Map.Entry;
import java.util.PriorityQueue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.util.IAutomatonStatePartition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.util.IBlock;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.util.PartitionBackedSetOfPairs;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * This class minimizes nested word automata.
 * <p>
 * It is based on Hopcroft's minimization for deterministic finite automata.
 * <p>
 * Basically we do an over-approximation of the language by merging all states. Then iteratively the so-called
 * equivalence classes are split until no more witness for a split is found.
 * <p>
 * For DFAs the algorithm just performs Hopcroft's algorithm.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class ShrinkNwa<LETTER, STATE> extends AbstractMinimizeNwa<LETTER, STATE> {
	// size suggestion for random splits of blocks for efficiency reasons
	public static final int SUGGESTED_RANDOM_SPLIT_SIZE = 200;

	// TODO<debug>
	// general output
	private static final boolean DEBUG = false;
	// general return split
	private static final boolean DEBUG2 = false;
	// first return split
	private static final boolean DEBUG3 = false;
	// naive return split
	private static final boolean DEBUG4 = false;

	// TODO<statistics>
	private static final boolean STATISTICS = false;

	// size information before return splits
	private static final boolean STAT_RETURN_SIZE = false;

	private static final int HIER_PRED_MAX_SIZE = 150;

	// old automaton
	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	private IDoubleDeckerAutomaton<LETTER, STATE> mDoubleDecker;
	// partition object
	private Partition mPartition;
	// IDs for equivalence classes
	private int mEquivalenceClassIds;
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

	// after a split, add both equivalence classes to work list for automata with nondeterministic transitions
	private final boolean mNondeterministicTransitions;

	/* optional random splits before the return split to keep matrices small */
	// true iff before the first return split some random splits are executed
	private boolean mRandomReturnSplit;
	// maximum size of equivalence classes with outgoing calls/returns
	private final int mTreshold;

	// true iff first return split is not finished yet
	private boolean mFirstReturnSplit;
	// map for first return split (open check)
	private HashMap<EquivalenceClass, HashSet<STATE>> mFirstReturnLin2Hiers;

	// temporarily activate alternative return split before the first run
	private boolean mFirstReturnSplitAlternative;
	// also do the hierarchical split without a matrix
	private boolean mFirstReturnSplitHierAlternative;

	/* split all call predecessors to avoid one dimension in the matrix */
	private boolean mSplitAllCallPreds;

	/* naive return split (needs another split for correctness) */
	private boolean mReturnSplitNaive;
	private HashSet<EquivalenceClass> mReturnSplitCorrectnessEcs;

	private int mSplitsWithChange;
	private int mSplitsWithoutChange;
	private int mIncomingTransitions;
	private int mNoIncomingTransitions;
	private int mIgnoredReturnSingletons1x1;
	private long mReturnTime;
	private long mMatrixTime;
	private long mWholeTime;
	private long mReturnSeparateTime;
	private long mReturnFirstTime;
	private long mReturnFirstTimeAlternative;
	private long mReturnFirstTimeHierAlternative;

	private final BufferedWriter mWriter1;
	private final BufferedWriter mWriter2;

	private final int mInitialPartitionSize;
	private int mLargestBlockInitialPartition;

	private final boolean mInitialPartitionSeparatesFinalsAndNonfinals;

	/**
	 * This constructor creates a copy of the operand.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            preprocessed nested word automaton preprocessing: dead end and unreachable states/transitions removed
	 * @throws AutomataOperationCanceledException
	 *             if cancel signal is received
	 */
	public ShrinkNwa(final AutomataLibraryServices services, final IMinimizationStateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, false, 0, false, 0, false, false);
	}

	/**
	 * This constructor creates a copy of the operand with additional options.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            preprocessed nested word automaton preprocessing: dead end and unreachable states/transitions removed
	 * @param stateFactory
	 *            state factory
	 * @param splitOutgoing
	 *            true iff states should be split initially by outgoing transitions
	 * @param splitRandomSize
	 *            size of equivalence classes before first return split (0 for deactivation)
	 * @param firstReturnSplit
	 *            true iff before first return split there shall be a preprocessing
	 * @param firstReturnSplitAlternative
	 *            0 == no alternative return split 1 == alternative return split 2 == alternative hierarchical split
	 * @param returnSplitNaive
	 *            true iff a naive return split is used
	 * @param splitAllCallPreds
	 *            true iff all call predecessors should be singleton
	 * @throws AutomataOperationCanceledException
	 *             if cancel signal is received
	 */
	public ShrinkNwa(final AutomataLibraryServices services, final IMinimizationStateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand, final boolean splitOutgoing, final int splitRandomSize,
			final boolean firstReturnSplit, final int firstReturnSplitAlternative, final boolean splitAllCallPreds,
			final boolean returnSplitNaive) throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, null, false, false, splitOutgoing, splitRandomSize, firstReturnSplit,
				firstReturnSplitAlternative, splitAllCallPreds, returnSplitNaive, true, false);
	}

	/**
	 * This constructor creates a copy of the operand with an initial partition.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            preprocessed nested word automaton preprocessing: dead end and unreachable states/transitions removed
	 * @param equivalenceClasses
	 *            represent initial equivalence classes
	 * @param stateFactory
	 *            state factory
	 * @param addMapOldState2newState
	 *            true iff mapping old to new state is needed
	 * @param isFiniteAutomaton
	 *            true iff automaton is a finite automaton
	 * @param splitOutgoing
	 *            true iff states should be split initially by outgoing transitions
	 * @param splitRandomSize
	 *            size of equivalence classes before first return split (0 for deactivation)
	 * @param firstReturnSplit
	 *            true iff before first return split there shall be a preprocessing
	 * @param firstReturnSplitAlternative
	 *            0 == no alternative return split 1 == alternative return split 2 == alternative hierarchical split
	 * @param splitAllCallPreds
	 *            true iff all call predecessors should be singleton
	 * @param returnSplitNaive
	 *            true iff a naive return split is used
	 * @param nondeterministicTransitions
	 *            should be set to true for automata with nondeterministic transitions (more expensive, but correct)
	 * @throws AutomataOperationCanceledException
	 *             if cancel signal is received
	 */
	public ShrinkNwa(final AutomataLibraryServices services, final IMinimizationStateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final PartitionBackedSetOfPairs<STATE> equivalenceClasses, final boolean addMapOldState2newState,
			final boolean isFiniteAutomaton, final boolean splitOutgoing, final int splitRandomSize,
			final boolean firstReturnSplit, final int firstReturnSplitAlternative, final boolean splitAllCallPreds,
			final boolean returnSplitNaive, final boolean nondeterministicTransitions,
			final boolean initialPartitionSeparatesFinalsAndNonfinals) throws AutomataOperationCanceledException {
		super(services, stateFactory);
		mOperand = operand;

		printStartMessage();
		if (STAT_RETURN_SIZE) {
			try {
				mWriter1 = new BufferedWriter(new FileWriter(new File("DEBUG-1.txt")));
				mWriter2 = new BufferedWriter(new FileWriter(new File("DEBUG-2.txt")));
			} catch (final IOException e) {
				throw new AssertionError(e);
			}
		} else {
			mWriter1 = null;
			mWriter2 = null;
		}

		if (operand instanceof IDoubleDeckerAutomaton) {
			mDoubleDecker = (IDoubleDeckerAutomaton<LETTER, STATE>) operand;
		} else {
			if (!isFiniteAutomaton()) {
				throw new IllegalArgumentException(
						"The input must either be a finite automaton or an IDoubleDeckerAutomaton.");
			}
			mDoubleDecker = null;
		}
		mInitialPartitionSeparatesFinalsAndNonfinals = initialPartitionSeparatesFinalsAndNonfinals;
		mPartition = new Partition();
		mEquivalenceClassIds = 0;
		mWorkListIntCall = new WorkListIntCall();
		mWorkListRet = new WorkListRet();
		mSplitEcsReturn = new LinkedList<>();
		mNegativeSet = new HashSet<>();
		mNegativeClass = new EquivalenceClass();
		mNegativeSet.add(mNegativeClass);
		mSingletonMatrix = new Matrix();
		mDownStateMap = new DummyMap();
		mInitialPartitionSize = equivalenceClasses == null ? 0 : equivalenceClasses.getRelation().size();

		/* options */
		mSplitOutgoing = splitOutgoing;
		if (mSplitOutgoing) {
			mOutInternal = new OutgoingHelperInternal();
			mOutCall = new OutgoingHelperCall();
		} else {
			mOutInternal = null;
			mOutCall = null;
		}

		mTreshold = splitRandomSize;
		mRandomReturnSplit = splitRandomSize > 0;

		mFirstReturnSplit = firstReturnSplit;
		mFirstReturnLin2Hiers = mFirstReturnSplit ? new HashMap<>(2) : null;

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
				throw new IllegalArgumentException("firstReturnSplitAlternative must be one of 0, 1, 2.");
		}
		if (mFirstReturnSplitAlternative) {
			mWorkListRetHier = new WorkListRetHier();
		}

		mSplitAllCallPreds = splitAllCallPreds;

		mReturnSplitNaive = returnSplitNaive;
		if (mReturnSplitNaive) {
			mReturnSplitCorrectnessEcs = new HashSet<>();
		}

		mNondeterministicTransitions = nondeterministicTransitions;

		// must be the last part of the constructor
		minimize(isFiniteAutomaton, equivalenceClasses, addMapOldState2newState);
		constructAutomaton(addMapOldState2newState);

		printExitMessage();

		if (STATISTICS) {
			mWholeTime += new GregorianCalendar().getTimeInMillis();

			mLogger.info("positive splits: " + mSplitsWithChange);
			mLogger.info("negative splits: " + mSplitsWithoutChange);
			mLogger.info("quota (p/n): " + (mSplitsWithoutChange == 0
					? "--"
					: (((double) mSplitsWithChange) / ((double) mSplitsWithoutChange))));
			mLogger.info("incoming transition checks : " + mIncomingTransitions);
			mLogger.info("no incoming transitions found : " + mNoIncomingTransitions);
			mLogger.info("quota (p/n): " + (mNoIncomingTransitions == 0
					? "--"
					: (((double) mIncomingTransitions) / ((double) mNoIncomingTransitions))));
			mLogger.info("ignored return splits due to singletons: " + mIgnoredReturnSingletons1x1);
			mLogger.info("time consumption (ms): return separation: " + mReturnSeparateTime + ", matrix time: "
					+ mMatrixTime + ", first return split: " + mReturnFirstTime + ", alternative lin "
					+ mReturnFirstTimeAlternative + ", alternative hier " + mReturnFirstTimeHierAlternative
					+ ", returns: " + mReturnTime + ", all: " + mWholeTime);
			mLogger.info(
					"quota (ret/all): " + (mWholeTime == 0 ? "--" : (((double) mReturnTime) / ((double) mWholeTime)))
							+ ", without: " + (mWholeTime - mReturnTime) + " ms");
			mLogger.info(
					"quota (mat/ret): " + (mReturnTime == 0 ? "--" : (((double) mMatrixTime) / ((double) mReturnTime)))
							+ ", without: " + (mReturnTime - mMatrixTime) + " ms");
			mLogger.info(
					"quota (mat/all): " + (mWholeTime == 0 ? "--" : (((double) mMatrixTime) / ((double) mWholeTime)))
							+ ", without: " + (mWholeTime - mMatrixTime) + " ms");
			mLogger.info("quota (first/all): "
					+ (mWholeTime == 0 ? "--" : (((double) mReturnFirstTime) / ((double) mWholeTime))) + ", without: "
					+ (mWholeTime - mReturnFirstTime) + " ms");
			mLogger.info("quota (altLin/all): "
					+ (mWholeTime == 0 ? "--" : (((double) mReturnFirstTimeAlternative) / ((double) mWholeTime)))
					+ ", without: " + (mWholeTime - mReturnFirstTimeAlternative) + " ms");
			mLogger.info("quota (altHier/all): "
					+ (mWholeTime == 0 ? "--" : (((double) mReturnFirstTimeHierAlternative) / ((double) mWholeTime)))
					+ ", without: " + (mWholeTime - mReturnFirstTimeHierAlternative) + " ms");
		}
	}

	@Override
	protected INestedWordAutomaton<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		final AutomataOperationStatistics statistics = super.getAutomataOperationStatistics();
		if (mLargestBlockInitialPartition != 0) {
			statistics.addKeyValuePair(StatisticsType.SIZE_MAXIMAL_INITIAL_BLOCK, mLargestBlockInitialPartition);
		}
		return statistics;
	}

	// --- [start] main methods --- //

	/**
	 * This is the main method that merges states not distinguishable (based on Hopcroft's algorithm).
	 * 
	 * @param isFiniteAutomaton
	 *            true iff automaton is a finite automaton
	 * @param modules
	 *            predefined modules that must be split
	 * @param includeMapping
	 *            true iff mapping old to new state is needed
	 * @throws AutomataOperationCanceledException
	 *             if cancel signal is received
	 */
	private void minimize(final boolean isFiniteAutomaton, final PartitionBackedSetOfPairs<STATE> modules,
			final boolean includeMapping) throws AutomataOperationCanceledException {
		if (STATISTICS) {
			mWholeTime -= new GregorianCalendar().getTimeInMillis();
		}

		if (DEBUG) {
			mLogger.debug("---------------START---------------");
		}
		// initialize the partition object
		initialize(modules);

		final InternalTransitionIterator internalIterator = new InternalTransitionIterator();

		// for DFAs only the internal split is both necessary and sufficient
		if (isFiniteAutomaton) {
			// iterative refinement
			while (mWorkListIntCall.hasNext()) {
				// cancel if signal is received
				checkTimeOut();

				final EquivalenceClass a = mWorkListIntCall.next();

				// internal split
				splitInternalOrCallPredecessors(a, internalIterator, true);
			}
		} else {
			// more complicated splitting
			final CallTransitionIterator callIterator = new CallTransitionIterator();

			// iterative refinement
			outer: while (true) {
				checkTimeOut();

				// internals and calls
				while (mWorkListIntCall.hasNext()) {
					final EquivalenceClass a = mWorkListIntCall.next();

					// internal split
					if (a.mIncomingInt == IncomingStatus.IN_WORKLIST) {
						a.mIncomingInt = IncomingStatus.UNKNOWN;
						if (DEBUG) {
							mLogger.info("\n-- internal search");
						}
						splitInternalOrCallPredecessors(a, internalIterator, true);
					}

					// call split
					if (a.mIncomingCall == IncomingStatus.IN_WORKLIST) {
						a.mIncomingCall = IncomingStatus.UNKNOWN;
						if (DEBUG) {
							mLogger.info("\n-- call search");
						}
						if (!mSplitAllCallPreds) {
							splitInternalOrCallPredecessors(a, callIterator, false);
						}
					}
				}

				checkTimeOut();

				// return predecessors
				if (mWorkListRet.hasNext()) {
					// optional random split
					if (mRandomReturnSplit) {
						mRandomReturnSplit = false;
						final LinkedList<EquivalenceClass> bigEcs = new LinkedList<>();
						for (final EquivalenceClass ec : mPartition.mEquivalenceClasses) {
							if (ec.mStates.size() > mTreshold) {
								bigEcs.add(ec);
							}
						}
						for (final EquivalenceClass ec : bigEcs) {
							splitRandom(ec);
						}
						continue outer;
					}

					if (STATISTICS) {
						mReturnTime -= new GregorianCalendar().getTimeInMillis();
					}

					if (STAT_RETURN_SIZE) {
						try {
							final GregorianCalendar date = new GregorianCalendar();
							mWriter1.append(
									date.get(GregorianCalendar.MINUTE) + ":" + date.get(GregorianCalendar.SECOND) + ":"
											+ date.get(GregorianCalendar.MILLISECOND) + " (min:sec:ms)\n");
							mWriter1.append(mPartition.mEquivalenceClasses.size() + " ECs before return split of "
									+ mWorkListRet.mQueue.size() + " ECs\n");
							final int[] sizes = new int[mWorkListRet.mQueue.size()];
							mWriter2.append("\n\nnew round with " + sizes.length + " ECs");

							int idx = -1;
							for (final EquivalenceClass ec : mWorkListRet.mQueue) {
								sizes[++idx] = ec.mStates.size();
							}
							Arrays.sort(sizes);
							for (idx = 0; idx < sizes.length; ++idx) {
								if (idx % 15 == 0) {
									mWriter2.append("\n");
								}
								mWriter2.append(sizes[idx] + ", ");
							}
						} catch (final IOException e) {
							throw new AssertionError(e);
						}
					}

					// optional first linear split
					if (mFirstReturnSplit) {
						splitReturnPredecessorsFirstTime();
					} else {
						if (mFirstReturnSplitAlternative) {
							mReturnFirstTimeAlternative -= new GregorianCalendar().getTimeInMillis();
							splitReturnLinearAlt();
							mReturnFirstTimeAlternative += new GregorianCalendar().getTimeInMillis();
						} else if (mReturnSplitNaive) {
							splitReturnNaiveHierarchicalStates(mWorkListRet.next());
						} else {
							splitReturnPredecessors();
						}
					}

					if (STATISTICS) {
						mReturnTime += new GregorianCalendar().getTimeInMillis();
					}

					if (STAT_RETURN_SIZE) {
						try {
							final GregorianCalendar date = new GregorianCalendar();
							mWriter1.append(
									date.get(GregorianCalendar.MINUTE) + ":" + date.get(GregorianCalendar.SECOND) + ":"
											+ date.get(GregorianCalendar.MILLISECOND) + " (min:sec:ms)\n");
							mWriter1.append(mPartition.mEquivalenceClasses.size() + " ECs after return split\n");
						} catch (final IOException e) {
							throw new AssertionError(e);
						}
					}
				} else {
					if (mFirstReturnSplitAlternative) {
						if (mFirstReturnSplitHierAlternative) {
							if (DEBUG4) {
								mLogger.debug("hierarchical split");
							}

							if (mWorkListRetHier.hasNext()) {
								mReturnFirstTimeHierAlternative -= new GregorianCalendar().getTimeInMillis();
								splitReturnHierAlt();
								mReturnFirstTimeHierAlternative += new GregorianCalendar().getTimeInMillis();
								continue outer;
							}
							break outer;
						}
						if (DEBUG4) {
							mLogger.debug("ALTERNATIVE FINISHED");
						}

						mFirstReturnSplitAlternative = false;
						mWorkListRet.fillWithAll();
						continue outer;
					} else if ((mReturnSplitCorrectnessEcs != null) && (!mReturnSplitCorrectnessEcs.isEmpty())) {
						final Iterator<EquivalenceClass> iterator = mReturnSplitCorrectnessEcs.iterator();
						assert iterator.hasNext();
						final EquivalenceClass linEc = iterator.next();
						iterator.remove();
						splitReturnCorrectness(linEc);
						continue outer;
					} else {
						break outer;
					}
				}
			}

			if (STAT_RETURN_SIZE) {
				try {
					mWriter1.close();
					mWriter2.close();
				} catch (final IOException e) {
					mLogger.fatal(e);
				}
			}
		}
		if (DEBUG) {
			mLogger.debug("----------------END----------------");
		}
	}

	private void checkTimeOut() throws AutomataOperationCanceledException {
		if (isCancellationRequested()) {
			final String taskDescription = NestedWordAutomataUtils.generateGenericMinimizationRunningTaskDescription(
					operationName(), mOperand, mInitialPartitionSize, mLargestBlockInitialPartition);
			throw new AutomataOperationCanceledException(new RunningTaskInfo(this.getClass(), taskDescription));
		}
	}

	/**
	 * This method does a naive linear return split. All states that reach the splitter class with the same hierarchical
	 * state and return letter are split from the rest. Additionally, the hierarchical states are considered. This seems
	 * to be worse for the resulting size.
	 * 
	 * @param a
	 *            the splitter equivalence class
	 */
	private void splitReturnNaiveHierarchicalEcs(final EquivalenceClass a) {
		// create a hash map from letter to respective predecessor states
		final HashMap<LETTER, HashMap<EquivalenceClass, HashSet<STATE>>> letter2hierEc2lin = new HashMap<>();
		for (final STATE state : a.mStates) {
			final Iterator<IncomingReturnTransition<LETTER, STATE>> transitions =
					mOperand.returnPredecessors(state).iterator();
			while (transitions.hasNext()) {
				final IncomingReturnTransition<LETTER, STATE> transition = transitions.next();
				final LETTER letter = transition.getLetter();
				HashMap<EquivalenceClass, HashSet<STATE>> hierEc2lin = letter2hierEc2lin.get(letter);
				if (hierEc2lin == null) {
					hierEc2lin = new HashMap<>();
					letter2hierEc2lin.put(letter, hierEc2lin);
				}
				final EquivalenceClass hierEc = mPartition.mState2EquivalenceClass.get(transition.getHierPred());
				HashSet<STATE> lins = hierEc2lin.get(hierEc);
				if (lins == null) {
					lins = new HashSet<>();
					hierEc2lin.put(hierEc, lins);
				}
				lins.add(transition.getLinPred());
			}
		}

		// remember that this equivalence class has no incoming transitions
		if (letter2hierEc2lin.isEmpty()) {
			a.mIncomingRet = IncomingStatus.NONE;
			if (STATISTICS) {
				++mNoIncomingTransitions;
			}
		} else {
			if (STATISTICS) {
				++mIncomingTransitions;
			}

			// split each map value (set of predecessor states)
			for (final HashMap<EquivalenceClass, HashSet<STATE>> hierEc2lin : letter2hierEc2lin.values()) {
				for (final HashSet<STATE> lins : hierEc2lin.values()) {
					assert !lins.isEmpty();
					mPartition.splitEquivalenceClasses(lins);
				}
			}
		}
	}

	/**
	 * This method does a naive linear return split. All states that reach the splitter class with the same hierarchical
	 * state and return letter are split from the rest. Additionally, the hierarchical states are considered. This seems
	 * to be worse for the resulting size.
	 * 
	 * @param ec
	 *            the splitter equivalence class
	 */
	private void splitReturnNaiveHierarchicalStates(final EquivalenceClass ec) {
		// create a hash map from letter to respective predecessor states
		final HashMap<LETTER, HashMap<STATE, HashSet<STATE>>> letter2hier2lin = new HashMap<>();
		for (final STATE state : ec.mStates) {
			final Iterator<IncomingReturnTransition<LETTER, STATE>> transitions =
					mOperand.returnPredecessors(state).iterator();
			while (transitions.hasNext()) {
				final IncomingReturnTransition<LETTER, STATE> transition = transitions.next();
				final LETTER letter = transition.getLetter();
				HashMap<STATE, HashSet<STATE>> hier2lin = letter2hier2lin.get(letter);
				if (hier2lin == null) {
					hier2lin = new HashMap<>();
					letter2hier2lin.put(letter, hier2lin);
				}
				final STATE hier = transition.getHierPred();
				HashSet<STATE> lins = hier2lin.get(hier);
				if (lins == null) {
					lins = new HashSet<>();
					hier2lin.put(hier, lins);
				}
				lins.add(transition.getLinPred());
			}
		}

		// remember that this equivalence class has no incoming transitions
		if (letter2hier2lin.isEmpty()) {
			ec.mIncomingRet = IncomingStatus.NONE;
			if (STATISTICS) {
				++mNoIncomingTransitions;
			}
		} else {
			if (STATISTICS) {
				++mIncomingTransitions;
			}

			// split each map value (set of predecessor states)
			for (final HashMap<STATE, HashSet<STATE>> hier2lin : letter2hier2lin.values()) {
				for (final HashSet<STATE> lins : hier2lin.values()) {
					assert !lins.isEmpty();
					mPartition.splitEquivalenceClasses(lins);
				}
			}
		}
	}

	/**
	 * This method does a naive linear return split. All states that reach the splitter class with the same hierarchical
	 * state and return letter are split from the rest. Hierarchical states are ignored.
	 * 
	 * @param ec
	 *            the splitter equivalence class
	 */
	private void splitReturnNaive(final EquivalenceClass ec) {
		// create a hash map from letter to respective predecessor states
		final HashMap<LETTER, HashSet<STATE>> letter2states = new HashMap<>();
		for (final STATE state : ec.mStates) {
			final Iterator<IncomingReturnTransition<LETTER, STATE>> transitions =
					mOperand.returnPredecessors(state).iterator();
			while (transitions.hasNext()) {
				final IncomingReturnTransition<LETTER, STATE> transition = transitions.next();
				final LETTER letter = transition.getLetter();
				HashSet<STATE> predecessorSet = letter2states.get(letter);
				if (predecessorSet == null) {
					predecessorSet = new HashSet<>();
					letter2states.put(letter, predecessorSet);
				}
				predecessorSet.add(transition.getLinPred());
			}
		}

		// remember that this equivalence class has no incoming transitions
		if (letter2states.isEmpty()) {
			ec.mIncomingRet = IncomingStatus.NONE;
			if (STATISTICS) {
				++mNoIncomingTransitions;
			}
		} else {
			if (STATISTICS) {
				++mIncomingTransitions;
			}

			// split each map value (set of predecessor states)
			for (final HashSet<STATE> predecessorSet : letter2states.values()) {
				assert !predecessorSet.isEmpty();
				mPartition.splitEquivalenceClasses(predecessorSet);
			}
		}
	}

	/**
	 * This method assures correctness for the naive return split.
	 * <p>
	 * Currently it just executes the old return split, which seems to be too expensive.
	 * 
	 * @param linEc
	 *            the linear equivalence class
	 */
	private void splitReturnCorrectness(final EquivalenceClass linEc) {
		if (DEBUG2) {
			mLogger.debug("\nNEW CORRECTNESS RETURN SPLITTING");
		}

		final HashMap<STATE, HashSet<STATE>> lin2hier = new HashMap<>();
		for (final STATE lin : linEc.mStates) {
			final HashSet<STATE> hiers = new HashSet<>();
			final Iterator<OutgoingReturnTransition<LETTER, STATE>> transitions =
					mOperand.returnSuccessors(lin).iterator();
			if (transitions.hasNext()) {
				do {
					hiers.add(transitions.next().getHierPred());
				} while (transitions.hasNext());
				lin2hier.put(lin, hiers);
			}
		}

		HashMap<EquivalenceClass, HashSet<EquivalenceClass>> linEc2hierEc = splitReturnEcTranslation(lin2hier);

		splitReturnForwardsAnalysis(linEc2hierEc, true);

		while (!mSplitEcsReturn.isEmpty()) {
			assert assertSetProperty(mSplitEcsReturn);
			splitReturnExecute(mSplitEcsReturn);
			linEc2hierEc = splitReturnEcTranslation(lin2hier);
			mSplitEcsReturn = new LinkedList<>();
			splitReturnForwardsAnalysis(linEc2hierEc, true);
		}

		splitReturnForwardsAnalysis(linEc2hierEc, false);

		if (!mSplitEcsReturn.isEmpty()) {
			assert assertSetProperty(mSplitEcsReturn);
			splitReturnExecute(mSplitEcsReturn);
			mSplitEcsReturn = new LinkedList<>();
		}
	}

	/**
	 * This method assures correctness for the naive return split.
	 * <p>
	 * Currently it just executes the old return split, which seems to be too expensive. Hierarchical states are not
	 * analyzed.
	 * 
	 * @param linEc
	 *            the linear equivalence class
	 */
	private void splitReturnCorrectnessNoHier(final EquivalenceClass linEc) {
		if (DEBUG2) {
			mLogger.debug("\nNEW CORRECTNESS RETURN SPLITTING");
		}

		final HashMap<STATE, HashSet<STATE>> lin2hier = new HashMap<>();
		for (final STATE lin : linEc.mStates) {
			final HashSet<STATE> hiers = new HashSet<>();
			final Iterator<OutgoingReturnTransition<LETTER, STATE>> transitions =
					mOperand.returnSuccessors(lin).iterator();
			if (transitions.hasNext()) {
				do {
					hiers.add(transitions.next().getHierPred());
				} while (transitions.hasNext());
				lin2hier.put(lin, hiers);
			}
		}

		final HashMap<EquivalenceClass, HashSet<EquivalenceClass>> linEc2hierEc = splitReturnEcTranslation(lin2hier);

		splitReturnForwardsAnalysis(linEc2hierEc, false);

		if (!mSplitEcsReturn.isEmpty()) {
			assert assertSetProperty(mSplitEcsReturn);
			splitReturnExecute(mSplitEcsReturn);
			mSplitEcsReturn = new LinkedList<>();
		}
	}

	/**
	 * This method assures correctness for the naive return split. No matrix is constructed. Currently, the hierarchical
	 * split is missing. The runtime indicates that this method is not reasonable.
	 * 
	 * @param linEc
	 *            the linear equivalence class
	 */
	private void splitReturnCorrectnessNoMatrix(final EquivalenceClass linEc) {
		if (DEBUG2) {
			mLogger.debug("\nNEW CORRECTNESS RETURN SPLITTING");
		}

		// find all hierarchical predecessor equivalence classes
		final HashSet<EquivalenceClass> hierEcs = new HashSet<>();
		for (final STATE lin : linEc.mStates) {
			final Iterator<IncomingReturnTransition<LETTER, STATE>> transitions =
					mOperand.returnPredecessors(lin).iterator();
			while (transitions.hasNext()) {
				hierEcs.add(mPartition.mState2EquivalenceClass.get(transitions.next().getHierPred()));
			}
		}

		// linear split
		for (final EquivalenceClass hierEc : hierEcs) {
			for (final STATE hier : hierEc.mStates) {
				final HashMap<LETTER, HashMap<EquivalenceClass, HashSet<STATE>>> letter2succEc2lins = new HashMap<>();
				for (final STATE lin : linEc.mStates) {
					if (!mDoubleDecker.isDoubleDecker(lin, hier)) {
						continue;
					}
					final Iterator<OutgoingReturnTransition<LETTER, STATE>> transitions =
							mOperand.returnSuccessorsGivenHier(lin, hier).iterator();
					final HashMap<EquivalenceClass, HashSet<STATE>> succEc2lins = new HashMap<>();
					if (transitions.hasNext()) {
						do {
							final OutgoingReturnTransition<LETTER, STATE> transition = transitions.next();
							final EquivalenceClass succEc =
									mPartition.mState2EquivalenceClass.get(transition.getSucc());
							HashSet<STATE> lins = succEc2lins.get(succEc);
							if (lins == null) {
								lins = new HashSet<>();
								succEc2lins.put(succEc, lins);
							}
							lins.add(lin);
						} while (transitions.hasNext());
					} else {
						HashSet<STATE> lins = succEc2lins.get(mNegativeClass);
						if (lins == null) {
							lins = new HashSet<>();
							succEc2lins.put(mNegativeClass, lins);
						}
						lins.add(lin);
					}
				}

				// split linear states
				for (final HashMap<EquivalenceClass, HashSet<STATE>> succEc2lins : letter2succEc2lins.values()) {
					final Collection<HashSet<STATE>> values = succEc2lins.values();
					if (values.size() > 1) {
						hierEc.markSplit(values);
					}
				}
				if (!mSplitEcsReturn.isEmpty()) {
					splitReturnExecute(mSplitEcsReturn);
					mSplitEcsReturn = new LinkedList<>();
				}
			}
		}

		// hierarchical split (missing)
	}

	/**
	 * The partition object is initialized. Final states are separated from non-final states. For the passed modules
	 * this is assumed.
	 * 
	 * @param modulesWrapped
	 *            modules that must be split
	 */
	private void initialize(final PartitionBackedSetOfPairs<STATE> modulesWrapped) {
		// split final from non-final states
		if (modulesWrapped == null) {
			final HashSet<STATE> finals = new HashSet<>();
			final HashSet<STATE> nonfinals = new HashSet<>();

			for (final STATE state : mOperand.getStates()) {
				if (mSplitAllCallPreds && (mOperand.callSuccessors(state).iterator().hasNext())) {
					mPartition.addEcInitialization(Collections.singleton(state));
				} else if (mOperand.isFinal(state)) {
					finals.add(state);
				} else {
					nonfinals.add(state);
				}
			}

			if (mSplitOutgoing) {
				splitOutgoing(finals, nonfinals);
			} else {
				// only separate final and non-final states
				if (!finals.isEmpty()) {
					mPartition.addEcInitialization(finals);
				}
				if (!nonfinals.isEmpty()) {
					mPartition.addEcInitialization(nonfinals);
				}
			}
		} else {
			final Collection<Set<STATE>> modules = modulesWrapped.getRelation();
			if (mInitialPartitionSeparatesFinalsAndNonfinals) {
				// predefined modules are already split with respect to final states
				assert assertStatesSeparation(modules) : "The states in the initial modules are not separated with "
						+ "respect to their final status.";
				for (final Set<STATE> module : modules) {
					mPartition.addEcInitialization(module);
					mLargestBlockInitialPartition = Math.max(mLargestBlockInitialPartition, module.size());
				}
			} else {
				HashSet<STATE> finals = new HashSet<>();
				HashSet<STATE> nonfinals = new HashSet<>();
				for (final Set<STATE> module : modules) {
					for (final STATE state : module) {
						if (mOperand.isFinal(state)) {
							finals.add(state);
						} else {
							nonfinals.add(state);
						}
					}
					if (!finals.isEmpty()) {
						mPartition.addEcInitialization(finals);
						mLargestBlockInitialPartition = Math.max(mLargestBlockInitialPartition, finals.size());
						finals = new HashSet<>();
					}
					if (!nonfinals.isEmpty()) {
						mPartition.addEcInitialization(nonfinals);
						mLargestBlockInitialPartition = Math.max(mLargestBlockInitialPartition, nonfinals.size());
						nonfinals = new HashSet<>();
					}
				}
			}
		}

		if (mSplitAllCallPreds) {
			for (final EquivalenceClass ec : mPartition.mEquivalenceClasses) {
				ec.mIncomingCall = IncomingStatus.NONE;
			}
		}

		if (mReturnSplitCorrectnessEcs != null) {
			mReturnSplitCorrectnessEcs.addAll(mPartition.mEquivalenceClasses);
		}

		if (DEBUG) {
			mLogger.debug("starting with " + mPartition.mEquivalenceClasses.size() + " equivalence classes");
		}
	}

	/**
	 * For each state and internal or call symbol respectively do the usual Hopcroft backwards split.
	 * <p>
	 * First all predecessor sets (with respect to a single symbol) are found and then for each such set the states are
	 * split from their equivalence classes.
	 * 
	 * @param ec
	 *            the splitter equivalence class
	 * @param iterator
	 *            the iterator abstracting from the letter type
	 * @param isInternal
	 *            true iff split is internal
	 */
	private void splitInternalOrCallPredecessors(final EquivalenceClass ec,
			final ITransitionIterator<LETTER, STATE> iterator, final boolean isInternal) {
		assert (isInternal && (iterator instanceof ShrinkNwa.InternalTransitionIterator)
				&& (ec.mIncomingInt != IncomingStatus.IN_WORKLIST))
				|| ((!isInternal) && ((iterator instanceof ShrinkNwa.CallTransitionIterator)
						&& (ec.mIncomingCall != IncomingStatus.IN_WORKLIST)));

		// create a hash map from letter to respective predecessor states
		final HashMap<LETTER, HashSet<STATE>> letter2states = new HashMap<>();
		for (final STATE state : ec.mStates) {
			iterator.nextState(state);
			while (iterator.hasNext()) {
				final LETTER letter = iterator.nextAndLetter();
				HashSet<STATE> predecessorSet = letter2states.get(letter);
				if (predecessorSet == null) {
					predecessorSet = new HashSet<>();
					letter2states.put(letter, predecessorSet);
				}
				predecessorSet.add(iterator.getPred());
			}
		}

		// remember that this equivalence class has no incoming transitions
		if (letter2states.isEmpty()) {
			if (isInternal) {
				ec.mIncomingInt = IncomingStatus.NONE;
			} else {
				ec.mIncomingCall = IncomingStatus.NONE;
			}
			if (STATISTICS) {
				++mNoIncomingTransitions;
			}
		} else {
			if (STATISTICS) {
				++mIncomingTransitions;
			}

			// split each map value (set of predecessor states)
			for (final HashSet<STATE> predecessorSet : letter2states.values()) {
				assert !predecessorSet.isEmpty();
				mPartition.splitEquivalenceClasses(predecessorSet);
			}
		}
	}

	/**
	 * This method implements the return split.
	 * <p>
	 * For each return symbol respectively first find the predecessor states (both linear and hierarchical). Then do the
	 * following first for the linear and then for the hierarchical states: Mark the simple splits, then find violations
	 * due to the neutral states and break ties on which states to split there.
	 */
	private void splitReturnPredecessors() {
		if (DEBUG2) {
			mLogger.debug("\nNEW RETURN SPLITTING ROUND");
		}

		final HashMap<STATE, HashSet<STATE>> lin2hier = splitReturnBackwardsAnalysis();

		HashMap<EquivalenceClass, HashSet<EquivalenceClass>> linEc2hierEc = splitReturnEcTranslation(lin2hier);

		splitReturnForwardsAnalysis(linEc2hierEc, true);

		while (!mSplitEcsReturn.isEmpty()) {
			assert assertSetProperty(mSplitEcsReturn);
			splitReturnExecute(mSplitEcsReturn);
			linEc2hierEc = splitReturnEcTranslation(lin2hier);
			mSplitEcsReturn = new LinkedList<>();
			splitReturnForwardsAnalysis(linEc2hierEc, true);
		}

		splitReturnForwardsAnalysis(linEc2hierEc, false);

		if (!mSplitEcsReturn.isEmpty()) {
			assert assertSetProperty(mSplitEcsReturn);
			splitReturnExecute(mSplitEcsReturn);
			mSplitEcsReturn = new LinkedList<>();
		}
	}

	/**
	 * This method finds all involved linear and hierarchical equivalence classes for all successor equivalence classes
	 * currently in the work list for the return split.
	 * 
	 * @return map linear state to hierarchical states
	 */
	private HashMap<STATE, HashSet<STATE>> splitReturnBackwardsAnalysis() {
		if (DEBUG2) {
			mLogger.debug("analyzing backwards");
		}
		final HashMap<STATE, HashSet<STATE>> lin2hier =
				new HashMap<>(computeHashCap(mPartition.mEquivalenceClasses.size()));

		// find all involved linear and hierarchical states
		while (mWorkListRet.hasNext()) {
			final EquivalenceClass succEc = mWorkListRet.next();
			boolean incomingReturns = false;

			for (final STATE succ : succEc.mStates) {
				final Iterator<IncomingReturnTransition<LETTER, STATE>> edges =
						mOperand.returnPredecessors(succ).iterator();
				if (edges.hasNext()) {
					incomingReturns = true;
					do {
						final IncomingReturnTransition<LETTER, STATE> edge = edges.next();
						final STATE lin = edge.getLinPred();
						HashSet<STATE> hiers = lin2hier.get(lin);
						if (hiers == null) {
							hiers = new HashSet<>();
							lin2hier.put(lin, hiers);
						}
						hiers.add(edge.getHierPred());
					} while (edges.hasNext());
				}
			}

			// no return transitions found, remember that
			if (!incomingReturns) {
				succEc.mIncomingRet = IncomingStatus.NONE;
				if (STATISTICS) {
					++mNoIncomingTransitions;
				}
			}

			if (DEBUG2) {
				mLogger.debug(
						" succEc: " + succEc.toStringShort() + " has " + (incomingReturns ? "" : "no ") + "returns");
			}
		}
		return lin2hier;
	}

	/**
	 * This method translates the mapping of linear to hierarchical states to a mapping of linear to hierarchical
	 * equivalence classes.
	 * 
	 * @param lin2hier
	 *            map linear state to hierarchical states
	 * @return map linear equivalence class to hierarchical equivalence classes
	 */
	private HashMap<EquivalenceClass, HashSet<EquivalenceClass>>
			splitReturnEcTranslation(final HashMap<STATE, HashSet<STATE>> lin2hier) {
		if (DEBUG2) {
			mLogger.debug("\ntranslating to ECs");
		}

		final HashMap<EquivalenceClass, HashSet<EquivalenceClass>> linEc2hierEcs =
				new HashMap<>(computeHashCap(lin2hier.size()));
		for (final Entry<STATE, HashSet<STATE>> entry : lin2hier.entrySet()) {
			final EquivalenceClass linEc = mPartition.mState2EquivalenceClass.get(entry.getKey());
			HashSet<EquivalenceClass> hierEcs = linEc2hierEcs.get(linEc);
			if (hierEcs == null) {
				hierEcs = new HashSet<>();
				linEc2hierEcs.put(linEc, hierEcs);
			}
			for (final STATE hier : entry.getValue()) {
				hierEcs.add(mPartition.mState2EquivalenceClass.get(hier));
			}
		}

		if (DEBUG2) {
			mLogger.debug("resulting map: " + linEc2hierEcs);
		}

		return linEc2hierEcs;
	}

	/**
	 * This method triggers for each given pair of linear and hierarchical equivalence classes the linear and the
	 * hierarchical return split.
	 * 
	 * @param linEc2hierEc
	 *            map linear EC to hierarchical EC
	 * @param linearAnalysis
	 *            analysis: true = linear, false = hierarchical
	 */
	private void splitReturnForwardsAnalysis(final HashMap<EquivalenceClass, HashSet<EquivalenceClass>> linEc2hierEc,
			final boolean linearAnalysis) {
		for (final Entry<EquivalenceClass, HashSet<EquivalenceClass>> entry : linEc2hierEc.entrySet()) {
			final EquivalenceClass linEc = entry.getKey();
			final boolean linEcSingleton = linEc.mStates.size() == 1;
			final HashSet<EquivalenceClass> hierEcs = entry.getValue();

			if (DEBUG2) {
				mLogger.debug("\nlinEc: " + linEc.toStringShort());
			}

			// get matrix
			Matrix matrix = linEc.mMatrix;
			if (matrix == null) {
				linEc.initializeMatrix(hierEcs);
				matrix = linEc.mMatrix;
			}
			if (matrix == mSingletonMatrix) {
				if (DEBUG2) {
					mLogger.debug(" ignoring matrix: " + matrix);
				}

				continue;
			}

			if (DEBUG2) {
				mLogger.debug("matrix: " + matrix);
			}

			final HashMap<STATE, HashMap<STATE, HashMap<LETTER, HashSet<STATE>>>> hier2lin2letter2succ =
					matrix.mHier2lin2letter2succ;

			for (final EquivalenceClass hierEc : hierEcs) {
				if (DEBUG2) {
					mLogger.debug(" hierEc: " + hierEc.toStringShort());
				}

				if (linEcSingleton && hierEc.mStates.size() == 1) {
					if (DEBUG2) {
						mLogger.debug("  ignoring singletons");
					}

					if (STATISTICS) {
						++mIgnoredReturnSingletons1x1;
					}

					continue;
				}

				/*
				 * find relevant rows (avoids duplicate computations for the hierarchical split)
				 */
				final ArrayList<MatrixRow> relevantRows = new ArrayList<>(hierEc.mStates.size());
				for (final STATE hier : hierEc.mStates) {
					final HashMap<STATE, HashMap<LETTER, HashSet<STATE>>> map = hier2lin2letter2succ.get(hier);
					if ((map != null) && (!map.isEmpty())) {
						relevantRows.add(new MatrixRow(hier, map));
					} else {
						if (DEBUG2) {
							mLogger.debug(" ignoring hier " + hier);
						}
					}
				}

				if (DEBUG2) {
					mLogger.debug(" relevant rows: " + relevantRows);
				}

				// linear states analysis
				if (linearAnalysis) {
					if (!linEcSingleton) {
						splitReturnAnalyzeLinear(hier2lin2letter2succ, linEc, relevantRows);
					}
				} else {
					// hierarchical states analysis
					if (relevantRows.size() > 1) {
						splitReturnAnalyzeHierarchical(hier2lin2letter2succ, hierEc, relevantRows);
					}
				}
			}
		}
	}

	/**
	 * This method checks and potentially triggers a linear return split.
	 * <p>
	 * TODO(nondeterminism) at most one successor for deterministic automata, offer improved version (no Set of STATE ,
	 * no Set of EquivalenceClass)?
	 * <p>
	 * TODO(ignoreMarked) ignore already marked pairs
	 * 
	 * @param hier2lin2letter2succ
	 *            map hier. to lin. to letter to succ. state
	 * @param linEc
	 *            linear equivalence class
	 * @param rows
	 *            matrix rows (hierarchical states)
	 */
	private void splitReturnAnalyzeLinear(
			final HashMap<STATE, HashMap<STATE, HashMap<LETTER, HashSet<STATE>>>> hier2lin2letter2succ,
			final EquivalenceClass linEc, final ArrayList<MatrixRow> rows) {
		if (DEBUG2) {
			mLogger.debug("-linear analysis");
		}

		for (final MatrixRow row : rows) {
			final HashMap<STATE, HashMap<LETTER, HashSet<STATE>>> lin2letter2succ = row.mLin2letter2succ;
			if (DEBUG2) {
				mLogger.debug(" hier " + row.mHier + " -> " + lin2letter2succ);
			}

			if (lin2letter2succ.size() == 1) {
				if (DEBUG2) {
					mLogger.debug("  only one entry, ignore");
				}

				continue;
			}

			final int size = computeHashCap(lin2letter2succ.size());
			final HashMap<HashMap<LETTER, HashSet<EquivalenceClass>>, HashSet<STATE>> letter2succEc2lin =
					new HashMap<>(size);
			final HashSet<STATE> noTransitions = new HashSet<>(size);
			for (final Entry<STATE, HashMap<LETTER, HashSet<STATE>>> entry : lin2letter2succ.entrySet()) {
				final STATE lin = entry.getKey();
				assert linEc.mStates.contains(lin);
				final HashMap<LETTER, HashSet<STATE>> letter2succ = entry.getValue();

				if (DEBUG2) {
					mLogger.debug("   lin: " + lin);
				}

				if (letter2succ == mDownStateMap) {
					if (DEBUG2) {
						mLogger.debug("   no transition, but DS");
					}

					noTransitions.add(lin);
					continue;
				}

				final HashMap<LETTER, HashSet<EquivalenceClass>> letter2succEc =
						new HashMap<>(computeHashCap(letter2succ.size()));
				for (final Entry<LETTER, HashSet<STATE>> innerEntry : letter2succ.entrySet()) {
					final LETTER letter = innerEntry.getKey();
					final HashSet<STATE> succs = innerEntry.getValue();

					final HashSet<EquivalenceClass> succEcs = new HashSet<>(computeHashCap(succs.size()));

					if (DEBUG2) {
						mLogger.debug("   letter: " + letter + ", succs: " + succs);
					}

					for (final STATE succ : succs) {
						succEcs.add(mPartition.mState2EquivalenceClass.get(succ));
					}

					letter2succEc.put(letter, succEcs);
				}

				HashSet<STATE> lins = letter2succEc2lin.get(letter2succEc);
				if (lins == null) {
					lins = new HashSet<>();
					letter2succEc2lin.put(letter2succEc, lins);
				}
				lins.add(lin);

				if (DEBUG2) {
					mLogger.debug("   adding: " + lin + " to " + letter2succEc);
				}
			}

			if (DEBUG2) {
				mLogger.debug("    receiving: " + letter2succEc2lin + " and {{DS}=" + noTransitions + "}");
			}

			if (!noTransitions.isEmpty()) {
				letter2succEc2lin.put(null, noTransitions);
			}

			if (letter2succEc2lin.size() <= 1) {
				if (DEBUG2) {
					mLogger.debug("    no linear split");
				}
			} else {
				if (DEBUG2) {
					mLogger.debug(
							"    mark linear split of " + linEc.toStringShort() + ": " + letter2succEc2lin.values());
				}

				linEc.markSplit(letter2succEc2lin.values());
			}
		}
	}

	/**
	 * This method checks and potentially triggers a hierarchical return split.
	 * <p>
	 * TODO(nondeterminism) at most one successor for deterministic automata, offer improved version (no Set of STATE,
	 * no Set of EquivalenceClass)?
	 * 
	 * @param hier2lin2letter2succ
	 *            map hier. to lin. to letter to succ. state
	 * @param hierEc
	 *            hierarchical equivalence class
	 * @param rows
	 *            matrix rows (hierarchical states)
	 */
	private void splitReturnAnalyzeHierarchical(
			final HashMap<STATE, HashMap<STATE, HashMap<LETTER, HashSet<STATE>>>> hier2lin2letter2succ,
			final EquivalenceClass hierEc, final ArrayList<MatrixRow> rows) {
		if (DEBUG2) {
			mLogger.debug("-hierarchical analysis");
		}

		final int size = rows.size();

		if (DEBUG2) {
			mLogger.debug("  rows remaining: " + size);
		}

		if (size <= 1) {
			if (DEBUG2) {
				mLogger.debug("   ignore");
			}

			return;
		}

		final int modSize = computeHashCap(size);
		final HashMap<HashMap<LETTER, HashSet<EquivalenceClass>>, HashSet<STATE>> letter2succEc2hier =
				new HashMap<>(modSize);
		final HashSet<STATE> noTransitions = new HashSet<>(modSize);
		final int hierEcModSize = computeHashCap(hierEc.mStates.size());

		// go through rows (each entry per row behaves the same)
		for (int i = 0; i < size; ++i) {
			final MatrixRow row = rows.get(i);
			final STATE hier = row.mHier;
			// choose the first entry in this row
			final HashMap<LETTER, HashSet<STATE>> letter2succ = row.mLin2letter2succ.values().iterator().next();

			if (DEBUG2) {
				mLogger.debug(" hier " + hier + " -> " + letter2succ);
			}

			if (letter2succ == mDownStateMap) {
				noTransitions.add(hier);
				continue;
			}

			// translate to map with equivalence class
			final HashMap<LETTER, HashSet<EquivalenceClass>> letter2succEc =
					new HashMap<>(computeHashCap(letter2succ.size()));
			for (final Entry<LETTER, HashSet<STATE>> entry : letter2succ.entrySet()) {
				final LETTER letter = entry.getKey();
				final HashSet<STATE> succs = entry.getValue();
				final HashSet<EquivalenceClass> succEcs = new HashSet<>(computeHashCap(succs.size()));
				for (final STATE succ : succs) {
					succEcs.add(mPartition.mState2EquivalenceClass.get(succ));
				}
				letter2succEc.put(letter, succEcs);
			}
			if (DEBUG2) {
				mLogger.debug("  letter2succEc: " + letter2succEc);
			}

			HashSet<STATE> hiers = letter2succEc2hier.get(letter2succEc);
			if (hiers == null) {
				hiers = new HashSet<>(hierEcModSize);
				letter2succEc2hier.put(letter2succEc, hiers);
			}
			hiers.add(hier);
		}

		if (DEBUG2) {
			mLogger.debug("    receiving: " + letter2succEc2hier + " and {{DS}=" + noTransitions + "}");
		}

		if (!noTransitions.isEmpty()) {
			letter2succEc2hier.put(null, noTransitions);
		}

		if (letter2succEc2hier.size() > 1) {
			if (DEBUG2) {
				mLogger.debug("    mark hierarchical split of " + hierEc.toStringShort() + ": "
						+ letter2succEc2hier.values());
			}

			hierEc.markSplit(letter2succEc2hier.values());
		}
	}

	/**
	 * This method executes the return splits for all passed equivalence classes. The input has information of which
	 * states must be separated. The goal is to come up with a splitting that satisfies the separations.
	 * <p>
	 * The general solution is algorithmically hard, so here the following heuristic is used: The general rule is to
	 * assign a state to an existing group of states if possible. If there is more than one possible group, the first
	 * one found is chosen.
	 *
	 * @param splitEquivalenceClasses
	 *            split equivalence classes
	 */
	private void splitReturnExecute(final Collection<EquivalenceClass> splitEquivalenceClasses) {
		if (DEBUG2) {
			mLogger.debug("\n-- executing return splits");
		}

		if (STATISTICS) {
			mReturnSeparateTime -= new GregorianCalendar().getTimeInMillis();
		}

		for (final EquivalenceClass oldEc : splitEquivalenceClasses) {
			final HashMap<STATE, HashSet<STATE>> state2separatedSet = oldEc.mState2SeparatedSet;
			assert state2separatedSet != null;

			if (DEBUG2) {
				mLogger.debug(oldEc + " : " + state2separatedSet);
			}

			// map: color to associated states and blocked states
			int statesRemaining = oldEc.mStates.size();
			final ArrayList<ColorSet> colorSets = new ArrayList<>(statesRemaining);

			// for each state find a color
			outer: for (final Entry<STATE, HashSet<STATE>> stateEntry : state2separatedSet.entrySet()) {
				final STATE state = stateEntry.getKey();
				final HashSet<STATE> separatedSet = stateEntry.getValue();

				assert (oldEc.mStates.contains(state)) && (separatedSet != null);

				// find fitting color
				for (int i = 0; i < colorSets.size(); ++i) {
					// found a fitting color
					final ColorSet colorSet = colorSets.get(i);
					if (!colorSet.mBlocked.contains(state)) {
						colorSet.mContent.add(state);
						colorSet.mBlocked.addAll(separatedSet);
						--statesRemaining;
						continue outer;
					}
				}

				// no color available, use a new one
				colorSets.add(new ColorSet(statesRemaining, state, separatedSet));
				--statesRemaining;
			}

			/*
			 * States without any separation information behave like the states in the group that remains without a
			 * split.
			 */
			assert statesRemaining >= 0;

			if (DEBUG2) {
				mLogger.debug("colorSets: " + colorSets);
			}

			/*
			 * If there are no states without any group preference, keep the biggest set from splitting. Else keep the
			 * smallest set from splitting, since those states will stay there. This is to reduce the size of the
			 * equivalence classes.
			 * 
			 * NOTE: This typically has nearly no practical influence.
			 */
			int remainingColor = 0;
			if (statesRemaining == 0) {
				// find maximum set
				int maxSize = colorSets.get(0).mContent.size();
				for (int i = colorSets.size() - 1; i > 0; --i) {
					final int size = colorSets.get(i).mContent.size();
					if (size > maxSize) {
						maxSize = size;
						remainingColor = i;
					}
				}
			} else {
				// find minimum set
				int minSize = colorSets.get(0).mContent.size();
				for (int i = colorSets.size() - 1; i > 0; --i) {
					final int size = colorSets.get(i).mContent.size();
					if (size < minSize) {
						minSize = size;
						remainingColor = i;
					}
				}
			}

			// finally split the equivalence class
			int colorIndex = colorSets.size();
			while (true) {
				if (--colorIndex == remainingColor) {
					--colorIndex;
				}
				if (colorIndex < 0) {
					break;
				}

				final EquivalenceClass newEc = mPartition.addEcReturn(colorSets.get(colorIndex).mContent, oldEc);

				if (STATISTICS) {
					++mSplitsWithChange;
				}

				if (DEBUG2) {
					mLogger.debug("new equivalence class: " + newEc.toStringShort());
				}
			}

			// reset separation mapping
			oldEc.mState2SeparatedSet = null;
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
			mLogger.debug("L succEc " + succEc.toStringShort());
		}

		final HashMap<EquivalenceClass, HashSet<IncomingReturnTransition<LETTER, STATE>>> linEc2trans =
				splitReturnFindTransitionsAlt(succEc);

		if (linEc2trans.isEmpty()) {
			succEc.mIncomingRet = IncomingStatus.NONE;
			return;
		}

		if (DEBUG4) {
			mLogger.debug("linEc2trans " + linEc2trans);
		}

		for (final Entry<EquivalenceClass, HashSet<IncomingReturnTransition<LETTER, STATE>>> entry : linEc2trans
				.entrySet()) {
			splitReturnLinearAltHelper(entry.getKey(), entry.getValue());

		}
	}

	/**
	 * This method finds the transitions for the alternative linear return split.
	 * 
	 * @param succEc
	 *            successor equivalence class
	 * @return map linear equivalence class to return transitions
	 */
	private HashMap<EquivalenceClass, HashSet<IncomingReturnTransition<LETTER, STATE>>>
			splitReturnFindTransitionsAlt(final EquivalenceClass succEc) {
		final HashMap<EquivalenceClass, HashSet<IncomingReturnTransition<LETTER, STATE>>> linEc2trans = new HashMap<>();
		final HashMap<STATE, EquivalenceClass> state2ec = mPartition.mState2EquivalenceClass;

		for (final STATE succ : succEc.mStates) {
			for (final IncomingReturnTransition<LETTER, STATE> edge : mOperand.returnPredecessors(succ)) {
				final EquivalenceClass linEc = state2ec.get(edge.getLinPred());
				HashSet<IncomingReturnTransition<LETTER, STATE>> edges = linEc2trans.get(linEc);
				if (edges == null) {
					edges = new HashSet<>();
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
	 * @param linEc
	 *            linear equivalence class
	 * @param transitions
	 *            return transitions
	 */
	private void splitReturnLinearAltHelper(final EquivalenceClass linEc,
			final Collection<IncomingReturnTransition<LETTER, STATE>> transitions) {
		if (DEBUG4) {
			mLogger.debug("linEc " + linEc + ", transitions " + transitions);
		}

		final Set<STATE> linStates = linEc.mStates;
		final int linEcSize = linStates.size();
		if (linEcSize == 1) {
			return;
		}

		final HashSet<STATE> linsVisited = new HashSet<>(computeHashCap(linEcSize));
		final HashMap<STATE, HashMap<LETTER, HashSet<STATE>>> hier2letters2lins =
				new HashMap<>(computeHashCap(transitions.size()));

		linEc.mState2SeparatedSet = new HashMap<>(computeHashCap(linEcSize));

		// find all linear predecessors
		for (final IncomingReturnTransition<LETTER, STATE> trans : transitions) {
			final STATE hier = trans.getHierPred();
			HashMap<LETTER, HashSet<STATE>> letter2lins = hier2letters2lins.get(hier);
			if (letter2lins == null) {
				letter2lins = new HashMap<>();
				hier2letters2lins.put(hier, letter2lins);
			}
			final LETTER letter = trans.getLetter();
			HashSet<STATE> lins = letter2lins.get(letter);
			if (lins == null) {
				lins = new HashSet<>();
				letter2lins.put(letter, lins);
			}
			final STATE lin = trans.getLinPred();
			lins.add(lin);
			linsVisited.add(lin);
		}

		if (DEBUG4) {
			mLogger.debug(" hier2letters2lins " + hier2letters2lins);
			mLogger.debug(" linsVisited " + linsVisited);
		}

		// (linear) states not visited
		final ArrayList<STATE> linsUnvisited = new ArrayList<>(linEcSize - linsVisited.size());
		for (final STATE lin : linStates) {
			if (!linsVisited.contains(lin)) {
				linsUnvisited.add(lin);
			}
		}

		// mark: all visited from each other and from all non-visited with DS
		for (final Entry<STATE, HashMap<LETTER, HashSet<STATE>>> outerEntry : hier2letters2lins.entrySet()) {
			final STATE hier = outerEntry.getKey();

			if (DEBUG4) {
				mLogger.debug("  hier " + hier);
			}

			// compute sets of DS/no DS states
			final int modSize = computeHashCap(linEcSize - linsVisited.size());
			final HashSet<STATE> noDsStates = new HashSet<>(modSize);
			final HashSet<STATE> dsStates = new HashSet<>(modSize);
			for (final STATE lin : linsUnvisited) {
				if (mDoubleDecker.isDoubleDecker(lin, hier)) {
					dsStates.add(lin);

					// mark returns from non-returns
					for (final STATE linPos : linsVisited) {
						linEc.markPair(lin, linPos);
					}
				} else {
					noDsStates.add(lin);
				}
			}

			if (DEBUG4) {
				mLogger.debug("  dsStates " + dsStates);
				mLogger.debug("  noDsStates " + noDsStates);
			}

			for (final Entry<LETTER, HashSet<STATE>> innerEntry : outerEntry.getValue().entrySet()) {
				final HashSet<STATE> lins = innerEntry.getValue();

				if (DEBUG4) {
					mLogger.debug("  lins " + lins);
				}

				if (lins.size() == linsVisited.size()) {
					if (DEBUG4) {
						mLogger.debug("   ignore");
					}

					continue;
				}

				for (final STATE lin : linsVisited) {
					if ((!lins.contains(lin)) && (mDoubleDecker.isDoubleDecker(lin, hier))) {
						if (DEBUG4) {
							mLogger.debug("   later split");
						}

						// mark different returns
						for (final STATE linPos : lins) {
							linEc.markPair(lin, linPos);
						}
					}
				}
			}
		}

		if (linEc.mState2SeparatedSet.size() > 0) {
			if (DEBUG4) {
				mLogger.debug(" SPLIT");
			}

			mSplitEcsReturn.add(linEc);
			splitReturnExecute(mSplitEcsReturn);
			mSplitEcsReturn = new LinkedList<>();
		} else {
			if (DEBUG4) {
				mLogger.debug(" NO SPLIT");
			}
		}
		linEc.mState2SeparatedSet = null;
	}

	/**
	 * This method is an alternative hierarchical return split.
	 */
	private void splitReturnHierAlt() {
		EquivalenceClass succEc;
		while (true) {
			succEc = mWorkListRetHier.next();
			if (succEc.mIncomingRet == IncomingStatus.NONE) {
				if (!mWorkListRetHier.hasNext()) {
					return;
				}
			} else {
				break;
			}
		}

		if (DEBUG4) {
			mLogger.debug("H succEc " + succEc.toStringShort());
		}

		final HashMap<EquivalenceClass, HashSet<EquivalenceClass>> hierEc2linEcs =
				splitReturnFindOutgoingTransitions(succEc);

		if (hierEc2linEcs.isEmpty()) {
			succEc.mIncomingRet = IncomingStatus.NONE;
			return;
		}

		if (DEBUG4) {
			mLogger.debug("linEc2hierEcs " + hierEc2linEcs);
		}

		for (final Entry<EquivalenceClass, HashSet<EquivalenceClass>> entry : hierEc2linEcs.entrySet()) {
			splitReturnHierAltHelper(entry.getKey(), entry.getValue());
		}
	}

	/**
	 * This method finds the transitions for the alternative hierarchical return split.
	 * 
	 * @param succEc
	 *            successor equivalence class
	 * @return map hierarchical equivalence class to linear equivalence class
	 */
	private HashMap<EquivalenceClass, HashSet<EquivalenceClass>>
			splitReturnFindOutgoingTransitions(final EquivalenceClass succEc) {
		final HashMap<EquivalenceClass, HashSet<EquivalenceClass>> hierEc2linEcs = new HashMap<>();
		final HashMap<STATE, EquivalenceClass> state2ec = mPartition.mState2EquivalenceClass;

		for (final STATE succ : succEc.mStates) {
			for (final IncomingReturnTransition<LETTER, STATE> edge : mOperand.returnPredecessors(succ)) {
				final EquivalenceClass hierEc = state2ec.get(edge.getHierPred());
				HashSet<EquivalenceClass> linEcs = hierEc2linEcs.get(hierEc);
				if (linEcs == null) {
					linEcs = new HashSet<>();
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
	 * @param hierEc
	 *            hierarchical equivalence class
	 * @param linEcs
	 *            linear equivalence classes
	 */
	private void splitReturnHierAltHelper(final EquivalenceClass hierEc, final HashSet<EquivalenceClass> linEcs) {
		if (DEBUG4) {
			mLogger.debug("hierEc " + hierEc + ", linEcs " + linEcs);
		}

		final Set<STATE> hierStates = hierEc.mStates;
		final int hierEcSize = hierStates.size();
		if (hierEcSize == 1) {
			if (DEBUG4) {
				mLogger.debug("   ignore");
			}

			return;
		}

		hierEc.mState2SeparatedSet = new HashMap<>(computeHashCap(hierEcSize));
		final HashMap<STATE, EquivalenceClass> state2ec = mPartition.mState2EquivalenceClass;

		for (final EquivalenceClass linEc : linEcs) {
			final HashMap<HashMap<EquivalenceClass, HashSet<LETTER>>, HashSet<STATE>> succEc2letter2hiers =
					new HashMap<>();

			for (final STATE hier : hierStates) {
				final HashMap<EquivalenceClass, HashSet<LETTER>> succEc2letters =
						new HashMap<>(computeHashCap(hierEcSize));

				inner: for (final STATE lin : linEc.mStates) {
					if (mDoubleDecker.isDoubleDecker(lin, hier)) {
						final Iterator<OutgoingReturnTransition<LETTER, STATE>> edges =
								mOperand.returnSuccessorsGivenHier(lin, hier).iterator();
						if (edges.hasNext()) {
							do {
								final OutgoingReturnTransition<LETTER, STATE> edge = edges.next();
								final EquivalenceClass succEc = state2ec.get(edge.getSucc());
								HashSet<LETTER> letters = succEc2letters.get(succEc);
								if (letters == null) {
									letters = new HashSet<>();
									succEc2letters.put(succEc, letters);
								}
								letters.add(edge.getLetter());
							} while (edges.hasNext());
							break inner;
						} else {
							succEc2letters.put(mNegativeClass, null);
							break inner;
						}
					}
				}

				assert !succEc2letters.isEmpty();
				HashSet<STATE> hiers = succEc2letter2hiers.get(succEc2letters);
				if (hiers == null) {
					hiers = new HashSet<>();
					succEc2letter2hiers.put(succEc2letters, hiers);
				}
				hiers.add(hier);
			}

			if (succEc2letter2hiers.size() > 1) {
				hierEc.markSplit(succEc2letter2hiers.values());
			}
		}

		if (hierEc.mState2SeparatedSet.size() > 0) {
			if (DEBUG4) {
				mLogger.debug(" SPLIT");
			}

			mSplitEcsReturn.add(hierEc);
			splitReturnExecute(mSplitEcsReturn);
			mSplitEcsReturn = new LinkedList<>();
		} else {
			if (DEBUG4) {
				mLogger.debug(" NO SPLIT");
			}
		}
		hierEc.mState2SeparatedSet = null;
	}

	/**
	 * This method implements an optional first linear return split before considering the real return split.
	 * <p>
	 * NOTE: The split is not perfect in the sense that once an equivalence class has been split, its return
	 * predecessors are not reconsidered. This could be added, but is currently not the case, since this is only meant
	 * as a preprocessing step.
	 */
	private void splitReturnPredecessorsFirstTime() {
		if (DEBUG2) {
			mLogger.debug("\nNEW RETURN SPLITTING ROUND");
		}

		if (DEBUG3) {
			if (mPartition.mEquivalenceClasses.size() == mWorkListRet.mQueue.size()) {
				mLogger.debug("first return split, starting with " + mPartition.mEquivalenceClasses.size() + " ECs");
			}
		}

		if (STATISTICS) {
			mReturnFirstTime -= new GregorianCalendar().getTimeInMillis();
		}

		EquivalenceClass linEc;
		HashSet<STATE> hiers;
		final Set<Entry<EquivalenceClass, HashSet<STATE>>> entrySet = mFirstReturnLin2Hiers.entrySet();

		while (true) {
			// continue from last time
			if (!entrySet.isEmpty()) {
				assert entrySet.size() == 1;
				final Entry<EquivalenceClass, HashSet<STATE>> entry = entrySet.iterator().next();
				linEc = entry.getKey();
				hiers = entry.getValue();
			} else if (mWorkListRet.hasNext()) {
				linEc = mWorkListRet.next();
			} else {
				break;
			}

			if (DEBUG3) {
				mLogger.debug("linEc size: " + linEc.mStates.size());
			}

			// singleton equivalence classes are ignored
			if (linEc.mStates.size() == 1) {
				if (DEBUG3) {
					mLogger.debug(" ignoring");
				}

				continue;
			}

			// analyse linear equivalence class
			hiers = splitReturnPredecessorsFirstTimeRepeat(linEc, new HashSet<STATE>());

			while ((hiers != null) && (!hiers.isEmpty())) {
				// new internal and call splits available, prefer them
				if (mWorkListIntCall.hasNext()) {
					mFirstReturnLin2Hiers = new HashMap<>(2);
					mFirstReturnLin2Hiers.put(linEc, hiers);
					break;
				}

				// singleton equivalence classes are ignored
				if (linEc.mStates.size() == 1) {
					if (DEBUG3) {
						mLogger.debug(" ignoring");
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
			mLogger.debug("first return split executed, now having " + mPartition.mEquivalenceClasses.size() + " ECs");
		}
	}

	/**
	 * This method is repeated in the loop of the optional first return split.
	 * 
	 * @param linEc
	 *            the linear equivalence class
	 * @param oldHiers
	 *            old hierarchical predecessors
	 * @return hierarchical states visited so far
	 */
	private HashSet<STATE> splitReturnPredecessorsFirstTimeRepeat(final EquivalenceClass linEc,
			HashSet<STATE> oldHiers) {
		// analyse linear equivalence class
		oldHiers = splitReturnPredecessorsFirstTimeAnalyze(linEc, oldHiers);

		// if there are reasons for a split, execute it
		if (mSplitEcsReturn.size() == 1) {
			if (DEBUG3) {
				mLogger.debug("splitting EC of size " + linEc.mStates.size());
			}

			assert mSplitEcsReturn.get(0) == linEc;
			splitReturnExecute(mSplitEcsReturn);
			mSplitEcsReturn.clear();
		} else {
			assert mSplitEcsReturn.isEmpty();
		}
		return oldHiers;
	}

	/**
	 * This method checks whether the given equivalence class must be split linearly. If so, the states are marked.
	 * <p>
	 * This is a mixture of a full and a random split, since only a fixed number of hierarchical predecessor states is
	 * considered at one time. If there are more of them, they are considered in a later iteration.
	 * 
	 * @param linEc
	 *            the linear equivalence class
	 * @param oldHiers
	 *            old hierarchical predecessors
	 * @return hierarchical states visited so far
	 */
	private HashSet<STATE> splitReturnPredecessorsFirstTimeAnalyze(final EquivalenceClass linEc,
			HashSet<STATE> oldHiers) {
		final Set<STATE> lins = linEc.mStates;

		// collect all relevant hierarchical predecessors
		final HashSet<STATE> newHiers = new HashSet<>();
		boolean broke = oldHiers.isEmpty();
		outer: for (final STATE lin : lins) {
			for (final OutgoingReturnTransition<LETTER, STATE> edge : mOperand.returnSuccessors(lin)) {
				final STATE hier = edge.getHierPred();
				if (oldHiers.add(hier)) {
					newHiers.add(hier);
					// fixed number: 150
					if (newHiers.size() == HIER_PRED_MAX_SIZE) {
						broke = true;
						break outer;
					}
				}
			}
		}
		if (!broke) {
			oldHiers = null;
		}

		final int modSize = computeHashCap(lins.size());
		for (final STATE hier : newHiers) {
			final HashMap<HashMap<LETTER, HashSet<STATE>>, HashSet<STATE>> trans2lin = new HashMap<>(modSize);
			final HashSet<STATE> noTransitions = new HashSet<>(modSize);
			for (final STATE lin : lins) {
				if (!mDoubleDecker.isDoubleDecker(lin, hier)) {
					continue;
				}

				final Iterator<OutgoingReturnTransition<LETTER, STATE>> edges =
						mOperand.returnSuccessorsGivenHier(lin, hier).iterator();
				if (edges.hasNext()) {
					final HashMap<LETTER, HashSet<STATE>> transitions = new HashMap<>();
					do {
						final OutgoingReturnTransition<LETTER, STATE> edge = edges.next();
						final LETTER letter = edge.getLetter();
						HashSet<STATE> succs = transitions.get(letter);
						if (succs == null) {
							succs = new HashSet<>();
							transitions.put(letter, succs);
						}
						succs.add(edge.getSucc());
					} while (edges.hasNext());

					HashSet<STATE> otherLins = trans2lin.get(transitions);
					if (otherLins == null) {
						otherLins = new HashSet<>();
						trans2lin.put(transitions, otherLins);
					}
					otherLins.add(lin);
				} else {
					noTransitions.add(lin);
				}
			}

			if (!noTransitions.isEmpty()) {
				trans2lin.put(null, noTransitions);
			}
			if (trans2lin.size() > 1) {
				linEc.markSplit(trans2lin.values());
			}
		}

		return oldHiers;
	}

	@SuppressWarnings("unchecked")
	private void splitReturnExecuteOld(final Collection<EquivalenceClass> splitEquivalenceClasses) {
		if (DEBUG2) {
			mLogger.debug("\n-- executing return splits");
		}

		long time;
		if (STATISTICS) {
			time = new GregorianCalendar().getTimeInMillis();
		}

		for (final EquivalenceClass oldEc : splitEquivalenceClasses) {
			final HashMap<STATE, HashSet<STATE>> state2separatedSet = oldEc.mState2SeparatedSet;
			assert state2separatedSet != null;

			if (DEBUG2) {
				mLogger.debug(oldEc + " : " + state2separatedSet);
			}

			// mapping: state to associated color
			final HashMap<STATE, Integer> state2color = new HashMap<>(computeHashCap(oldEc.mStates.size()));
			// current number of colors
			int colors = 0;

			for (final Entry<STATE, HashSet<STATE>> entry : state2separatedSet.entrySet()) {
				final STATE state = entry.getKey();
				final HashSet<STATE> separatedSet = entry.getValue();

				assert (oldEc.mStates.contains(state)) && (separatedSet != null);

				// first color can be directly assigned
				if (colors == 0) {
					state2color.put(state, 0);
					++colors;
				} else {
					// find fitting color or use a new one
					final HashSet<Integer> blockedColors = new HashSet<>(computeHashCap(colors));

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
					} else {
						// at least one color available
						assert blockedColors.size() < colors;
						int color = 0;
						while (true) {
							assert color <= colors;
							if (!blockedColors.contains(color)) {
								state2color.put(state, color);
								break;
							}
							++color;
						}
					}
				}
			}
			assert colors > 1;

			// index 0 is ignored
			final HashSet<STATE>[] newEcs = new HashSet[colors];
			for (int i = colors - 1; i > 0; --i) {
				newEcs[i] = new HashSet<>();
			}
			for (final Entry<STATE, Integer> entry : state2color.entrySet()) {
				final int color = entry.getValue();
				if (color > 0) {
					newEcs[color].add(entry.getKey());
				}
			}

			if (DEBUG2) {
				mLogger.debug("state2color: " + state2color);
			}

			// finally split the equivalence class
			for (int i = newEcs.length - 1; i > 0; --i) {
				final HashSet<STATE> newStates = newEcs[i];
				final EquivalenceClass newEc = mPartition.addEcReturn(newStates, oldEc);

				if (STATISTICS) {
					++mSplitsWithChange;
				}

				if (DEBUG2) {
					mLogger.debug("new equivalence class: " + newEc.toStringShort());
				}
			}

			// reset separation mapping
			oldEc.mState2SeparatedSet = null;
		}

		if (STATISTICS) {
			time = new GregorianCalendar().getTimeInMillis() - time;
			mReturnSeparateTime += time;
		}
	}

	/**
	 * This method randomly splits the given equivalence class.
	 * <p>
	 * If it has outgoing call transitions, it is split into equally sized blocks of states.
	 * <p>
	 * Otherwise (without any outgoing call transitions) it keeps states with no outgoing return transitions together,
	 * since these states will never take part in any matrix and hence can be kept together.
	 * 
	 * @param ec
	 *            the equivalence class
	 */
	private void splitRandom(final EquivalenceClass ec) {
		if (mOperand.callSuccessors(ec.mStates.iterator().next()).iterator().hasNext()) {
			splitRandomEqual(ec);
		} else {
			splitRandomReturns(ec);
		}
	}

	/**
	 * This method randomly splits an equivalence class into equally sized blocks of states.
	 * 
	 * @param ec
	 *            the equivalence class
	 */
	private void splitRandomEqual(final EquivalenceClass ec) {
		final Set<STATE> oldStates = ec.mStates;
		final int size = computeHashCap(mTreshold);
		while (oldStates.size() > mTreshold) {
			final HashSet<STATE> newStates = new HashSet<>(size);
			int index = mTreshold;
			for (final STATE state : oldStates) {
				newStates.add(state);
				if (--index == 0) {
					mPartition.addEcReturn(newStates, ec);
					break;
				}
			}
		}
	}

	/**
	 * This method randomly splits an equivalence class into equally sized blocks of states, with one exception: It
	 * keeps states without any outgoing return transitions together.
	 * 
	 * @param ec
	 *            the equivalence class
	 */
	private void splitRandomReturns(final EquivalenceClass ec) {
		final Set<STATE> oldStates = ec.mStates;
		final int size = computeHashCap(mTreshold);
		final LinkedList<HashSet<STATE>> newClasses = new LinkedList<>();

		HashSet<STATE> returns = new HashSet<>(size);
		for (final STATE state : oldStates) {
			if (mOperand.returnSuccessors(state).iterator().hasNext()) {
				returns.add(state);
				if (returns.size() == mTreshold) {
					newClasses.add(returns);
					returns = new HashSet<>(size);
				}
			}
		}
		if (!returns.isEmpty()) {
			newClasses.add(returns);
		} else if (newClasses.isEmpty()) {
			return;
		}

		int numberOfStates = oldStates.size();
		for (final HashSet<STATE> states : newClasses) {
			assert !states.isEmpty();
			numberOfStates -= states.size();

			// no state without return transitions, do not split last class
			if (numberOfStates == 0) {
				break;
			}

			mPartition.addEcReturn(states, ec);
		}
	}

	/**
	 * For each remaining equivalence class create a new state. Also remove all other objects references.
	 * 
	 * @param addMapping
	 *            true iff mapping old to new state is needed
	 */
	private void constructAutomaton(final boolean addMapping) {
		if (DEBUG) {
			mLogger.info("finished splitting, constructing result");
		}

		mPartition.markInitials();

		// construct result with library method
		constructResultFromPartition(mPartition, addMapping);

		// clean up
		if (DEBUG) {
			mLogger.info("finished construction");
			mLogger.info(mPartition);
		}
		mPartition = null;
		mWorkListIntCall = null;
		mWorkListRet = null;
	}

	// --- [end] main methods --- //

	/**
	 * This method checks that the states in each equivalence class initially passed in the constructor are all either
	 * final or non-final.
	 *
	 * @param equivalenceClasses
	 *            partition passed in constructor
	 * @return true iff equivalence classes respect final status of states
	 */
	private boolean assertStatesSeparation(final Iterable<Set<STATE>> equivalenceClasses) {
		for (final Set<STATE> equivalenceClass : equivalenceClasses) {
			final Iterator<STATE> it = equivalenceClass.iterator();
			assert it.hasNext() : "Empty equivalence classes should be avoided.";
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
	 * This method checks the assertion that a given list contains an element only once.
	 * 
	 * @param <T>
	 *            type parameter
	 * @param list
	 *            the list
	 * @return true iff each element is contained only once
	 */
	private <T> boolean assertSetProperty(final List<T> list) {
		final HashSet<T> set = new HashSet<>(computeHashCap(list.size()));
		set.addAll(list);
		return set.size() == list.size();
	}

	/**
	 * This method does an extra split with outgoing transitions for internal and call symbols at the beginning. This is
	 * totally fine, since these splits would occur later anyway. The reason for this split overhead is that the regular
	 * splitting starts with smaller equivalence classes where less states and transitions have to be considered.
	 *
	 * @param finals
	 *            the final states
	 * @param nonfinals
	 *            the non-final states
	 */
	private void splitOutgoing(final HashSet<STATE> finals, final HashSet<STATE> nonfinals) {
		HashSet<STATE> states = finals;

		for (int i = 0; i < 2; ++i) {
			if (states.isEmpty()) {
				continue;
			}

			final HashMap<Collection<LETTER>, Collection<STATE>> callSplit = splitOutgoingHelper(states, mOutCall);
			for (final Collection<STATE> callStates : callSplit.values()) {
				final HashMap<Collection<LETTER>, Collection<STATE>> internalSplit =
						splitOutgoingHelper(callStates, mOutInternal);

				// split states
				for (final Collection<STATE> newStates : internalSplit.values()) {
					assert (!newStates.isEmpty()) && (newStates instanceof HashSet<?>);
					mPartition.addEcInitialization((HashSet<STATE>) newStates);
				}
			}

			states = nonfinals;
		}
	}

	/**
	 * This is a helper method that sets up data structures for splits by outgoing transitions.
	 *
	 * @param states
	 *            collection of states
	 * @param helper
	 *            helper object to abstract from internal and call symbols
	 * @return map from collection of letters to states with such symbols
	 */
	private HashMap<Collection<LETTER>, Collection<STATE>> splitOutgoingHelper(final Collection<STATE> states,
			final IOutgoingHelper<LETTER, STATE> helper) {
		final HashMap<Collection<LETTER>, Collection<STATE>> letterSet2stateSet =
				new HashMap<>(computeHashCap(helper.size()));

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

	@Override
	protected Pair<Boolean, String> checkResultHelper(final IMinimizationCheckResultStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		return checkLanguageEquivalence(stateFactory);
	}

	/**
	 * This enum is used to tell for an equivalence class whether it contains incoming transitions. Since it is
	 * expensive to compute this each time, only the answer "no" is correct. This status is inherited by the two
	 * resulting equivalence classes after a split. The idea is to not insert such equivalence classes in the work list,
	 * for which it is known that there are no incoming transitions. The status is updated as a byproduct after the
	 * search for transitions.
	 */
	private enum IncomingStatus {
		/** Unknown whether there are incoming transitions. */
		UNKNOWN,

		/** Equivalence class is in work list. */
		IN_WORKLIST,

		/** There are no incoming transitions. */
		NONE
	}

	/**
	 * A transition iterator is used for splitting internal and call predecessors.
	 *
	 * @param <STATE>
	 *            state type
	 * @param <LETTER>
	 *            letter type
	 */
	private interface ITransitionIterator<LETTER, STATE> {
		/**
		 * A new successor state is considered.
		 *
		 * @param state
		 *            the successor state
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
		 * @return The predecessor state.
		 */
		STATE getPred();
	}

	/**
	 * This is the implementation for internal transitions.
	 */
	private class InternalTransitionIterator implements ITransitionIterator<LETTER, STATE> {
		// iterator of the operand
		private Iterator<IncomingInternalTransition<LETTER, STATE>> mIterator;
		// current transition
		private IncomingInternalTransition<LETTER, STATE> mTransition;

		@Override
		public void nextState(final STATE state) {
			mIterator = mOperand.internalPredecessors(state).iterator();
		}

		@Override
		public STATE getPred() {
			return mTransition.getPred();
		}

		@Override
		public LETTER nextAndLetter() {
			mTransition = mIterator.next();
			return mTransition.getLetter();
		}

		@Override
		public boolean hasNext() {
			return mIterator.hasNext();
		}
	}

	/**
	 * This is the implementation for call transitions.
	 */
	private class CallTransitionIterator implements ITransitionIterator<LETTER, STATE> {
		// iterator of the operand
		private Iterator<IncomingCallTransition<LETTER, STATE>> mIterator;
		// current transition
		private IncomingCallTransition<LETTER, STATE> mTransition;

		@Override
		public void nextState(final STATE state) {
			mIterator = mOperand.callPredecessors(state).iterator();
		}

		@Override
		public LETTER nextAndLetter() {
			mTransition = mIterator.next();
			return mTransition.getLetter();
		}

		@Override
		public STATE getPred() {
			return mTransition.getPred();
		}

		@Override
		public boolean hasNext() {
			return mIterator.hasNext();
		}
	}

	/**
	 * This interface is used for the outgoing split at the beginning to abstract from whether internal or call symbols
	 * are considered.
	 * 
	 * @param <LETTER>
	 *            letter type
	 * @param <STATE>
	 *            state type
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
		 * @param state
		 *            state to consider
		 * @return all outgoing letters
		 */
		Set<LETTER> letters(final STATE state);

		/**
		 * This method returns a new collection. This is for efficiency reasons, since first only a list is needed,
		 * where later a set is needed.
		 *
		 * @return new collection
		 */
		Collection<STATE> newCollection();

		/**
		 * This method only checks that the symbols are correctly returned by the API.
		 *
		 * @param state
		 *            state to consider
		 * @return true iff symbols are correct
		 */
		boolean assertLetters(final STATE state);
	}

	/**
	 * This is the implementation for the outgoing internal split helper.
	 */
	private class OutgoingHelperInternal implements IOutgoingHelper<LETTER, STATE> {
		@Override
		public int size() {
			return mOperand.getVpAlphabet().getInternalAlphabet().size();
		}

		@Override
		public Set<LETTER> letters(final STATE state) {
			assert assertLetters(state);

			return mOperand.lettersInternal(state);
		}

		@Override
		public Collection<STATE> newCollection() {
			return new HashSet<>();
		}

		@Override
		public boolean assertLetters(final STATE state) {
			final Collection<LETTER> model = mOperand.lettersInternal(state);

			final HashSet<LETTER> checker = new HashSet<>(computeHashCap(model.size()));
			final Iterator<OutgoingInternalTransition<LETTER, STATE>> it =
					mOperand.internalSuccessors(state).iterator();
			while (it.hasNext()) {
				checker.add(it.next().getLetter());
			}

			if (checker.size() != model.size()) {
				return false;
			}
			for (final LETTER letter : model) {
				if (!checker.contains(letter)) {
					return false;
				}
			}

			return true;
		}
	}

	/**
	 * This is the implementation for the alternative call split helper.
	 */
	private class OutgoingHelperCall implements IOutgoingHelper<LETTER, STATE> {
		@Override
		public int size() {
			return mOperand.getVpAlphabet().getCallAlphabet().size();
		}

		@Override
		public Set<LETTER> letters(final STATE state) {
			assert assertLetters(state);

			return mOperand.lettersCall(state);
		}

		@Override
		public Collection<STATE> newCollection() {
			return new LinkedList<>();
		}

		@Override
		public boolean assertLetters(final STATE state) {
			final Collection<LETTER> model = mOperand.lettersCall(state);

			final HashSet<LETTER> checker = new HashSet<>(computeHashCap(model.size()));
			final Iterator<OutgoingCallTransition<LETTER, STATE>> it = mOperand.callSuccessors(state).iterator();
			while (it.hasNext()) {
				checker.add(it.next().getLetter());
			}

			if (checker.size() != model.size()) {
				return false;
			}
			for (final LETTER letter : model) {
				if (!checker.contains(letter)) {
					return false;
				}
			}

			return true;
		}
	}

	/**
	 * This class represents a return split matrix. The columns are the linear and the rows are the hierarchical
	 * predecessor states. The implementation is not really a matrix, but rather a hash map, since the matrix would be
	 * very sparse.
	 */
	private class Matrix {
		private final HashMap<STATE, HashMap<STATE, HashMap<LETTER, HashSet<STATE>>>> mHier2lin2letter2succ;

		/**
		 * @param size
		 *            number of non-singleton.
		 */
		public Matrix(final int size) {
			mHier2lin2letter2succ = new HashMap<>(computeHashCap(size));
		}

		/**
		 * This constructor is only used for the useless 1x1-matrix.
		 */
		private Matrix() {
			mHier2lin2letter2succ = null;
		}

		@Override
		public String toString() {
			return (mHier2lin2letter2succ == null) ? "{1x1-matrix}" : mHier2lin2letter2succ.toString();
		}
	}

	/**
	 * This class represents a matrix row. It knows its associated hierarchical predecessor state and the matrix entries
	 * of this row.
	 */
	private class MatrixRow {
		private final STATE mHier;
		private final HashMap<STATE, HashMap<LETTER, HashSet<STATE>>> mLin2letter2succ;

		/**
		 * @param hier
		 *            the hierarchical state.
		 * @param lin2letter2succ
		 *            the map (matrix row entries)
		 */
		public MatrixRow(final STATE hier, final HashMap<STATE, HashMap<LETTER, HashSet<STATE>>> lin2letter2succ) {
			mHier = hier;
			assert !lin2letter2succ.isEmpty();
			mLin2letter2succ = lin2letter2succ;
		}

		@Override
		public String toString() {
			return mHier + " -> " + mLin2letter2succ;
		}
	}

	/**
	 * This class is a dummy map. It is currently used for the empty return split matrix row.
	 */
	private class DummyMap extends HashMap<LETTER, HashSet<STATE>> {
		private static final long serialVersionUID = 1L;

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
	 * This class stores all states for a certain color and all states that are blocked for this color.
	 */
	private class ColorSet {
		// associated states
		protected final HashSet<STATE> mContent;
		protected final HashSet<STATE> mBlocked;

		/**
		 * @param size
		 *            size of the equivalence class.
		 * @param state
		 *            the first state
		 * @param blocked
		 *            the set of blocked states
		 */
		public ColorSet(final int size, final STATE state, final HashSet<STATE> blocked) {
			mContent = new HashSet<>(computeHashCap(size));
			mContent.add(state);
			mBlocked = blocked;
		}
	}

	// --- [end] helper methods and classes --- //

	// --- [start] important inner classes --- //

	/**
	 * The partition is the main object of the procedure. It contains and handles the equivalence classes and works as
	 * the resulting automaton.
	 */
	public class Partition implements IAutomatonStatePartition<STATE> {
		// equivalence classes
		private final Collection<EquivalenceClass> mEquivalenceClasses;
		// mapping 'state -> equivalence class'
		private final HashMap<STATE, EquivalenceClass> mState2EquivalenceClass;

		/**
		 * Constructor.
		 */
		public Partition() {
			mEquivalenceClasses = new LinkedList<>();
			mState2EquivalenceClass = new HashMap<>(computeHashCap(mOperand.size()));
		}

		/**
		 * Marks all respective equivalence classes as initial.
		 */
		public void markInitials() {
			/*
			 * if an equivalence class contains an initial state, the whole equivalence class should be initial
			 */
			for (final STATE state : mOperand.getInitialStates()) {
				final EquivalenceClass ec = mState2EquivalenceClass.get(state);
				ec.markAsInitial();
			}
		}

		/**
		 * This method adds an equivalence class (also to the work list) during the initialization phase.
		 *
		 * @param module
		 *            the states in the equivalence class
		 */
		private void addEcInitialization(final Set<STATE> module) {
			final EquivalenceClass ec = new EquivalenceClass(module);
			mEquivalenceClasses.add(ec);
			for (final STATE state : module) {
				mState2EquivalenceClass.put(state, ec);
			}
		}

		/**
		 * This method adds an equivalence class to the partition that resulted from an internal or call split.
		 *
		 * @param parent
		 *            the parent equivalence class
		 * @return the equivalence class
		 */
		private EquivalenceClass addEcIntCall(final EquivalenceClass parent) {
			Set<STATE> newStates = parent.mIntersection;
			if (newStates.size() > parent.mStates.size()) {
				newStates = parent.mStates;
				parent.mStates = parent.mIntersection;
			}
			final EquivalenceClass ec = new EquivalenceClass(newStates, parent);
			mEquivalenceClasses.add(ec);
			for (final STATE state : ec.mStates) {
				mState2EquivalenceClass.put(state, ec);
			}
			return ec;
		}

		/**
		 * This method adds an equivalence class to the partition that resulted from a return split.
		 *
		 * @param parent
		 *            the parent equivalence class
		 * @param states
		 *            the states
		 * @return the equivalence class
		 */
		private EquivalenceClass addEcReturn(final Set<STATE> states, final EquivalenceClass parent) {
			final EquivalenceClass ec = new EquivalenceClass(states, parent);
			mEquivalenceClasses.add(ec);

			// update mapping
			for (final STATE state : states) {
				assert (parent.mStates.contains(state)) && (mState2EquivalenceClass.get(state) == parent);

				parent.mStates.remove(state);
				mState2EquivalenceClass.put(state, ec);
			}

			return ec;
		}

		/**
		 * This method splits a state from its equivalence class during the internal and call split. The equivalence
		 * class is remembered.
		 * 
		 * @param state
		 *            the state
		 * @param splitEcs
		 *            the list of split equivalence classes
		 */
		private void splitState(final STATE state, final LinkedList<EquivalenceClass> splitEcs) {
			final EquivalenceClass ec = mState2EquivalenceClass.get(state);

			// first occurrence of the equivalence class, mark it
			if (ec.mIntersection.isEmpty()) {
				assert !splitEcs.contains(ec);
				splitEcs.add(ec);
			} else {
				assert splitEcs.contains(ec);
			}

			// move state to intersection set
			ec.mIntersection.add(state);

			// remove state from old set
			ec.mStates.remove(state);
		}

		/**
		 * This method finally splits the marked equivalence classes into two (for the internal and call split). The
		 * states have already been split in the equivalence class before. Only if there are states remaining the split
		 * is executed, otherwise the old equivalence class is restored.
		 * 
		 * @param states
		 *            set of states to split
		 * @return true iff a split occurred
		 */
		public boolean splitEquivalenceClasses(final Iterable<STATE> states) {
			boolean splitOccurred = false;
			final LinkedList<EquivalenceClass> splitEcs = new LinkedList<>();

			// process splits
			for (final STATE state : states) {
				if (DEBUG) {
					mLogger.info("splitting state " + state);
				}
				splitState(state, splitEcs);
			}

			// check and finalize splits
			for (final EquivalenceClass ec : splitEcs) {
				// split removed every state, restore equivalence class
				if (ec.mStates.isEmpty()) {
					ec.mStates = ec.mIntersection;
					if (DEBUG) {
						mLogger.info("EC was skipped " + ec);
					}
					++mSplitsWithoutChange;
				} else {
					// do a split
					if (DEBUG) {
						mLogger.info("EC was split " + ec);
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
			for (final EquivalenceClass ec : mEquivalenceClasses) {
				builder.append(append);
				append = ", ";
				builder.append(ec);
			}
			builder.append("}");
			return builder.toString();
		}

		@Override
		public IBlock<STATE> getBlock(final STATE state) {
			return mState2EquivalenceClass.get(state);
		}

		@Override
		public Set<STATE> getContainingSet(final STATE state) {
			return mState2EquivalenceClass.get(state).mStates;
		}

		@Override
		public int size() {
			return mEquivalenceClasses.size();
		}

		@Override
		public Iterator<IBlock<STATE>> blocksIterator() {
			return new Iterator<IBlock<STATE>>() {
				private final Iterator<EquivalenceClass> mIt = mEquivalenceClasses.iterator();

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

		@Override
		public Iterator<Set<STATE>> iterator() {
			return new Iterator<Set<STATE>>() {
				private final Iterator<EquivalenceClass> mIt = mEquivalenceClasses.iterator();

				@Override
				public boolean hasNext() {
					return mIt.hasNext();
				}

				@Override
				public Set<STATE> next() {
					return mIt.next().mStates;
				}
			};
		}
	}

	/**
	 * An equivalence class contains states and knows whether it is in the work list.
	 * <p>
	 * Two equivalence class objects are equal iff they share the same pointer.
	 */
	private class EquivalenceClass implements IBlock<STATE> {
		// unique ID (useful for hashCode and so for deterministic runs)
		private final int mId;
		// the states
		private Set<STATE> mStates;
		// intersection set that finally becomes a new equivalence class
		private Set<STATE> mIntersection;
		// status regarding incoming transitions
		private IncomingStatus mIncomingInt;
		private IncomingStatus mIncomingCall;
		private IncomingStatus mIncomingRet;
		// mapping: state to states that are separated
		private HashMap<STATE, HashSet<STATE>> mState2SeparatedSet;
		// matrix with return transition information
		private Matrix mMatrix;
		// status regarding outgoing return transitions
		private IncomingStatus mOutgoingRet;
		// does the equivalence class contain an initial state?
		private boolean mIsInitial;

		/**
		 * This is a partial constructor which is used for both initialization and splitting.
		 * 
		 * @param states
		 *            the set of states for the equivalence class
		 * @param fromSplit
		 *            flag currently ignored (necessary for overloading)
		 */
		private EquivalenceClass(final Set<STATE> states, final boolean fromSplit) {
			assert !states.isEmpty();
			++mEquivalenceClassIds;
			mId = mEquivalenceClassIds;
			mStates = states;
			reset();
		}

		/**
		 * This constructor is reserved for the placeholder equivalence class.
		 */
		private EquivalenceClass() {
			mId = 0;
			mStates = null;
			mIntersection = null;
		}

		/**
		 * This constructor is used for the initialization.
		 * 
		 * @param states
		 *            the set of states for the equivalence class
		 */
		public EquivalenceClass(final Set<STATE> states) {
			this(states, false);
			mIncomingInt = IncomingStatus.IN_WORKLIST;
			mIncomingCall = IncomingStatus.IN_WORKLIST;
			mWorkListIntCall.add(this);
			mIncomingRet = IncomingStatus.IN_WORKLIST;
			mWorkListRet.add(this);
			if (mFirstReturnSplitAlternative) {
				mOutgoingRet = IncomingStatus.IN_WORKLIST;
				mWorkListRetHier.add(this);
			}
			mMatrix = null;
		}

		/**
		 * This constructor is used during a split.
		 * 
		 * @param states
		 *            the set of states for the equivalence class
		 * @param parent
		 *            the parent equivalence class
		 */
		public EquivalenceClass(final Set<STATE> states, final EquivalenceClass parent) {
			this(states, true);

			switch (parent.mIncomingInt) {
				case UNKNOWN:
				case IN_WORKLIST:
					mIncomingInt = IncomingStatus.IN_WORKLIST;
					mWorkListIntCall.add(this);
					break;
				case NONE:
					mIncomingInt = IncomingStatus.NONE;
					break;
				default:
					throw new IllegalArgumentException();
			}

			switch (parent.mIncomingCall) {
				case UNKNOWN:
				case IN_WORKLIST:
					mIncomingCall = IncomingStatus.IN_WORKLIST;
					if (mIncomingInt != IncomingStatus.IN_WORKLIST) {
						mWorkListIntCall.add(this);
					}
					break;
				case NONE:
					mIncomingCall = IncomingStatus.NONE;
					break;
				default:
					throw new IllegalArgumentException();
			}

			switch (parent.mIncomingRet) {
				case UNKNOWN:
				case IN_WORKLIST:
					mIncomingRet = IncomingStatus.IN_WORKLIST;
					mWorkListRet.add(this);
					break;
				case NONE:
					mIncomingRet = IncomingStatus.NONE;
					break;
				default:
					throw new IllegalArgumentException();
			}

			if (mFirstReturnSplitAlternative) {
				switch (parent.mOutgoingRet) {
					case UNKNOWN:
					case IN_WORKLIST:
						mOutgoingRet = IncomingStatus.IN_WORKLIST;
						mWorkListRetHier.add(this);
						break;
					case NONE:
						mOutgoingRet = IncomingStatus.NONE;
						break;
					default:
						throw new IllegalArgumentException();
				}
			}

			if (mNondeterministicTransitions) {
				// also add other equivalence class to work list for nondeterministic transitions
				if (parent.mIncomingInt == IncomingStatus.UNKNOWN) {
					parent.mIncomingInt = IncomingStatus.IN_WORKLIST;
					mWorkListIntCall.add(parent);
				}
				if (parent.mIncomingCall == IncomingStatus.UNKNOWN) {
					parent.mIncomingCall = IncomingStatus.IN_WORKLIST;
					if (parent.mIncomingInt != IncomingStatus.IN_WORKLIST) {
						mWorkListIntCall.add(parent);
					}
				}

				if (parent.mIncomingRet == IncomingStatus.UNKNOWN) {
					parent.mIncomingRet = IncomingStatus.IN_WORKLIST;
					mWorkListRet.add(parent);
				}
			}

			if (mReturnSplitCorrectnessEcs != null) {
				// own predecessors
				for (final STATE state : mStates) {
					for (final IncomingReturnTransition<LETTER, STATE> transition : mOperand
							.returnPredecessors(state)) {
						mReturnSplitCorrectnessEcs.add(mPartition.mState2EquivalenceClass.get(transition.getLinPred()));
					}
				}
				// parent predecessors
				for (final STATE state : parent.mStates) {
					for (final IncomingReturnTransition<LETTER, STATE> transition : mOperand
							.returnPredecessors(state)) {
						mReturnSplitCorrectnessEcs.add(mPartition.mState2EquivalenceClass.get(transition.getLinPred()));
					}
				}
				// inherit from parent
				if (mReturnSplitCorrectnessEcs.contains(parent)) {
					mReturnSplitCorrectnessEcs.add(this);
				}
			}
			resetMatrix(parent);
		}

		/**
		 * Sets the equivalence class as initial.
		 */
		void markAsInitial() {
			mIsInitial = true;
		}

		@Override
		public int hashCode() {
			return mId;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			assert getClass() == obj.getClass();
			final EquivalenceClass other = (EquivalenceClass) obj;
			return mId == other.mId;
		}

		/**
		 * This method initializes the matrix. This is not done at the beginning to avoid creating a huge but sparse
		 * matrix, since other splits can be executed first.
		 * 
		 * @param hierEcs
		 *            hierarchical predecessor equivalence classes
		 */
		@SuppressWarnings("unchecked")
		public void initializeMatrix(final HashSet<EquivalenceClass> hierEcs) {
			if (STATISTICS) {
				mMatrixTime -= new GregorianCalendar().getTimeInMillis();
			}

			final Collection<EquivalenceClass> hierEcsUsed;

			// ignore singletons
			if (mStates.size() == 1) {
				hierEcsUsed = new ArrayList<>(hierEcs.size());
				for (final EquivalenceClass hierEc : hierEcs) {
					if (hierEc.mStates.size() > 1) {
						hierEcsUsed.add(hierEc);
					}
				}
			} else {
				// add all
				hierEcsUsed = hierEcs;
			}
			final int size = hierEcsUsed.size();

			/*
			 * The matrix has only one column and only one-liners for each hierarchical equivalence class - ignore that.
			 */
			if (size == 0) {
				if (DEBUG2) {
					mLogger.debug("--creating 1x1 dummy matrix");
				}

				mMatrix = mSingletonMatrix;

				if (STATISTICS) {
					mMatrixTime += new GregorianCalendar().getTimeInMillis();
				}
				return;
			}

			mMatrix = new Matrix(size);
			final HashMap<STATE, HashMap<STATE, HashMap<LETTER, HashSet<STATE>>>> hier2lin2letter2succ =
					mMatrix.mHier2lin2letter2succ;

			if (DEBUG2) {
				mLogger.debug("--adding entries");
			}

			// add entries
			final int mapSize = computeHashCap(mStates.size());

			for (final EquivalenceClass hierEc : hierEcsUsed) {
				for (final STATE hier : hierEc.mStates) {
					final HashMap<STATE, HashMap<LETTER, HashSet<STATE>>> lin2letter2succ = new HashMap<>(mapSize);

					if (DEBUG2) {
						mLogger.debug(" consider hier: " + hier);
					}

					for (final STATE lin : mStates) {
						if (DEBUG2) {
							mLogger.debug("  and lin: " + lin);
						}

						// first check whether hier is a down state
						if (!mDoubleDecker.isDoubleDecker(lin, hier)) {
							if (DEBUG2) {
								mLogger.debug("  no DS");
							}

							continue;
						}

						final Iterator<OutgoingReturnTransition<LETTER, STATE>> edges =
								mOperand.returnSuccessorsGivenHier(lin, hier).iterator();
						if (edges.hasNext()) {
							/*
							 * TODO(nondeterminism) at most one successor for
							 *     deterministic automata, offer improved
							 *     version (no Set<STATE>, no "if" in loop)?
							 */
							final HashMap<LETTER, HashSet<STATE>> return2succ = new HashMap<>();
							lin2letter2succ.put(lin, return2succ);
							do {
								final OutgoingReturnTransition<LETTER, STATE> edge = edges.next();
								final LETTER letter = edge.getLetter();
								HashSet<STATE> succs = return2succ.get(letter);
								if (succs == null) {
									succs = new HashSet<>();
									return2succ.put(letter, succs);
								}
								succs.add(edge.getSucc());
							} while (edges.hasNext());

							if (DEBUG2) {
								mLogger.debug("  transitions: " + return2succ);
							}
						} else {
							if (DEBUG2) {
								mLogger.debug("  DS");
							}

							lin2letter2succ.put(lin, mDownStateMap);
						}
					}

					if (lin2letter2succ.size() > 0) {
						hier2lin2letter2succ.put(hier, lin2letter2succ);
					}
				}
				assert hier2lin2letter2succ.size() > 0;
			}
			if (STATISTICS) {
				mMatrixTime += new GregorianCalendar().getTimeInMillis();
			}

			if (DEBUG2) {
				mLogger.debug("--finished creating matrix");
			}
		}

		/**
		 * This method checks whether a parent equivalence class (after a split) had a matrix. If so, the split states
		 * are shifted to the new child equivalence class.
		 * 
		 * @param parent
		 *            parent equivalenceClass class
		 */
		private void resetMatrix(final EquivalenceClass parent) {
			final Matrix oldMatrix = parent.mMatrix;
			if ((oldMatrix == null) || (oldMatrix == mSingletonMatrix)) {
				return;
			}

			if (DEBUG2) {
				mLogger.debug(
						"shifting matrix from " + parent.toStringShort() + "(" + oldMatrix + ") to " + toStringShort());
			}

			final HashMap<STATE, HashMap<STATE, HashMap<LETTER, HashSet<STATE>>>> oldHier2lin2letter2succ =
					oldMatrix.mHier2lin2letter2succ;
			final LinkedList<STATE> removeHiers = new LinkedList<>();
			final Set<STATE> states = mStates;
			mMatrix = new Matrix(oldHier2lin2letter2succ.size());
			final HashMap<STATE, HashMap<STATE, HashMap<LETTER, HashSet<STATE>>>> hier2lin2letter2succ =
					mMatrix.mHier2lin2letter2succ;
			for (final Entry<STATE, HashMap<STATE, HashMap<LETTER, HashSet<STATE>>>> outerEntry : oldHier2lin2letter2succ
					.entrySet()) {
				final HashMap<STATE, HashMap<LETTER, HashSet<STATE>>> oldLin2letter2succ = outerEntry.getValue();
				final Iterator<Entry<STATE, HashMap<LETTER, HashSet<STATE>>>> it =
						oldLin2letter2succ.entrySet().iterator();
				final LinkedList<STATE> removeLins = new LinkedList<>();
				while (it.hasNext()) {
					Entry<STATE, HashMap<LETTER, HashSet<STATE>>> innerEntry = it.next();
					STATE lin = innerEntry.getKey();
					if (states.contains(lin)) {
						final HashMap<STATE, HashMap<LETTER, HashSet<STATE>>> newLin2letter2succ =
								new HashMap<>(computeHashCap(oldLin2letter2succ.size()));
						newLin2letter2succ.put(lin, innerEntry.getValue());
						removeLins.add(lin);

						while (it.hasNext()) {
							innerEntry = it.next();
							lin = innerEntry.getKey();
							if (states.contains(lin)) {
								newLin2letter2succ.put(lin, innerEntry.getValue());
								removeLins.add(lin);
							}
						}

						final STATE hier = outerEntry.getKey();
						hier2lin2letter2succ.put(hier, newLin2letter2succ);
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
						 * can result in the state being twice in the list, but this is acceptable
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
					parent.mMatrix = null;
				} else if (parent.mStates.size() - mStates.size() == 1) {
					parent.mMatrix = mSingletonMatrix;
				}
			}

			if (hier2lin2letter2succ.size() <= 1) {
				if (hier2lin2letter2succ.size() == 0) {
					mMatrix = null;
				} else if (mStates.size() == 1) {
					mMatrix = mSingletonMatrix;
				}
			}

			if (DEBUG2) {
				mLogger.debug("resulting in matrices: parent: " + parent.mMatrix + ", child: " + mMatrix);
			}
		}

		/**
		 * This method marks the pairs of splits necessary for given sets of states, but does not invoke the splits yet.
		 *
		 * @param splitSets
		 *            sets of states to be marked for split
		 */
		public void markSplit(final Collection<HashSet<STATE>> splitSets) {
			assert splitSets.size() > 1 : "Splits with " + splitSets.size()
					+ " set are not sensible and should be caught beforehand.";

			if (mState2SeparatedSet == null) {
				mState2SeparatedSet = new HashMap<>(computeHashCap(mStates.size()));
				mSplitEcsReturn.add(this);
			} else {
				assert mSplitEcsReturn.contains(this);
			}

			final HashSet<Iterable<STATE>> visited = new HashSet<>();

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
		 * @param state1
		 *            one state
		 * @param state2
		 *            another state
		 */
		private void markPair(final STATE state1, final STATE state2) {
			if (DEBUG2) {
				mLogger.debug("separate " + state1 + " " + state2);
			}

			assert state1 != state2 && (mStates.contains(state1)) && (mStates.contains(state2));

			HashSet<STATE> separated = mState2SeparatedSet.get(state1);
			if (separated == null) {
				separated = new HashSet<>();
				mState2SeparatedSet.put(state1, separated);
			}
			separated.add(state2);

			separated = mState2SeparatedSet.get(state2);
			if (separated == null) {
				separated = new HashSet<>();
				mState2SeparatedSet.put(state2, separated);
			}
			separated.add(state1);
		}

		/**
		 * This method resets the intersection set.
		 */
		private void reset() {
			mIntersection = new HashSet<>(computeHashCap(mStates.size()));
			mState2SeparatedSet = null;
		}

		@Override
		public String toString() {
			if (mStates == null) {
				return "negative equivalence class";
			}

			if (!DEBUG && (DEBUG2 || DEBUG3 || DEBUG4)) {
				return toStringShort();
			}

			final StringBuilder builder = new StringBuilder();
			String append = "";

			builder.append("<[");
			builder.append(mIncomingInt);
			builder.append(",");
			builder.append(mIncomingCall);
			builder.append(",");
			builder.append(mIncomingRet);
			if (mFirstReturnSplitAlternative) {
				builder.append(",");
				builder.append(mOutgoingRet);
			}
			builder.append("], [");
			for (final STATE state : mStates) {
				builder.append(append);
				append = ", ";
				builder.append(state);
			}
			builder.append("], [");
			append = "";
			for (final STATE state : mIntersection) {
				builder.append(append);
				append = ", ";
				builder.append(state);
			}
			builder.append("]>");
			return builder.toString();
		}

		/**
		 * This method returns a short representation of the equivalence class with only the states. States in the
		 * intersection are not visible.
		 *
		 * @return a short string representation of the states
		 */
		public String toStringShort() {
			if (mStates == null) {
				return "negative equivalence class";
			}

			final StringBuilder builder = new StringBuilder();
			String append = "";

			builder.append("<");
			for (final STATE state : mStates) {
				builder.append(append);
				append = ", ";
				builder.append(state);
			}
			builder.append(">");

			return builder.toString();
		}

		@Override
		public boolean isInitial() {
			return mIsInitial;
		}

		@Override
		public boolean isFinal() {
			return mOperand.isFinal(mStates.iterator().next());
		}

		@Override
		public STATE minimize(final IMergeStateFactory<STATE> stateFactory) {
			return stateFactory.merge(mStates);
		}

		@Override
		public Iterator<STATE> iterator() {
			return mStates.iterator();
		}

		@Override
		public boolean isRepresentativeIndependentInternalsCalls() {
			return true;
		}
	}

	/**
	 * The work list has a priority queue of equivalence classes.
	 * <p>
	 * Since the size of the equivalence classes may change due to splitting, it is not guaranteed that the order is
	 * correct over time, but since it is a heuristic rather than a rule to prefer smaller splitters first, this is not
	 * considered bad and additional overhead is avoided.
	 */
	private abstract class AWorkList implements Iterator<EquivalenceClass> {
		protected final PriorityQueue<EquivalenceClass> mQueue;

		public AWorkList() {
			mQueue = new PriorityQueue<>(Math.max(mOperand.size(), 1), new Comparator<EquivalenceClass>() {
				@Override
				public int compare(final EquivalenceClass ec1, final EquivalenceClass ec2) {
					return ec1.mStates.size() - ec2.mStates.size();
				}
			});
		}

		/**
		 * This method adds an equivalence class to the work list. The caller asserts that the class is not already in
		 * the work list and must inform the equivalence class beforehand.
		 *
		 * @param ec
		 *            the equivalence class
		 */
		public void add(final EquivalenceClass ec) {
			assert !mQueue.contains(ec);
			mQueue.add(ec);
		}

		@Override
		public boolean hasNext() {
			return !mQueue.isEmpty();
		}

		@Override
		public abstract EquivalenceClass next();

		@Override
		public void remove() {
			throw new UnsupportedOperationException("Removing is not supported.");
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
		 * @param builder
		 *            the string builder
		 */
		protected void toStringHelper(final StringBuilder builder) {
			builder.append("<<");
			String append = "";
			for (final EquivalenceClass ec : mQueue) {
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
			final EquivalenceClass ec = mQueue.poll();
			if (DEBUG) {
				mLogger.info("\npopping from IntCall WL: " + ec);
			}
			return ec;
		}

		@Override
		public void add(final EquivalenceClass ec) {
			assert (ec.mIncomingInt == IncomingStatus.IN_WORKLIST) || (ec.mIncomingCall == IncomingStatus.IN_WORKLIST);
			if (DEBUG) {
				mLogger.info("adding of IntCall WL: " + ec);
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
			final EquivalenceClass ec = mQueue.poll();
			ec.mIncomingRet = IncomingStatus.UNKNOWN;
			if (DEBUG) {
				mLogger.info("\npopping from return WL: " + ec);
			}
			return ec;
		}

		@Override
		public void add(final EquivalenceClass ec) {
			assert ec.mIncomingRet == IncomingStatus.IN_WORKLIST;
			if (DEBUG) {
				mLogger.info("adding of return WL: " + ec);
			}
			super.add(ec);
		}

		/**
		 * This method fills the queue with all equivalence classes so far. It is used exactly once when the first
		 * return split has finished.
		 */
		public void fillWithAll() {
			for (final EquivalenceClass ec : mPartition.mEquivalenceClasses) {
				if (ec.mIncomingRet != IncomingStatus.NONE) {
					ec.mIncomingRet = IncomingStatus.IN_WORKLIST;
					mQueue.add(ec);
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
			final EquivalenceClass ec = mQueue.poll();
			ec.mOutgoingRet = IncomingStatus.UNKNOWN;
			if (DEBUG) {
				mLogger.info("\npopping from return hier WL: " + ec);
			}
			return ec;
		}

		@Override
		public void add(final EquivalenceClass ec) {
			assert ec.mOutgoingRet == IncomingStatus.IN_WORKLIST;
			if (DEBUG) {
				mLogger.info("adding of return hier WL: " + ec);
			}
			super.add(ec);
		}
	}

	// --- [end] important inner classes --- //
}
