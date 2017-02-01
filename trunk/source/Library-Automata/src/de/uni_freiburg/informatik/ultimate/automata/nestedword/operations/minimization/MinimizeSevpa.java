/*
 * Copyright (C) 2013-2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
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

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.PriorityQueue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.util.FalseFlag;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.util.IBlock;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.util.IFlag;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.util.IPartition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.util.PartitionBackedSetOfPairs;

/**
 * Minimizer for special type of nested word automata used in Ultimate.
 * <p>
 * based on idea of Hopcroft's minimization for deterministic finite automata
 * applied to nested word automata (some huge differences)
 * <p>
 * over-approximation of the language due to ignorance of
 * history encoded in call and return edges
 * afterwards soundness is assured using a more expensive analysis
 * this process is looped until no change occurs anymore
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
@SuppressWarnings("squid:UselessParenthesesCheck")
public class MinimizeSevpa<LETTER, STATE> extends AbstractMinimizeNwa<LETTER, STATE> {
	/*
	 * EXPERIMENTAL
	 * deterministic finite automata can be handled more efficiently
	 * 
	 * not even correct for non-total DFAs
	 * but: if non-final states are initially added to the work list,
	 * all examples run with monlyOneToWorkList set to true
	 * (but example 08 is even more reduced, so there IS a difference)
	 */
	private static final boolean ONLY_ONE_TO_WORK_LIST = false;
	// use sound but expensive linear return split
	private static final boolean SPLIT_ALL_RETURNS_LIN = false;
	// use sound but expensive hierarchical return split
	private static final boolean SPLIT_ALL_RETURNS_HIER = false;
	
	private static final boolean STATISTICS = false;
	
	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	// old automaton
	private final IDoubleDeckerAutomaton<LETTER, STATE> mDoubleDecker;
	// ID for equivalence classes
	private int mEquivalenceClassId;
	// Partition of states into equivalence classes
	private Partition mPartition;
	
	private int mSplitsWithChange;
	private int mSplitsWithoutChange;
	
	private final IFlag mTimeout;
	private boolean mConstructionInterrupted;
	
	private final boolean mInitialPartitionSeparatesFinalsAndNonfinals;
	
	/* EXPERIMENTAL END */
	
	/**
	 * Creates a copy of operand where non-reachable states are omitted.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            nested word automaton to minimize
	 * @throws AutomataOperationCanceledException
	 *             iff cancel signal is received
	 */
	public MinimizeSevpa(final AutomataLibraryServices services, final IMergeStateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, null, false, false);
	}
	
	/**
	 * Creates a copy of operand with an initial partition.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            nested word automaton to minimize
	 * @param equivalenceClasses
	 *            represent initial equivalence classes
	 * @param addMapOldState2newState
	 *            add map old state 2 new state?
	 * @throws AutomataOperationCanceledException
	 *             iff cancel signal is received
	 */
	public MinimizeSevpa(final AutomataLibraryServices services, final IMergeStateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final PartitionBackedSetOfPairs<STATE> equivalenceClasses, final boolean addMapOldState2newState,
			final boolean initialPartitionSeparatesFinalsAndNonfinals) throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, equivalenceClasses, addMapOldState2newState, new FalseFlag(),
				initialPartitionSeparatesFinalsAndNonfinals);
	}
	
	/**
	 * Creates a copy of operand with an initial partition.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            nested word automaton to minimize
	 * @param equivalenceClasses
	 *            represent initial equivalence classes
	 * @param addMapOldState2newState
	 *            add map old state 2 new state?
	 * @param timeout
	 *            timeout
	 * @throws AutomataOperationCanceledException
	 *             iff cancel signal is received
	 */
	public MinimizeSevpa(final AutomataLibraryServices services, final IMergeStateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final PartitionBackedSetOfPairs<STATE> equivalenceClasses, final boolean addMapOldState2newState,
			final IFlag timeout, final boolean initialPartitionSeparatesFinalsAndNonfinals)
			throws AutomataOperationCanceledException {
		super(services, stateFactory);
		mOperand = operand;
		
		printStartMessage();
		if (operand instanceof IDoubleDeckerAutomaton) {
			mDoubleDecker = (IDoubleDeckerAutomaton<LETTER, STATE>) operand;
		} else {
			if (!isFiniteAutomaton()) {
				throw new IllegalArgumentException(
						"The input must either be a finite automaton or an IDoubleDeckerAutomaton.");
			}
			mDoubleDecker = null;
		}
		mTimeout = timeout;
		mInitialPartitionSeparatesFinalsAndNonfinals = initialPartitionSeparatesFinalsAndNonfinals;
		
		minimize(equivalenceClasses, addMapOldState2newState);
		
		printExitMessage();
		
		if (STATISTICS) {
			mLogger.info("positive splits: " + mSplitsWithChange);
			mLogger.info("negative splits: " + mSplitsWithoutChange);
			mLogger.info("quote (p/n): "
					+ (mSplitsWithChange / Math.max(mSplitsWithoutChange, 1)));
		}
	}
	
	@Override
	protected INestedWordAutomaton<LETTER, STATE> getOperand() {
		return mOperand;
	}
	
	/**
	 * Minimization technique for deterministic finite automata by Hopcroft
	 * (http://en.wikipedia.org/wiki/DFA_minimization).
	 * 
	 * @param equivalenceClasses
	 *            initial partition of the states
	 * @param addMapping
	 *            add map old state 2 new state?
	 * @throws AutomataOperationCanceledException
	 *             iff cancel signal is received
	 */
	private void minimize(final PartitionBackedSetOfPairs<STATE> equivalenceClasses, final boolean addMapping)
			throws AutomataOperationCanceledException {
		// cancel if signal is received
		if (isCancellationRequested()) {
			throw new AutomataOperationCanceledException(getClass());
		}
		
		// intermediate container for the states
		final StatesContainer states = new StatesContainer(mOperand);
		
		// merge non-distinguishable states
		mergeStates(states, equivalenceClasses, addMapping);
	}
	
	/**
	 * Merges states that are not distinguishable
	 * (based on Hopcroft's algorithm).
	 * 
	 * @param states
	 *            container with reachable states (gets deleted)
	 * @param equivalenceClasses
	 *            initial partition of the states
	 * @param addMapping
	 *            add map old state 2 new state?
	 * @throws AutomataOperationCanceledException
	 *             iff cancel signal is received
	 */
	private void mergeStates(StatesContainer states, final PartitionBackedSetOfPairs<STATE> equivalenceClasses,
			final boolean addMapping) throws AutomataOperationCanceledException {
		assert (mPartition == null);
		if (equivalenceClasses == null) {
			// creation of the initial partition (if not passed in the constructor)
			mPartition = createInitialPartition(states);
		} else {
			final Collection<Set<STATE>> modules = equivalenceClasses.getRelation();
			mPartition = new Partition(mOperand, states.size());
			if (mInitialPartitionSeparatesFinalsAndNonfinals) {
				// predefined modules are already split with respect to final states
				assert (assertStatesSeparation(modules)) : "initial partition does not separate final/non-final states";
				
				for (final Set<STATE> ecSet : modules) {
					assert !ecSet.isEmpty();
					mPartition.addEquivalenceClass(
							new EquivalenceClass(ecSet, mOperand.isFinal(ecSet.iterator().next())));
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
						mPartition.addEquivalenceClass(new EquivalenceClass(finals, true));
						finals = new HashSet<>();
					}
					if (!nonfinals.isEmpty()) {
						mPartition.addEquivalenceClass(new EquivalenceClass(nonfinals, false));
						nonfinals = new HashSet<>();
					}
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
		constructAutomaton(addMapping);
	}
	
	/**
	 * Checks that the states in each equivalence class are all either final
	 * or non-final.
	 *
	 * @param equivalenceClasses
	 *            partition passed in constructor
	 * @return true iff equivalence classes respect final status of states
	 */
	private boolean assertStatesSeparation(final Collection<Set<STATE>> equivalenceClasses) {
		for (final Set<STATE> equivalenceClass : equivalenceClasses) {
			final Iterator<STATE> it = equivalenceClass.iterator();
			assert (it.hasNext());
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
	 * Creates the initial partition.
	 * Distinguishes between final and non-final states.
	 * 
	 * @param states
	 *            container with reachable states
	 * @return initial partition of the states
	 */
	private Partition createInitialPartition(final StatesContainer states) {
		// build two sets with final and non-final states, respectively
		HashSet<STATE> finals;
		HashSet<STATE> nonfinals;
		
		if (states.wasCopied()) {
			// if sets already exist, use them
			finals = states.getFinals();
			nonfinals = states.getNonfinals();
		} else {
			// make a copy here if states container has no sets
			finals = new HashSet<>(
					computeHashCap(mOperand.getFinalStates().size()));
			nonfinals = new HashSet<>(computeHashCap(
					mOperand.size() - mOperand.getFinalStates().size()));
			for (final STATE state : mOperand.getStates()) {
				if (mOperand.isFinal(state)) {
					finals.add(state);
				} else {
					nonfinals.add(state);
				}
			}
		}
		
		// create partition object
		final Partition partition =
				new Partition(mOperand, finals.size() + nonfinals.size());
		
		// set up the initial equivalence classes
		
		// final states
		if (!finals.isEmpty()) {
			final EquivalenceClass finalsP = new EquivalenceClass(finals, true, true);
			partition.addEquivalenceClass(finalsP);
		}
		
		// non-final states (initially not in work list)
		if (!nonfinals.isEmpty()) {
			final EquivalenceClass nonfinalsP =
					new EquivalenceClass(nonfinals, false, true);
			partition.addEquivalenceClass(nonfinalsP);
		}
		
		return partition;
	}
	
	/**
	 * Iteratively refines partition until fixed point is reached.
	 * For each letter finds the set of predecessor states (X).
	 * 
	 * @throws AutomataOperationCanceledException
	 *             iff cancel signal is received
	 */
	private void refinePartition() throws AutomataOperationCanceledException {
		/*
		 * naiveSplit used as long as possible
		 * then switch to more complicated but sound split
		 */
		boolean naiveSplit = true;
		// assures that complicated split is executed at least once
		boolean firstIteration = true;
		// number of equivalence classes (termination if no change)
		int equivalenceClasses = mPartition.getEquivalenceClasses().size();
		
		while (true) {
			if (mTimeout.getStatus()) {
				mConstructionInterrupted = true;
				break;
			}
			
			// fixed point iteration
			while (!mPartition.workListIsEmpty()) {
				// A = next equivalence class from W, also called target set
				final TargetSet a = new TargetSet(mPartition.popFromWorkList());
				assert !a.isEmpty();
				
				// collect all incoming letters (and outgoing returns)
				HashSet<LETTER> internalLetters;
				HashSet<LETTER> callLetters;
				HashSet<LETTER> returnLettersOutgoing;
				final HashSet<LETTER> returnLetters = new HashSet<>();
				
				if (naiveSplit) {
					internalLetters = new HashSet<>();
					callLetters = new HashSet<>();
					returnLettersOutgoing = new HashSet<>();
					
					final Iterator<STATE> iterator = a.iterator();
					while (iterator.hasNext()) {
						final STATE state = iterator.next();
						
						internalLetters.addAll(
								mOperand.lettersInternalIncoming(state));
						callLetters.addAll(
								mOperand.lettersCallIncoming(state));
						returnLetters.addAll(
								mOperand.lettersReturnIncoming(state));
						returnLettersOutgoing.addAll(
								mOperand.lettersReturn(state));
					}
				} else {
					internalLetters = null;
					callLetters = null;
					returnLettersOutgoing = null;
					
					final Iterator<STATE> iterator = a.iterator();
					while (iterator.hasNext()) {
						final STATE state = iterator.next();
						
						returnLetters.addAll(
								mOperand.lettersReturnIncoming(state));
					}
				}
				
				if (naiveSplit) {
					// internal alphabet
					findXByInternalOrCall(a, mPartition, internalLetters,
							new InternalPredecessorSetFinder(mPartition, a));
					
					// call alphabet
					findXByInternalOrCall(a, mPartition, callLetters,
							new CallPredecessorSetFinder(mPartition, a));
				}
				
				// return alphabet
				
				findXByReturn(a, mPartition, returnLetters, naiveSplit);
				
				if (naiveSplit) {
					// return successor split
					
					findXByOutgoingReturn(a, mPartition, returnLettersOutgoing,
							new ReturnSuccessorSetFinder(mPartition, a));
				}
				
				// remove flags for target set
				a.delete();
				
				// cancel iteration iff cancel signal is received
				if (isCancellationRequested()) {
					throw new AutomataOperationCanceledException(getClass());
				}
			}
			
			if (firstIteration) {
				// after the first iteration the complicated split is executed
				firstIteration = false;
			} else {
				// termination criterion: complicated split did not change anything
				if (mPartition.getEquivalenceClasses().size() == equivalenceClasses) {
					break;
				}
				assert (mPartition.getEquivalenceClasses().size() > equivalenceClasses);
			}
			
			naiveSplit = !naiveSplit;
			equivalenceClasses = mPartition.getEquivalenceClasses().size();
			putAllToWorkList(mPartition, naiveSplit);
		}
	}
	
	/**
	 * Finds set of predecessor states X and invokes next step.
	 * 
	 * @param targetSet
	 *            target set of which X shall be computed
	 * @param partition
	 *            partition of the states
	 * @param alphabet
	 *            collection of internal or call letters
	 * @param predecessorFinder
	 *            finds the predecessor set X
	 */
	private void findXByInternalOrCall(final TargetSet targetSet, final Partition partition,
			final Collection<LETTER> alphabet, final APredecessorSetFinder predecessorFinder) {
		for (final LETTER letter : alphabet) {
			/*
			 * X = predecessor set of A = all states s1
			 * with transition (s1, l, s2) for letter l and s2 in A
			 */
			final PredecessorSet predSet = predecessorFinder.find(letter);
			
			searchY(partition, targetSet, predSet);
		}
	}
	
	/**
	 * Finds set of predecessor states X and invokes next step.
	 * Considers return letters and splits linear and hierarchical predecessors.
	 * 
	 * @param targetSet
	 *            target set of which X shall be computed
	 * @param partition
	 *            partition of the states
	 * @param alphabet
	 *            collection of return letters
	 * @param naiveSplit
	 *            true iff naive split shall be used
	 */
	private void findXByReturn(final TargetSet targetSet, final Partition partition, final Collection<LETTER> alphabet,
			final boolean naiveSplit) {
		if (naiveSplit) {
			findXByLinPred(targetSet, partition, alphabet);
			findXByHierPred(targetSet, partition, alphabet);
		} else {
			findXByDownStates(targetSet, partition, alphabet);
		}
	}
	
	/**
	 * Finds set of linear predecessor states X and invokes next step.
	 * 
	 * @param targetSet
	 *            target set of which X shall be computed
	 * @param partition
	 *            partition of the states
	 * @param alphabet
	 *            collection of return letters
	 */
	private void findXByLinPred(final TargetSet targetSet, final Partition partition,
			final Collection<LETTER> alphabet) {
		for (final LETTER letter : alphabet) {
			if (SPLIT_ALL_RETURNS_LIN) {
				// trivial split: every linear predecessor is different
				final ReturnPredecessorLinSetFinder finder =
						new ReturnPredecessorLinSetFinder(partition, targetSet);
				final PredecessorSet x = finder.find(letter);
				final Iterator<STATE> iterator = x.iterator();
				while (iterator.hasNext()) {
					final HashSet<STATE> hashSet =
							new HashSet<>(computeHashCap(1));
					hashSet.add(iterator.next());
					final PredecessorSet x2 = new PredecessorSet(hashSet);
					
					searchY(partition, targetSet, x2);
				}
			} else {
				/*
				 * only linear predecessors with hierarchical predecessors
				 * from different equivalence classes are split
				 */
				
				/*
				 * maps equivalence class EC of hierarchical predecessors
				 * to set of linear predecessors
				 */
				final HashMap<EquivalenceClass, HashSet<STATE>> ec2linSet =
						new HashMap<>();
				
				final Iterator<STATE> iterator = targetSet.iterator();
				while (iterator.hasNext()) {
					final STATE state = iterator.next();
					for (final IncomingReturnTransition<LETTER, STATE> inTrans : partition.hierPredIncoming(state,
							letter)) {
						final EquivalenceClass ec = partition.getEquivalenceClass(
								inTrans.getHierPred());
						HashSet<STATE> linSet = ec2linSet.get(ec);
						if (linSet == null) {
							linSet = new HashSet<>();
							ec2linSet.put(ec, linSet);
						}
						for (final IncomingReturnTransition<LETTER, STATE> inTransInner : partition.linPredIncoming(
								state,
								inTrans.getHierPred(), letter)) {
							linSet.add(inTransInner.getLinPred());
						}
					}
				}
				
				/*
				 * for each equivalence class of hierarchical predecessors
				 * split the linear predecessors
				 */
				for (final HashSet<STATE> set : ec2linSet.values()) {
					final PredecessorSet x = new PredecessorSet(set);
					
					searchY(partition, targetSet, x);
				}
			}
		}
	}
	
	/**
	 * Finds set of hierarchical predecessor states X and invokes next step.
	 * 
	 * @param targetSet
	 *            target set of which X shall be computed
	 * @param partition
	 *            partition of the states
	 * @param alphabet
	 *            collection of return letters
	 */
	private void findXByHierPred(final TargetSet targetSet, final Partition partition,
			final Collection<LETTER> alphabet) {
		for (final LETTER letter : alphabet) {
			if (SPLIT_ALL_RETURNS_HIER) {
				// trivial split: every linear predecessor is different
				
				// find all hierarchical predecessors of the states in A
				final Iterator<STATE> iterator = targetSet.iterator();
				final Collection<STATE> hierPreds = new HashSet<>();
				while (iterator.hasNext()) {
					for (final IncomingReturnTransition<LETTER, STATE> inTrans : partition
							.hierPredIncoming(iterator.next(), letter)) {
						hierPreds.add(inTrans.getHierPred());
					}
				}
				
				for (final STATE hier : hierPreds) {
					final HashSet<STATE> hashSet =
							new HashSet<>(computeHashCap(1));
					hashSet.add(hier);
					final PredecessorSet x = new PredecessorSet(hashSet);
					
					searchY(partition, targetSet, x);
				}
			} else {
				/*
				 * only hierarchical predecessors with linear predecessors
				 * from different equivalence classes are split
				 */
				
				// distinguish linear predecessors by equivalence classes
				final HashMap<EquivalenceClass, HashSet<STATE>> ec2hierSet =
						new HashMap<>();
				final Iterator<STATE> iterator = targetSet.iterator();
				while (iterator.hasNext()) {
					final STATE state = iterator.next();
					for (final IncomingReturnTransition<LETTER, STATE> inTrans : partition.hierPredIncoming(state,
							letter)) {
						final STATE hier = inTrans.getHierPred();
						final STATE lin = inTrans.getLinPred();
						final EquivalenceClass ec =
								partition.getEquivalenceClass(lin);
						HashSet<STATE> set = ec2hierSet.get(ec);
						if (set == null) {
							set = new HashSet<>();
							ec2hierSet.put(ec, set);
						}
						set.add(hier);
					}
				}
				
				/*
				 * for each equivalence class of linear predecessors
				 * split hierarchical predecessors
				 */
				for (final HashSet<STATE> set : ec2hierSet.values()) {
					final PredecessorSet x = new PredecessorSet(set);
					
					searchY(partition, targetSet, x);
				}
			}
		}
	}
	
	/**
	 * Splits states which encode different histories in the run.
	 * <p>
	 * distinguishes return transitions by the equivalence class of the
	 * hierarchical and linear predecessor and splits non-similar transitions
	 * <p>
	 * expensive method, only used to accomplish soundness in the end
	 * 
	 * @param targetSet
	 *            target set of which X shall be computed
	 * @param partition
	 *            partition of the states
	 * @param alphabet
	 *            collection of return letters
	 */
	private void findXByDownStates(final TargetSet targetSet, final Partition partition,
			final Collection<LETTER> alphabet) {
		for (final LETTER letter : alphabet) {
			// maps hierarchical states to linear states to return transitions
			final HashMap<EquivalenceClass, HashMap<EquivalenceClass, List<Set<ReturnTransition>>>> hier2lin2trans =
					new HashMap<>();
			
			final Iterator<STATE> iterator = targetSet.iterator();
			// for each successor state 'state' in A:
			while (iterator.hasNext()) {
				final STATE state = iterator.next();
				final HashSet<STATE> hierVisited = new HashSet<>();
				
				// for each hierarchical predecessor 'hier' of 'state':
				for (final IncomingReturnTransition<LETTER, STATE> inTrans : partition.hierPredIncoming(state,
						letter)) {
					final STATE hier = inTrans.getHierPred();
					
					// new change: ignore duplicate work
					if (!hierVisited.add(hier)) {
						continue;
					}
					
					final EquivalenceClass ecHier =
							partition.getEquivalenceClass(hier);
					
					HashMap<EquivalenceClass, List<Set<ReturnTransition>>> lin2trans = hier2lin2trans.get(ecHier);
					if (lin2trans == null) {
						lin2trans = new HashMap<>();
						hier2lin2trans.put(ecHier, lin2trans);
					}
					
					// for each linear predecessor 'lin' of 'state' and 'hier':
					for (final IncomingReturnTransition<LETTER, STATE> inTransInner : partition.linPredIncoming(state,
							hier, letter)) {
						final STATE lin = inTransInner.getLinPred();
						final EquivalenceClass ecLin =
								partition.getEquivalenceClass(lin);
						
						// list of similar sets
						List<Set<ReturnTransition>> similarSetsList =
								lin2trans.get(ecLin);
						if (similarSetsList == null) {
							similarSetsList =
									new LinkedList<>();
							lin2trans.put(ecLin, similarSetsList);
						}
						
						// return transition considered
						final ReturnTransition transition =
								new ReturnTransition(lin, hier, state);
						
						// find fitting set of similar return transitions
						Set<ReturnTransition> similarSet =
								getSimilarSet(partition, transition,
										letter, similarSetsList);
						if (similarSet == null) {
							similarSet = new HashSet<>();
							similarSetsList.add(similarSet);
						}
						
						similarSet.add(transition);
					}
				}
			}
			
			// split each set of similar states
			createAndSplitXByDownStates(targetSet, partition, hier2lin2trans);
		}
	}
	
	/**
	 * Finds the set of similar return transitions if possible.
	 * 
	 * @param partition
	 *            partition of the states
	 * @param transition
	 *            return transition
	 * @param letter
	 *            return letter
	 * @param similarSetsList
	 *            list of similar sets
	 * @return set of similar return transitions if possible, else null
	 */
	private Set<ReturnTransition> getSimilarSet(final Partition partition, final ReturnTransition transition,
			final LETTER letter, final List<Set<ReturnTransition>> similarSetsList) {
		for (final Set<ReturnTransition> result : similarSetsList) {
			boolean found = true;
			
			// compare with each transition in the set
			for (final ReturnTransition trans : result) {
				if (!transition.isSimilar(partition, trans, letter)) {
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
	 * Creates predecessor sets and splits them.
	 * 
	 * @param targetSet
	 *            target set of which X shall be computed
	 * @param partition
	 *            partition of the states
	 * @param hier2lin2trans
	 *            hash map with distinguished return transitions
	 */
	private void createAndSplitXByDownStates(final TargetSet targetSet, final Partition partition,
			final HashMap<EquivalenceClass, HashMap<EquivalenceClass, List<Set<ReturnTransition>>>> hier2lin2trans) {
		for (final HashMap<EquivalenceClass, List<Set<ReturnTransition>>> lin2trans : hier2lin2trans.values()) {
			for (final List<Set<ReturnTransition>> similarSetsList : lin2trans.values()) {
				// for each set of similar states perform a split
				for (final Set<ReturnTransition> similarSet : similarSetsList) {
					// set up linear and hierarchical predecessor sets
					final int size = computeHashCap(similarSet.size());
					final HashSet<STATE> lins = new HashSet<>(size);
					final HashSet<STATE> hiers = new HashSet<>(size);
					for (final ReturnTransition trans : similarSet) {
						lins.add(trans.getLin());
						hiers.add(trans.getHier());
					}
					
					// split similar linear predecessors
					PredecessorSet predSet = new PredecessorSet(lins);
					searchY(partition, targetSet, predSet);
					
					// split similar hierarchical predecessors
					predSet = new PredecessorSet(hiers);
					searchY(partition, targetSet, predSet);
				}
			}
		}
	}
	
	/**
	 * Split hierarchical predecessors of outgoing return transitions.
	 * 
	 * @param targetSet
	 *            target set of which X shall be computed
	 * @param partition
	 *            partition of the states
	 * @param alphabet
	 *            collection of return letters
	 * @param predecessorFinder
	 *            finds the predecessor set X
	 */
	private void findXByOutgoingReturn(final TargetSet targetSet, final Partition partition,
			final Collection<LETTER> alphabet, final ReturnSuccessorSetFinder predecessorFinder) {
		for (final LETTER letter : alphabet) {
			/*
			 * X = predecessor set of A in hierarchical view
			 * = all states h with transition (s1, l, h, s2) for s1 in A
			 */
			final PredecessorSet x = predecessorFinder.find(letter);
			
			searchY(partition, targetSet, x);
		}
	}
	
	/**
	 * Finds equivalence classes Y where intersection with X is non-empty
	 * and splits Y into 'Y \cap X' and 'Y \ X'.
	 * 
	 * @param partition
	 *            partition of the states
	 * @param targetSet
	 *            target set of which predecessor set X was computed
	 * @param predSet
	 *            predecessor set X
	 */
	private void searchY(final Partition partition, final TargetSet targetSet, final PredecessorSet predSet) {
		assert (predSet.size() > 0);
		
		/*
		 * list of split equivalence classes
		 */
		final LinkedList<EquivalenceClass> intersected =
				new LinkedList<>();
		
		// iteratively splits equivalence classes with elements from X
		final Iterator<STATE> iterator = predSet.iterator();
		while (iterator.hasNext()) {
			final STATE state = iterator.next();
			
			// find equivalence class Y
			final EquivalenceClass y = partition.getEquivalenceClass(state);
			assert y != null;
			
			// move state from Y to Y \cap X
			y.moveState(state, intersected);
			assert y.getIntersection(intersected).contains(state);
			assert !y.getCollection().contains(state);
		}
		
		// delete X
		predSet.delete();
		
		// split equivalence classes
		split(partition, targetSet, intersected);
	}
	
	/**
	 * Splits equivalence classes Y into 'Y \cap X' and 'Y \ X'.
	 * 
	 * @param partition
	 *            partition of the states
	 * @param targetSet
	 *            target set of which predecessor set X was computed
	 * @param intersected
	 *            list of equivalence classes Y
	 */
	private void split(final Partition partition, final TargetSet targetSet,
			final LinkedList<EquivalenceClass> intersected) {
		/*
		 * for all equivalence classes Y not contained in W:
		 * put one or two of {'Y \cap X', 'Y \ X'} in W,
		 * but only if Y was split, i.e., 'Y \ X != {}'
		 */
		for (final EquivalenceClass block : intersected) {
			/*
			 * if Y is empty, then the intersection is not needed
			 * and the states can be restored
			 */
			if (!block.isEmpty()) {
				++mSplitsWithChange;
				
				// create new equivalence class
				final EquivalenceClass intersection = block.split(partition);
				
				/*
				 * if Y was in the target set, the split equivalence class
				 * must also be inserted
				 */
				if (block.isInTargetSet()) {
					targetSet.addEquivalenceClass(intersection);
				}
				
				// if Y was not in work list, put it and/or intersection there
				if (!block.isInWorkList()) {
					assert (!intersection.isInWorkList());
					
					if (ONLY_ONE_TO_WORK_LIST) {
						/*
						 * if deterministic:
						 * put the smaller equivalence class
						 * of {'Y \cap X', 'Y \ X'} in W
						 * NOTE: see note for monlyOneToWorkList
						 */
						if (block.size() <= intersection.size()) {
							partition.addToWorkList(block);
						} else {
							partition.addToWorkList(intersection);
						}
					} else {
						/*
						 * if non-deterministic:
						 * put both equivalence classes in the work list
						 * (necessary for correctness)
						 */
						partition.addToWorkList(block);
						partition.addToWorkList(intersection);
					}
				}
				
				// add return successors to work list
				partition.addReturnsToWorkList(intersection);
			} else {
				++mSplitsWithoutChange;
			}
			
			// reset information about the intersection equivalence class
			block.resetIntersection();
		}
	}
	
	/**
	 * Puts all equivalence classes to the work list again.
	 * 
	 * @param partition
	 *            partition of the states
	 * @param naiveSplit
	 *            true iff naive split is used next
	 */
	private void putAllToWorkList(final Partition partition, final boolean naiveSplit) {
		if (naiveSplit) {
			// only collect equivalence classes, which have been split lately
			for (final EquivalenceClass block : partition.getEquivalenceClasses()) {
				if (block.wasSplitDuringSecondPhase()) {
					partition.addToWorkList(block);
				}
			}
		} else {
			// only collect equivalence classes with incoming return transitions
			for (final EquivalenceClass block : partition.getEquivalenceClasses()) {
				if (block.hasIncomingReturns(partition)) {
					partition.addToWorkList(block);
				}
			}
		}
	}
	
	/**
	 * Merges states from computed equivalence classes.
	 * 
	 * @param addMapping
	 *            add map old state 2 new state?
	 */
	private void constructAutomaton(final boolean addMapping) {
		// make sure initial equivalence classes are marked
		mPartition.markInitials();
		
		/*
		 * TODO 2016-05-26 Christian:
		 * temporary test that no equivalence class is empty in the end;
		 * can be removed after a while
		 */
		final boolean assertion = mPartition.removeEmptyEquivalenceClasses();
		if (assertion) {
			throw new AssertionError(
					"Please report this error to (schillic@informatik.uni-freiburg.de).");
		}
		
		// construct result with library method
		constructResultFromPartition(mPartition, addMapping);
	}
	
	/**
	 * @return {@code true} iff the construction was interrupted.
	 */
	protected boolean getConstructionInterrupted() {
		return mConstructionInterrupted;
	}
	
	/**
	 * Represents a return transition without the letter.
	 */
	protected class ReturnTransition {
		private final STATE mLin;
		private final STATE mHier;
		private final STATE mSucc;
		
		/**
		 * @param lin
		 *            linear predecessor state
		 * @param hier
		 *            hierarchical predecessor state
		 * @param succ
		 *            successor state
		 */
		protected ReturnTransition(final STATE lin, final STATE hier, final STATE succ) {
			mLin = lin;
			mHier = hier;
			mSucc = succ;
		}
		
		/**
		 * @return Linear predecessor state.
		 */
		public STATE getLin() {
			return mLin;
		}
		
		/**
		 * @return Hierarchical predecessor state.
		 */
		public STATE getHier() {
			return mHier;
		}
		
		/**
		 * @return Successor state.
		 */
		public STATE getSucc() {
			return mSucc;
		}
		
		/**
		 * Finds out if return transitions are similar.
		 * To do this, the down state rule is used.
		 * 
		 * @param partition
		 *            partition of the states
		 * @param transition
		 *            return transition
		 * @param letter
		 *            return letter
		 * @return true iff return transitions are similar
		 */
		private boolean isSimilar(final Partition partition,
				final ReturnTransition transition, final LETTER letter) {
			// check first hierarchical states pair
			STATE lin = transition.mLin;
			STATE hier = mHier;
			EquivalenceClass block =
					partition.getEquivalenceClass(transition.mSucc);
			if (!isSimilarHelper(partition, letter, lin, hier, block)) {
				return false;
			}
			
			// check second hierarchical states pair
			lin = mLin;
			hier = transition.mHier;
			block = partition.getEquivalenceClass(mSucc);
			return isSimilarHelper(partition, letter, lin, hier, block);
		}
		
		/**
		 * Helper for isSimilar().
		 * 
		 * @param partition
		 *            partition of the states
		 * @param letter
		 *            return letter
		 * @param lin
		 *            linear predecessor of return transition
		 * @param hier
		 *            hierarchical predecessor of return transition
		 * @param equivalenceClass
		 *            equivalence class of successor state
		 * @return true iff return transitions are similar
		 */
		private boolean isSimilarHelper(final Partition partition, final LETTER letter,
				final STATE lin, final STATE hier, final EquivalenceClass equivalenceClass) {
			return !mDoubleDecker.isDoubleDecker(lin, hier)
					|| (checkExistenceOfSimilarTransition(partition, partition.succReturn(lin, hier, letter),
							equivalenceClass));
		}
		
		/**
		 * Checks if there is a successor state equivalent to the old one.
		 * 
		 * @param partition
		 *            partition of the states
		 * @param iterable
		 *            collection of possible successor states
		 * @param equivalenceClass
		 *            equivalence class of successor state
		 * @return true iff there is an equivalent successor state
		 */
		private boolean checkExistenceOfSimilarTransition(
				final Partition partition,
				final Iterable<OutgoingReturnTransition<LETTER, STATE>> iterable,
				final EquivalenceClass equivalenceClass) {
			for (final OutgoingReturnTransition<LETTER, STATE> candidate : iterable) {
				final STATE succ = candidate.getSucc();
				if (partition.getEquivalenceClass(succ).equals(
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
			builder.append(mLin.toString());
			builder.append(", ");
			builder.append(mHier.toString());
			builder.append(", ");
			builder.append(mSucc.toString());
			builder.append(")");
			return builder.toString();
		}
	}
	
	/**
	 * Finds the predecessor set of a target set with respect to a letter.
	 */
	abstract class APredecessorSetFinder {
		// partition object
		protected Partition mPartition;
		protected TargetSet mTargetSet;
		
		/**
		 * @param partition
		 *            partition of the states
		 * @param targetSet
		 *            target set
		 */
		public APredecessorSetFinder(final Partition partition, final TargetSet targetSet) {
			mPartition = partition;
			mTargetSet = targetSet;
		}
		
		/**
		 * Finds the predecessor set of A and adds it to X.
		 * 
		 * @param letter
		 *            letter
		 * @return predecessor set X
		 */
		protected PredecessorSet find(final LETTER letter) {
			final PredecessorSet x = new PredecessorSet();
			final Iterator<STATE> iterator = mTargetSet.iterator();
			while (iterator.hasNext()) {
				final STATE state = iterator.next();
				addPred(state, letter, x);
			}
			return x;
		}
		
		/**
		 * Adds predecessor states.
		 * 
		 * @param state
		 *            state
		 * @param letter
		 *            letter
		 * @param predSet
		 *            predecessor set
		 */
		protected void addPred(final STATE state,
				final LETTER letter, final PredecessorSet predSet) {
			throw new AbstractMethodError();
		}
	}
	
	/**
	 * Finds the predecessor set of a target set given an internal letter.
	 */
	class InternalPredecessorSetFinder extends APredecessorSetFinder {
		/**
		 * @param partition
		 *            partition of the states
		 * @param targetSet
		 *            target set
		 */
		public InternalPredecessorSetFinder(final Partition partition, final TargetSet targetSet) {
			super(partition, targetSet);
		}
		
		/**
		 * Adds internal predecessor states.
		 * 
		 * @param state
		 *            state
		 * @param letter
		 *            internal letter
		 * @param predSet
		 *            predecessor set
		 */
		@Override
		protected void addPred(final STATE state,
				final LETTER letter, final PredecessorSet predSet) {
			mPartition.addPredInternal(state, letter, predSet);
		}
	}
	
	/**
	 * Finds the predecessor set of a target set given a call letter.
	 */
	class CallPredecessorSetFinder extends APredecessorSetFinder {
		/**
		 * @param partition
		 *            partition of the states
		 * @param targetSet
		 *            target set
		 */
		public CallPredecessorSetFinder(final Partition partition,
				final TargetSet targetSet) {
			super(partition, targetSet);
		}
		
		/**
		 * Adds call predecessor states.
		 * 
		 * @param state
		 *            state
		 * @param letter
		 *            call letter
		 * @param predSet
		 *            predecessor set
		 */
		@Override
		protected void addPred(final STATE state,
				final LETTER letter, final PredecessorSet predSet) {
			mPartition.addPredCall(state, letter, predSet);
		}
	}
	
	/**
	 * Finds the linear predecessor set of a target set given a return letter.
	 */
	class ReturnPredecessorLinSetFinder extends APredecessorSetFinder {
		/**
		 * @param partition
		 *            partition of the states
		 * @param targetSet
		 *            target set
		 */
		public ReturnPredecessorLinSetFinder(final Partition partition, final TargetSet targetSet) {
			super(partition, targetSet);
		}
		
		/**
		 * Adds linear return predecessor states.
		 * 
		 * @param state
		 *            state
		 * @param letter
		 *            return letter
		 * @param predSet
		 *            predecessor set
		 */
		@Override
		protected void addPred(final STATE state, final LETTER letter, final PredecessorSet predSet) {
			for (final IncomingReturnTransition<LETTER, STATE> inTrans : mPartition.hierPredIncoming(state, letter)) {
				mPartition.addPredReturnLin(state, letter,
						inTrans.getHierPred(), predSet);
			}
		}
	}
	
	/**
	 * Finds the linear predecessor set of a target set given a return letter
	 * and the hierarchical predecessor.
	 */
	class ReturnPredecessorLinSetGivenHierFinder extends APredecessorSetFinder {
		// hierarchical predecessor
		protected STATE mHier;
		
		/**
		 * @param partition
		 *            partition of the states
		 * @param targetSet
		 *            target set
		 * @param hier
		 *            hierarchical predecessor
		 */
		public ReturnPredecessorLinSetGivenHierFinder(final Partition partition,
				final TargetSet targetSet, final STATE hier) {
			super(partition, targetSet);
			mHier = hier;
		}
		
		/**
		 * Adds linear return predecessor states.
		 * 
		 * @param state
		 *            state
		 * @param letter
		 *            return letter
		 * @param predSet
		 *            predecessor set
		 */
		@Override
		protected void addPred(final STATE state, final LETTER letter, final PredecessorSet predSet) {
			mPartition.addPredReturnLin(state, letter, mHier, predSet);
		}
	}
	
	/**
	 * Finds the successor set of a target set given a return letter.
	 */
	class ReturnSuccessorSetFinder extends APredecessorSetFinder {
		/**
		 * @param partition
		 *            partition of the states
		 * @param targetSet
		 *            target set
		 */
		public ReturnSuccessorSetFinder(final Partition partition, final TargetSet targetSet) {
			super(partition, targetSet);
		}
		
		/**
		 * Adds return successor states.
		 * 
		 * @param state
		 *            state
		 * @param letter
		 *            return letter
		 * @param predSet
		 *            successor set
		 */
		@Override
		protected void addPred(final STATE state, final LETTER letter, final PredecessorSet predSet) {
			mPartition.addSuccReturnHier(state, letter, predSet);
		}
	}
	
	/**
	 * Equivalence class for the merge method.
	 * Contains the collection of states
	 * = equivalence class and information if the equivalence class is
	 * also contained in work list.
	 */
	public class EquivalenceClass implements IBlock<STATE> {
		// collection with equivalence class's elements
		private Set<STATE> mCollection;
		// equivalence class is contained in work list
		private boolean mInW;
		// equivalence class is contained in target set
		private boolean mInA;
		// equivalence class contains final/initial states
		private boolean mIsFinal;
		private boolean mIsInitial;
		// intersection collection during the splitting
		private HashSet<STATE> mIntersection;
		// individual ID
		private final int mId;
		// incoming returns
		private boolean mIncomingReturns;
		// split occurred
		private boolean mWasSplit;
		
		/**
		 * Constructor for initial equivalence classes.
		 * 
		 * @param collection
		 *            collection of states for the equivalence class
		 *            must contain at least one element
		 * @param isFinal
		 *            true iff equivalence states are final
		 */
		public EquivalenceClass(final Collection<STATE> collection,
				final boolean isFinal) {
			this(collection, isFinal, true);
		}
		
		/**
		 * Private constructor for initial equivalence classes.
		 * 
		 * @param collection
		 *            collection of states for the equivalence class
		 *            must contain at least one element
		 * @param isFinal
		 *            true iff equivalence states are final
		 * @param inW
		 *            true iff equivalence class shall be put in work list
		 */
		public EquivalenceClass(final Collection<STATE> collection, final boolean isFinal,
				final boolean inW) {
			this(isFinal, inW, false);
			assert (!collection.isEmpty());
			
			if (collection instanceof Set) {
				mCollection = (Set<STATE>) collection;
			} else {
				mCollection = new HashSet<>(computeHashCap(
						collection.size()));
				for (final STATE state : collection) {
					mCollection.add(state);
				}
			}
		}
		
		/**
		 * Private constructor for minor fields.
		 * 
		 * @param isFinal
		 *            true iff states are final
		 * @param inW
		 *            equivalence class is in work list
		 * @param inA
		 *            equivalence class is in target set
		 */
		private EquivalenceClass(final boolean isFinal, final boolean inW, final boolean inA) {
			mIsFinal = isFinal;
			mInW = inW;
			mInA = inA;
			// true because then the real result is computed later
			mWasSplit = true;
			// initially intersection is null
			mIntersection = null;
			mId = mEquivalenceClassId++;
		}
		
		/**
		 * @return true iff two equivalence classes are the same objects.
		 */
		@SuppressWarnings("unchecked")
		@Override
		public boolean equals(final Object obj) {
			if (obj == null) {
				return false;
			}
			if (obj.getClass() == this.getClass()) {
				return mId == ((EquivalenceClass) obj).mId;
			}
			return false;
		}
		
		@Override
		public int hashCode() {
			return mId;
		}
		
		/**
		 * @return Collection of states.
		 */
		Collection<STATE> getCollection() {
			return mCollection;
		}
		
		/**
		 * @return true iff equivalence class is in work list.
		 */
		boolean isInWorkList() {
			return mInW;
		}
		
		/**
		 * Should only be called by the partition object.
		 * 
		 * @param inW
		 *            true iff equivalence class is now in the work list
		 */
		private void setInWorkList(final boolean inW) {
			mInW = inW;
		}
		
		/**
		 * @return true iff equivalence class is in target set.
		 */
		boolean isInTargetSet() {
			return mInA;
		}
		
		/**
		 * @param inA
		 *            true iff equivalence class is in target set
		 */
		void setInTargetSet(final boolean inA) {
			mInA = inA;
		}
		
		@Override
		public boolean isFinal() {
			return mIsFinal;
		}
		
		/**
		 * Setter.
		 */
		void setWasSplit() {
			mWasSplit = true;
		}
		
		/**
		 * @param intersected
		 *            collection of intersected equivalence classes
		 *            needed to remember new intersections
		 * @return collection of states in the intersection
		 */
		Collection<STATE> getIntersection(
				final Collection<EquivalenceClass> intersected) {
			/*
			 * if equivalence class was split the first time during loop,
			 * create a new collection for intersection
			 */
			if (mIntersection == null) {
				mIntersection = new HashSet<>();
				intersected.add(this);
			}
			return mIntersection;
		}
		
		/**
		 * Resets the intersection equivalence class to null.
		 */
		void resetIntersection() {
			// if collection is empty, intersection can be restored
			if (mCollection.isEmpty()) {
				mCollection = mIntersection;
			}
			mIntersection = null;
		}
		
		/**
		 * @return Size of the collection.
		 */
		int size() {
			return mCollection.size();
		}
		
		/**
		 * @return true iff collection is empty.
		 */
		boolean isEmpty() {
			return mCollection.isEmpty();
		}
		
		/**
		 * @param state
		 *            state to add
		 * @return true iff state was not contained before
		 */
		boolean add(final STATE state) {
			return mCollection.add(state);
		}
		
		/**
		 * Moves a state from one equivalence class to intersection.
		 * 
		 * @param state
		 *            state to move
		 * @param intersected
		 *            collection of intersected equivalence classes
		 *            remembered for later computations
		 */
		public void moveState(final STATE state,
				final Collection<EquivalenceClass> intersected) {
			assert mCollection.contains(state);
			mCollection.remove(state);
			getIntersection(intersected).add(state);
		}
		
		/**
		 * Sets the equivalence class as initial.
		 */
		void markAsInitial() {
			mIsInitial = true;
		}
		
		/**
		 * Splits an equivalence class into two.
		 * 
		 * @param partition
		 *            partition of the states
		 * @return split equivalence class
		 */
		public EquivalenceClass split(final Partition partition) {
			final EquivalenceClass intersection =
					new EquivalenceClass(getIntersection(null), isFinal(),
							isInWorkList());
			partition.addEquivalenceClass(intersection);
			mWasSplit = true;
			
			// refresh state mapping
			for (final STATE state : intersection.getCollection()) {
				partition.setEquivalenceClass(state, intersection);
			}
			
			return intersection;
		}
		
		/**
		 * NOTE: is only correct, since the method is always called with
		 * wasSplitDuringSecondPhase() alternately and only at certain points.
		 * 
		 * @param partition
		 *            partition of the states
		 * @return true iff there are states with incoming return transitions
		 */
		boolean hasIncomingReturns(final Partition partition) {
			// if a split occurred, the result has to be recomputed
			if (mWasSplit) {
				mWasSplit = false;
				
				mIncomingReturns = false;
				for (final STATE state : mCollection) {
					if (partition.hasIncomingReturns(state)) {
						mIncomingReturns = true;
						break;
					}
				}
			}
			
			return mIncomingReturns;
		}
		
		/**
		 * NOTE: is only correct, since the method is always called with
		 * hasIncomingReturns() alternately and only at certain points.
		 * 
		 * @return true iff equivalence class was split during second phase
		 */
		boolean wasSplitDuringSecondPhase() {
			if (mWasSplit) {
				mWasSplit = false;
				return true;
			}
			return false;
		}
		
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			
			builder.append("[");
			for (final STATE state : mCollection) {
				builder.append(state.toString());
				builder.append(", ");
			}
			if (builder.length() > 2) {
				builder.delete(builder.length() - 2, builder.length());
			}
			builder.append("]");
			if (mIsFinal) {
				builder.append("f");
			}
			if (mInW) {
				builder.append("w");
			}
			
			return builder.toString();
		}
		
		@Override
		public boolean isInitial() {
			return mIsInitial;
		}
		
		@Override
		public STATE minimize(final IMergeStateFactory<STATE> stateFactory) {
			return stateFactory.merge(mCollection);
		}
		
		@Override
		public Iterator<STATE> statesIterator() {
			return mCollection.iterator();
		}
		
		@Override
		public boolean isRepresentativeIndependentInternalsCalls() {
			return !getConstructionInterrupted();
		}
	}
	
	/**
	 * Collection of equivalence classes and a mapping
	 * 'state -> equivalence class' for fast access.
	 */
	public class Partition implements IPartition<STATE> {
		// original nested word automaton
		private final INestedWordAutomaton<LETTER, STATE> mParentOperand;
		// equivalence classes
		private final LinkedList<EquivalenceClass> mEquivalenceClasses;
		// work list (W) with equivalence classes still to refine
		private final WorkList mWorkList;
		// mapping 'state -> equivalence class'
		private final HashMap<STATE, EquivalenceClass> mMapState2EquivalenceClass;
		
		/**
		 * @param operand
		 *            original nested word automaton
		 * @param states
		 *            number of states (avoids rehashing)
		 */
		Partition(final INestedWordAutomaton<LETTER, STATE> operand, final int states) {
			mParentOperand = operand;
			mEquivalenceClasses = new LinkedList<>();
			mWorkList = new WorkList(mParentOperand.size() / 2);
			mMapState2EquivalenceClass =
					new HashMap<>(
							computeHashCap(states));
		}
		
		/**
		 * Removes empty equivalence classes.
		 * 
		 * @return true iff there was an empty equivalence class
		 */
		public boolean removeEmptyEquivalenceClasses() {
			final ListIterator<EquivalenceClass> it =
					mEquivalenceClasses.listIterator();
			boolean hadEmptyEc = false;
			while (it.hasNext()) {
				final EquivalenceClass ec = it.next();
				if (ec.isEmpty()) {
					it.remove();
					hadEmptyEc = true;
				}
			}
			return hadEmptyEc;
		}
		
		/**
		 * Marks all respective equivalence classes as initial.
		 */
		public void markInitials() {
			/*
			 * if an equivalence class contains an initial state,
			 * the whole equivalence class should be initial
			 */
			for (final STATE state : mParentOperand.getInitialStates()) {
				final EquivalenceClass ec = mMapState2EquivalenceClass.get(state);
				// null check needed in case state was removed beforehand
				if (ec != null) {
					assert (!ec.isEmpty());
					ec.markAsInitial();
				}
			}
		}
		
		/**
		 * @return All equivalence classes.
		 */
		LinkedList<EquivalenceClass> getEquivalenceClasses() {
			return mEquivalenceClasses;
		}
		
		@Override
		public IBlock<STATE> getBlock(final STATE state) {
			return mMapState2EquivalenceClass.get(state);
		}
		
		@Override
		public int size() {
			return mEquivalenceClasses.size();
		}
		
		/**
		 * @param equivalenceClass
		 *            new equivalence class
		 */
		void addEquivalenceClass(final EquivalenceClass equivalenceClass) {
			mEquivalenceClasses.add(equivalenceClass);
			if (equivalenceClass.isInWorkList()) {
				mWorkList.add(equivalenceClass);
			}
			for (final STATE state : equivalenceClass.getCollection()) {
				mMapState2EquivalenceClass.put(state, equivalenceClass);
			}
		}
		
		/**
		 * @param state
		 *            state in equivalence class
		 * @return equivalence class containing the state
		 */
		EquivalenceClass getEquivalenceClass(final STATE state) {
			return mMapState2EquivalenceClass.get(state);
		}
		
		/**
		 * @param state
		 *            state for equivalence class
		 * @param equivalenceClass
		 *            equivalence class
		 */
		protected void setEquivalenceClass(final STATE state,
				final EquivalenceClass equivalenceClass) {
			mMapState2EquivalenceClass.put(state, equivalenceClass);
		}
		
		/**
		 * @return true iff work list is empty.
		 */
		boolean workListIsEmpty() {
			return mWorkList.isEmpty();
		}
		
		/**
		 * @param equivalenceClass
		 *            equivalence class for the work list
		 */
		void addToWorkList(final EquivalenceClass equivalenceClass) {
			mWorkList.add(equivalenceClass);
			equivalenceClass.setInWorkList(true);
		}
		
		/**
		 * Adds all equivalence classes to the work list,
		 * of which a state is reached from a newly outgoing return.
		 * 
		 * @param equivalenceClass
		 *            equivalence class with states from
		 *            predecessor set of which return successors are to be
		 *            added to the work list
		 */
		void addReturnsToWorkList(final EquivalenceClass equivalenceClass) {
			final Collection<STATE> collection = equivalenceClass.getCollection();
			final Iterator<STATE> iterator = collection.iterator();
			while (iterator.hasNext()) {
				final STATE state = iterator.next();
				
				// successors via linear edge
				for (final LETTER letter : mParentOperand.lettersReturn(state)) {
					final Iterable<STATE> hierPreds = hierPred(state, letter);
					for (final STATE hier : hierPreds) {
						final Iterable<OutgoingReturnTransition<LETTER, STATE>> succStates =
								succReturn(state, hier, letter);
						for (final OutgoingReturnTransition<LETTER, STATE> trans : succStates) {
							final STATE succ = trans.getSucc();
							final EquivalenceClass ec = getEquivalenceClass(succ);
							if (!ec.isInWorkList()) {
								addToWorkList(ec);
							}
						}
					}
				}
				
				// successors via hierarchical edge
				for (final SummaryReturnTransition<LETTER, STATE> trans : mParentOperand.summarySuccessors(state)) {
					final EquivalenceClass ec = getEquivalenceClass(trans.getSucc());
					if (!ec.isInWorkList()) {
						addToWorkList(ec);
					}
				}
			}
		}
		
		/**
		 * @return Next equivalence class in the work list.
		 */
		EquivalenceClass popFromWorkList() {
			final EquivalenceClass ec = mWorkList.pop();
			ec.setInWorkList(false);
			return ec;
		}
		
		/**
		 * @param state
		 *            state
		 * @return true iff state has an incoming return transition
		 */
		public boolean hasIncomingReturns(final STATE state) {
			return !mParentOperand.lettersReturnIncoming(state).isEmpty();
		}
		
		/**
		 * Finds successor states
		 * (for avoiding states that have already been removed).
		 * 
		 * @param states
		 *            set of target states
		 */
		private Collection<STATE> neighbors(final Iterable<STATE> states) {
			final LinkedList<STATE> result = new LinkedList<>();
			for (final STATE s : states) {
				if (mMapState2EquivalenceClass.get(s) != null) {
					result.add(s);
				}
			}
			return result;
		}
		
		Iterable<OutgoingInternalTransition<LETTER, STATE>> succInternal(
				final STATE state, final LETTER letter) {
			return mParentOperand.internalSuccessors(state, letter);
		}
		
		Iterable<OutgoingCallTransition<LETTER, STATE>> succCall(
				final STATE state, final LETTER letter) {
			return mParentOperand.callSuccessors(state, letter);
		}
		
		Iterable<OutgoingReturnTransition<LETTER, STATE>> succReturn(
				final STATE state, final STATE hier, final LETTER letter) {
			return mParentOperand.returnSuccessors(state, hier, letter);
		}
		
		Iterable<STATE> hierPred(final STATE state, final LETTER letter) {
			return mParentOperand.hierarchicalPredecessorsOutgoing(state, letter);
		}
		
		Iterable<IncomingReturnTransition<LETTER, STATE>> linPredIncoming(
				final STATE state, final STATE hier, final LETTER letter) {
			return mParentOperand.returnPredecessors(state, hier, letter);
		}
		
		Iterable<IncomingReturnTransition<LETTER, STATE>> hierPredIncoming(
				final STATE state, final LETTER letter) {
			return mParentOperand.returnPredecessors(state, letter);
		}
		
		/**
		 * Finds predecessor states and directly adds elements to the set.
		 * 
		 * @param states
		 *            target states of edges
		 * @param predSet
		 *            predecessor set
		 */
		private void addNeighbors(final Iterable<STATE> states,
				final PredecessorSet predSet) {
			for (final STATE s : states) {
				if (mMapState2EquivalenceClass.get(s) != null) {
					predSet.add(s);
				}
			}
		}
		
		/**
		 * Finds predecessor states and directly adds elements to the set.
		 * More efficient variant if no states were removed.
		 * 
		 * @param states
		 *            target states of edges
		 * @param predSet
		 *            predecessor set
		 */
		private void addNeighborsEfficient(final Iterable<STATE> states,
				final PredecessorSet predSet) {
			for (final STATE s : states) {
				predSet.add(s);
			}
		}
		
		private void addNeighborsEfficientLin(
				final Iterable<IncomingReturnTransition<LETTER, STATE>> transitions,
				final PredecessorSet predSet) {
			for (final IncomingReturnTransition<LETTER, STATE> inTrans : transitions) {
				predSet.add(inTrans.getLinPred());
			}
		}
		
		private void addNeighborsEfficientHier(
				final Iterable<IncomingReturnTransition<LETTER, STATE>> transitions,
				final PredecessorSet predSet) {
			for (final IncomingReturnTransition<LETTER, STATE> inTrans : transitions) {
				predSet.add(inTrans.getHierPred());
			}
		}
		
		void addPredInternal(final STATE state, final LETTER letter, final PredecessorSet predSet) {
			addNeighborsEfficient(new InternalTransitionIterator(
					mParentOperand.internalPredecessors(state, letter)), predSet);
		}
		
		void addPredCall(final STATE state, final LETTER letter, final PredecessorSet predSet) {
			addNeighborsEfficient(new CallTransitionIterator(
					mParentOperand.callPredecessors(state, letter)), predSet);
		}
		
		void addPredReturnLin(final STATE state, final LETTER letter,
				final STATE hier, final PredecessorSet predSet) {
			addNeighborsEfficientLin(mParentOperand.returnPredecessors(
					state, hier, letter), predSet);
		}
		
		void addPredReturnHier(final STATE state, final LETTER letter, final PredecessorSet predSet) {
			addNeighborsEfficientHier(
					mParentOperand.returnPredecessors(state, letter), predSet);
		}
		
		void addSuccReturnHier(final STATE state, final LETTER letter, final PredecessorSet predSet) {
			final HashSet<STATE> hierSet = new HashSet<>();
			for (final STATE hier : mParentOperand.hierarchicalPredecessorsOutgoing(state, letter)) {
				hierSet.add(hier);
			}
			addNeighborsEfficient(hierSet, predSet);
		}
		
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			
			builder.append("{ ");
			for (final EquivalenceClass block : mEquivalenceClasses) {
				builder.append(block.toString());
				builder.append(",\n");
			}
			if (builder.length() > 2) {
				builder.delete(builder.length() - 2, builder.length());
			}
			builder.append(" }");
			
			return builder.toString();
		}
		
		@Override
		public Iterator<IBlock<STATE>> blocksIterator() {
			return new Iterator<IBlock<STATE>>() {
				protected Iterator<EquivalenceClass> mIt =
						mEquivalenceClasses.iterator();
				
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
		
		/**
		 * Iterable for internal transitions.
		 */
		class InternalTransitionIterator implements Iterable<STATE> {
			protected final Iterable<IncomingInternalTransition<LETTER, STATE>> mIterable;
			
			public InternalTransitionIterator(
					final Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors) {
				mIterable = internalPredecessors;
			}
			
			@Override
			public Iterator<STATE> iterator() {
				final Iterator<IncomingInternalTransition<LETTER, STATE>> mIt =
						mIterable.iterator();
				return new Iterator<STATE>() {
					@Override
					public boolean hasNext() {
						return mIt.hasNext();
					}
					
					@Override
					public STATE next() {
						return mIt.next().getPred();
					}
				};
			}
		}
		
		/**
		 * Iterable for call transitions.
		 */
		class CallTransitionIterator implements Iterable<STATE> {
			protected final Iterable<IncomingCallTransition<LETTER, STATE>> mIterable;
			
			public CallTransitionIterator(
					final Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors) {
				mIterable = callPredecessors;
			}
			
			@Override
			public Iterator<STATE> iterator() {
				final Iterator<IncomingCallTransition<LETTER, STATE>> mIt =
						mIterable.iterator();
				return new Iterator<STATE>() {
					@Override
					public boolean hasNext() {
						return mIt.hasNext();
					}
					
					@Override
					public STATE next() {
						return mIt.next().getPred();
					}
				};
			}
		}
	}
	
	/**
	 * Target set 'A' of which the predecessor set is computed.
	 * In order to get valid results, the original equivalence class A has to
	 * be remembered somehow, since it can be destroyed during the splitting.
	 * <p>
	 * NOTE: The iterator must be used in 'hasNext()-loop'
	 * and with no change to the equivalence classes during iteration.
	 */
	class TargetSet {
		protected LinkedList<EquivalenceClass> mEquivalenceClasses;
		
		/**
		 * @param firstEquivalenceClass
		 *            first equivalence class
		 *            (must not be null)
		 */
		public TargetSet(final EquivalenceClass firstEquivalenceClass) {
			assert firstEquivalenceClass != null;
			mEquivalenceClasses = new LinkedList<>();
			mEquivalenceClasses.add(firstEquivalenceClass);
			firstEquivalenceClass.setInTargetSet(true);
		}
		
		/**
		 * NOTE: This is only correct if used in 'hasNext()-loop',
		 * but therefore needs less overhead.
		 * NOTE: This is only correct if no further equivalence classes are added
		 * during iteration.
		 * 
		 * @return iterator over all states
		 */
		Iterator<STATE> iterator() {
			return new Iterator<STATE>() {
				private final ListIterator<EquivalenceClass> mListIterator =
						mEquivalenceClasses.listIterator();
				private Iterator<STATE> mEquivalenceClassIterator;
				private STATE mNext = initialize();
				
				@Override
				public boolean hasNext() {
					return mNext != null;
				}
				
				@Override
				public STATE next() {
					assert mNext != null;
					
					// next element already computed before
					final STATE result = mNext;
					
					// compute next element
					computeNext();
					
					return result;
				}
				
				private STATE initialize() {
					mEquivalenceClassIterator =
							mListIterator.next().getCollection().iterator();
					computeNext();
					return mNext;
				}
				
				private void computeNext() {
					if (mEquivalenceClassIterator.hasNext()) {
						mNext = mEquivalenceClassIterator.next();
					} else {
						while (mListIterator.hasNext()) {
							mEquivalenceClassIterator =
									mListIterator.next().getCollection().iterator();
							
							if (mEquivalenceClassIterator.hasNext()) {
								mNext = mEquivalenceClassIterator.next();
								return;
							}
						}
						
						mNext = null;
					}
				}
				
				@Override
				public void remove() {
					throw new UnsupportedOperationException();
				}
			};
		}
		
		/**
		 * @param equivalenceClass
		 *            new equivalence class
		 */
		void addEquivalenceClass(final EquivalenceClass equivalenceClass) {
			mEquivalenceClasses.add(equivalenceClass);
			equivalenceClass.setInTargetSet(true);
		}
		
		/**
		 * Delete object and reset flag in equivalence class objects.
		 */
		void delete() {
			for (final EquivalenceClass block : mEquivalenceClasses) {
				block.setInTargetSet(false);
			}
			
			mEquivalenceClasses = null;
		}
		
		/**
		 * @return true iff equivalence class is empty.
		 */
		boolean isEmpty() {
			return !iterator().hasNext();
		}
		
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			builder.append("{");
			
			for (final EquivalenceClass block : mEquivalenceClasses) {
				builder.append(block.toString());
				builder.append("\n");
			}
			builder.append("}");
			
			return builder.toString();
		}
	}
	
	/**
	 * Work list which is roughly sorted by size (small < big).
	 * <p>
	 * NOTE: The ordering is not assured, since equivalence classes often change
	 * size, which results in reordering, which again is not efficient,
	 * since PriorityQueue does not offer a decreaseKey() method.
	 */
	class WorkList {
		protected PriorityQueue<EquivalenceClass> mQueue;
		
		/**
		 * Constructor.
		 */
		public WorkList(int size) {
			if (size == 0) {
				// special case where automaton has no reachable states
				size = 1;
			}
			mQueue = new PriorityQueue<>(size, (ec1, ec2) -> ec1.size() - ec2.size());
		}
		
		/**
		 * @param equivalenceClass
		 *            equivalence class to add
		 */
		public void add(final EquivalenceClass equivalenceClass) {
			assert (!mQueue.contains(equivalenceClass));
			mQueue.add(equivalenceClass);
		}
		
		/**
		 * @return Next equivalence class according to the ordering.
		 */
		public EquivalenceClass pop() {
			return mQueue.poll();
		}
		
		/**
		 * @return true iff work list is empty.
		 */
		public boolean isEmpty() {
			return mQueue.isEmpty();
		}
		
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			
			builder.append("{");
			builder.append(mQueue.toString());
			builder.append("}");
			
			return builder.toString();
		}
	}
	
	/**
	 * Representation of the collection of predecessor states.
	 */
	class PredecessorSet {
		protected HashSet<STATE> mCollection;
		
		/**
		 * Constructor.
		 */
		public PredecessorSet() {
			this(new HashSet<STATE>());
		}
		
		/**
		 * @param hashSet
		 *            hash set of states
		 */
		public PredecessorSet(final HashSet<STATE> hashSet) {
			assert hashSet != null;
			mCollection = hashSet;
		}
		
		/**
		 * @return Iterator for the collection.
		 */
		Iterator<STATE> iterator() {
			return mCollection.iterator();
		}
		
		/**
		 * @param state
		 *            state to add
		 */
		void add(final STATE state) {
			mCollection.add(state);
		}
		
		/**
		 * Melds two predecessor sets.
		 * 
		 * @param other
		 *            other predecessor set
		 */
		void meld(final PredecessorSet other) {
			mCollection.addAll(other.mCollection);
		}
		
		/**
		 * @return Size of the collection.
		 */
		int size() {
			return mCollection.size();
		}
		
		/**
		 * @return true iff collection is empty.
		 */
		boolean isEmpty() {
			return mCollection.isEmpty();
		}
		
		/**
		 * Deletes all stored elements.
		 */
		void delete() {
			mCollection = null;
		}
		
		@Override
		public String toString() {
			return mCollection.toString();
		}
	}
	
	/**
	 * Intermediate data storage for states reachable in the automaton.
	 * Already distinguishes between final and non-final states.
	 * Either has a copy of the states or only knows the removed states.
	 */
	class StatesContainer {
		// original nested word automaton
		private final INestedWordAutomaton<LETTER, STATE> mParentOperand;
		// states
		private HashSet<STATE> mFinals;
		private HashSet<STATE> mNonfinals;
		// true iff a real copy is made
		private final StatesContainerMode mMode;
		
		/**
		 * Constructor.
		 */
		StatesContainer(final INestedWordAutomaton<LETTER, STATE> operand) {
			mParentOperand = operand;
			mMode = StatesContainerMode.NONE;
			
			switch (mMode) {
				// if unreachable states shall be removed, make a copy
				case MAKE_COPY:
					mFinals =
							new HashSet<>(computeHashCap(
									mParentOperand.getFinalStates().size()));
					mNonfinals =
							new HashSet<>(computeHashCap(
									mParentOperand.size() - mParentOperand.getFinalStates().size()));
					break;
				/*
				 * if only dead ends shall be removed,
				 * only remember removed states
				 */
				case SAVE_REMOVED:
					mFinals = new HashSet<>();
					mNonfinals = new HashSet<>();
					break;
				// else the sets are not needed
				case NONE:
					mFinals = null;
					mNonfinals = null;
					break;
				default:
					assert false;
			}
		}
		
		/**
		 * Fast notice of trivial automaton.
		 * 
		 * @return true iff there are final states
		 */
		public boolean hasFinals() {
			switch (mMode) {
				case MAKE_COPY:
					return !mFinals.isEmpty();
				case SAVE_REMOVED:
					return ((mParentOperand.getFinalStates().size() - mFinals.size()) > 0);
				case NONE:
					return (!mParentOperand.getFinalStates().isEmpty());
				default:
					assert false;
					return false;
			}
		}
		
		/**
		 * Passes the copied set of states.
		 * Only used in case when states were copied.
		 * 
		 * @return non-final states
		 */
		HashSet<STATE> getNonfinals() {
			assert mMode == StatesContainerMode.MAKE_COPY;
			return mNonfinals;
		}
		
		/**
		 * @return Iterator of non-final states.
		 */
		Iterator<STATE> getNonfinalsIterator() {
			switch (mMode) {
				case MAKE_COPY:
					return mNonfinals.iterator();
				case SAVE_REMOVED:
					return new Iterator<STATE>() {
						private final Iterator<STATE> mIterator =
								mParentOperand.getStates().iterator();
						private STATE mNext = computeNext();
						
						@Override
						public boolean hasNext() {
							return mNext != null;
						}
						
						@Override
						public STATE next() {
							assert mNext != null;
							
							// next element already computed before
							final STATE result = mNext;
							
							// compute next element
							mNext = computeNext();
							
							return result;
						}
						
						private STATE computeNext() {
							STATE nextFound;
							while (mIterator.hasNext()) {
								nextFound = mIterator.next();
								if (!mParentOperand.isFinal(nextFound)
										&& contains(nextFound)) {
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
				case NONE:
					assert false;
					return null;
				default:
					assert false;
					return null;
			}
		}
		
		/**
		 * Passes the copied set of states.
		 * Only used in case when states were copied.
		 * 
		 * @return final states
		 */
		HashSet<STATE> getFinals() {
			assert mMode == StatesContainerMode.MAKE_COPY;
			return mFinals;
		}
		
		/**
		 * NOTE: This is only correct if used in 'hasNext()-loop',
		 * but therefore needs less overhead.
		 * NOTE: This is only correct if no further equivalence classes are added
		 * during iteration.
		 * 
		 * @return iterator of final states
		 */
		Iterator<STATE> getFinalsIterator() {
			switch (mMode) {
				case MAKE_COPY:
					return mFinals.iterator();
				case SAVE_REMOVED:
					return new Iterator<STATE>() {
						private final Iterator<STATE> mIterator =
								mParentOperand.getFinalStates().iterator();
						private STATE mNext = computeNext();
						
						@Override
						public boolean hasNext() {
							return mNext != null;
						}
						
						@Override
						public STATE next() {
							assert mNext != null;
							
							// next element already computed before
							final STATE result = mNext;
							
							// compute next element
							mNext = computeNext();
							
							return result;
						}
						
						private STATE computeNext() {
							STATE nextFound;
							while (mIterator.hasNext()) {
								nextFound = mIterator.next();
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
				case NONE:
					return mParentOperand.getFinalStates().iterator();
				default:
					assert false;
					return null;
			}
		}
		
		/**
		 * Number of states removed (only used for hash set initialization).
		 * 
		 * @param finals
		 *            true iff number of final states is needed
		 *            false iff number of non-final states is needed
		 * @return number of removed states
		 */
		int getRemovedSize(final boolean finals) {
			assert (mMode == StatesContainerMode.SAVE_REMOVED);
			
			if (finals) {
				return mFinals.size();
			}
			return mNonfinals.size();
		}
		
		/**
		 * Creates a collection of the non-final states for the merge.
		 * In case of an automaton with no word accepted.
		 * 
		 * @return collection of non-final states
		 */
		Collection<STATE> getTrivialAutomatonStates() {
			switch (mMode) {
				case MAKE_COPY:
					return mNonfinals;
				case SAVE_REMOVED:
					final LinkedList<STATE> result = new LinkedList<>();
					final Iterator<STATE> iterator = getNonfinalsIterator();
					while (iterator.hasNext()) {
						result.add(iterator.next());
					}
					return result;
				case NONE:
					return mParentOperand.getStates();
				default:
					assert false;
					return null;
			}
		}
		
		/**
		 * @return Number of states.
		 */
		int size() {
			switch (mMode) {
				case MAKE_COPY:
					return mFinals.size() + mNonfinals.size();
				case SAVE_REMOVED:
					return mParentOperand.size() - mFinals.size() - mNonfinals.size();
				case NONE:
					return mParentOperand.size();
				default:
					assert false;
					return 0;
			}
		}
		
		/**
		 * @param state
		 *            the state (must be contained in the original automaton)
		 * @return true iff state was not removed
		 */
		boolean contains(final STATE state) {
			switch (mMode) {
				case MAKE_COPY:
					return (mNonfinals.contains(state) || mFinals.contains(state));
				case SAVE_REMOVED:
					return (!(mNonfinals.contains(state) || mFinals.contains(state)));
				case NONE:
					return mParentOperand.getStates().contains(state);
				default:
					assert false;
					return false;
			}
		}
		
		/**
		 * Adds a state.
		 * Only used if copy of states is made.
		 * 
		 * @param state
		 *            new state
		 */
		void addState(final STATE state) {
			switch (mMode) {
				case MAKE_COPY:
					if (mParentOperand.isFinal(state)) {
						mFinals.add(state);
					} else {
						mNonfinals.add(state);
					}
					return;
				case SAVE_REMOVED:
				case NONE:
				default:
					assert false;
					return;
			}
		}
		
		/**
		 * Adds a collection of states.
		 * Only used if copy of states is made.
		 * 
		 * @param states
		 *            collection of new states
		 */
		public void addAll(final Collection<STATE> states) {
			switch (mMode) {
				case MAKE_COPY:
					for (final STATE state : states) {
						addState(state);
					}
					return;
				case SAVE_REMOVED:
				case NONE:
				default:
					assert false;
					return;
			}
		}
		
		/**
		 * @param state
		 *            state to remove
		 */
		void removeState(final STATE state) {
			switch (mMode) {
				case MAKE_COPY:
					if (!mNonfinals.remove(state)) {
						mFinals.remove(state);
					}
					return;
				case SAVE_REMOVED:
					if (mParentOperand.isFinal(state)) {
						mFinals.add(state);
					} else {
						mNonfinals.add(state);
					}
					return;
				case NONE:
				default:
					assert false;
					return;
			}
		}
		
		/**
		 * @return true iff states set is a real copy.
		 */
		boolean wasCopied() {
			return mMode == StatesContainerMode.MAKE_COPY;
		}
		
		/**
		 * Deletes all stored elements.
		 */
		void delete() {
			switch (mMode) {
				case MAKE_COPY:
				case SAVE_REMOVED:
					mFinals = null;
					mNonfinals = null;
					return;
				case NONE:
					return;
				default:
					assert false;
					return;
			}
		}
		
	}
	
	/**
	 * Possible modes of the states container.
	 */
	private enum StatesContainerMode {
		/**
		 * Makes a copy of the used states.
		 */
		MAKE_COPY,
		/**
		 * Makes a copy of the unused states.
		 */
		SAVE_REMOVED,
		/**
		 * Directly passes the states from the original automaton.
		 */
		NONE;
	}
}
