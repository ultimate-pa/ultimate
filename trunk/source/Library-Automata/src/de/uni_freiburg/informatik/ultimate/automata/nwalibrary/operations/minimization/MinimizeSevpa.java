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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
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
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.SummaryReturnTransition;

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
public class MinimizeSevpa<LETTER,STATE> extends AMinimizeNwa<LETTER, STATE> implements IOperation<LETTER,STATE> {
	// old automaton
	private final IDoubleDeckerAutomaton<LETTER, STATE> mDoubleDecker;
	// new (minimized) automaton
	private NestedWordAutomaton<LETTER,STATE> mNwa;
	// ID for equivalence classes
	private int mEquivalenceClassId = 0;
	// Partition of states into equivalence classes
	private Partition mPartition = null;
	// Only true after the result was constructed.
	private boolean mMinimizationFinished = false;
	// map old state -> new state
	private final Map<STATE, STATE> mOldState2newState;
	
	/*
	 * EXPERIMENTAL
	 * deterministic finite automata can be handled more efficiently
	 * 
	 * not even correct for non-total DFAs
	 * but: if non-final states are initially added to the work list,
	 * all examples run with monlyOneToWorkList set to true
	 * (but example 08 is even more reduced, so there IS a difference)
	 */
	private final boolean monlyOneToWorkList = false;
	// use sound but expensive linear return split
	private final boolean msplitAllReturnsLin = false;
	// use sound but expensive hierarchical return split
	private final boolean msplitAllReturnsHier = false;
	
	private final boolean STATISTICS = false;
	private int msplitsWithChange = 0;
	private int msplitsWithoutChange = 0;
	
	/* EXPERIMENTAL END */
	
	
	/**
	 * StateFactory used for the construction of new states. This is _NOT_ the
	 * state factory relayed to the new automaton.
	 * Necessary because the Automizer needs a special StateFactory during
	 * abstraction refinement (for computation of HoareAnnotation).
	 */
	private final StateFactory<STATE> mStateFactoryConstruction;
	
	/**
	 * creates a copy of operand where non-reachable states are omitted
	 * 
	 * @param operand nested word automaton to minimize
	 * @throws AutomataOperationCanceledException iff cancel signal is received
	 */
	public MinimizeSevpa(AutomataLibraryServices services,
			INestedWordAutomaton<LETTER,STATE> operand)
			throws AutomataLibraryException {
		this(services, operand, null, operand.getStateFactory(), false);
	}
	
	/**
	 * creates a copy of operand with an initial partition
	 * 
	 * @param operand nested word automaton to minimize
	 * @param equivalenceClasses represent initial equivalence classes
	 * @param removeUnreachables true iff removal of unreachable states is used
	 * @param removeDeadEnds true iff removal of dead-end states is used
	 * @param addMapOldState2newState add map old state 2 new state?
	 * @throws AutomataOperationCanceledException iff cancel signal is received
	 */
	public MinimizeSevpa(
			final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER,STATE> operand,
			final Collection<Set<STATE>> equivalenceClasses,
			final StateFactory<STATE> stateFactoryConstruction,
			final boolean addMapOldState2newState)
					throws AutomataOperationCanceledException {
		super(services, stateFactoryConstruction, "minimizeSevpa", operand);
		if (operand instanceof IDoubleDeckerAutomaton<?, ?>) {
			mDoubleDecker = (IDoubleDeckerAutomaton<LETTER, STATE>)operand;
		}
		else {
			throw new IllegalArgumentException(
					"Operand must be an IDoubleDeckerAutomaton.");
		}
		mStateFactoryConstruction = stateFactoryConstruction;
		
		// must be the last part of the constructor
		final QuotientNwaConstructor<LETTER, STATE> quotientNwaConstructor =
				minimize(equivalenceClasses, addMapOldState2newState);
		mNwa = quotientNwaConstructor.getResult();
		mOldState2newState = (addMapOldState2newState
				? quotientNwaConstructor.getOldState2newState()
				: null);
		mMinimizationFinished = true;
		mLogger.info(exitMessage());

		if (STATISTICS) {
			System.out.println("positive splits: " + msplitsWithChange);
			System.out.println("negative splits: " + msplitsWithoutChange);
			System.out.println("quote (p/n): " +
					(msplitsWithChange / Math.max(msplitsWithoutChange, 1)));
		}
	}
	
	/**
	 * minimization technique for deterministic finite automata by Hopcroft
	 * (http://en.wikipedia.org/wiki/DFA_minimization)
	 * 
	 * @param equivalenceClasses initial partition of the states
	 * @param addMapOldState2newState add map old state 2 new state?
	 * @return quotient automaton
	 * @throws AutomataOperationCanceledException iff cancel signal is received
	 */
	private QuotientNwaConstructor<LETTER, STATE> minimize(
			final Collection<Set<STATE>> equivalenceClasses,
			final boolean addMapOldState2newState)
					throws AutomataOperationCanceledException {
		
		// intermediate container for the states
		final StatesContainer states = new StatesContainer(mOperand);
		
		// cancel if signal is received
		if (!mServices.getProgressMonitorService().continueProcessing()) {
			throw new AutomataOperationCanceledException(this.getClass());
		}
		
		// merge non-distinguishable states
		final QuotientNwaConstructor<LETTER, STATE> result =
				mergeStates(states, equivalenceClasses, addMapOldState2newState);
		return result;
	}
	
	/**
	 * merges states that are not distinguishable
	 * (based on Hopcroft's algorithm)
	 * 
	 * @param states container with reachable states (gets deleted)
	 * @param equivalenceClasses initial partition of the states
	 * @param addMapOldState2newState add map old state 2 new state?
	 * @return quotient automaton
	 * @throws AutomataOperationCanceledException iff cancel signal is received
	 */
	private QuotientNwaConstructor<LETTER, STATE> mergeStates(
			StatesContainer states,
			final Collection<Set<STATE>> equivalenceClasses,
			final boolean addMapOldState2newState)
					throws AutomataOperationCanceledException {
		
		// creation of the initial partition (if not passed in the constructor)
		if (equivalenceClasses == null) {
			assert (mPartition == null);
			mPartition = createInitialPartition(states);
		}
		// construct initial partition using collections from constructor
		else {
			assert (mPartition == null &&
					assertStatesSeparation(equivalenceClasses));
			mPartition = new Partition(mOperand, states.size());
			
			for (final Set<STATE> ecSet : equivalenceClasses) { 
				assert ecSet.size() > 0; 
				mPartition.addEquivalenceClass( 
						new EquivalenceClass(ecSet, 
								mOperand.isFinal(ecSet.iterator().next()))); 
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
		return merge(addMapOldState2newState);
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
		else {
			finals = new HashSet<STATE>(
					computeHashSetCapacity(mOperand.getFinalStates().size()));
			nonfinals = new HashSet<STATE>(computeHashSetCapacity(
					mOperand.size() - mOperand.getFinalStates().size()));
			for (final STATE state : mOperand.getStates()) {
				if (mOperand.isFinal(state)) {
					finals.add(state);
				}
				else {
					nonfinals.add(state);
				}
			}
		}
		
		// create partition object
		final Partition partition =
				new Partition(mOperand, finals.size() + nonfinals.size());
		
		// set up the initial equivalence classes
		
		// final states
		if (finals.size() > 0) {
			final EquivalenceClass finalsP = new EquivalenceClass(finals, true, true);
			partition.addEquivalenceClass(finalsP);
		}
		
		// non-final states (initially not in work list)
		if (nonfinals.size() > 0) {
			final EquivalenceClass nonfinalsP =
								new EquivalenceClass(nonfinals, false, true);
			partition.addEquivalenceClass(nonfinalsP);
		}
		
		return partition;
	}
	
	/**
	 * iteratively refines partition until fixed point is reached
	 * for each letter finds the set of predecessor states (X)
	 * 
	 * @throws AutomataOperationCanceledException iff cancel signal is received
	 */
	private void refinePartition()
			throws AutomataOperationCanceledException {
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
			// fixed point iteration
			while (! mPartition.workListIsEmpty()) {
				
				// A = next equivalence class from W, also called target set
				final TargetSet a = new TargetSet(mPartition.popFromWorkList());
				assert !a.isEmpty();
				
				// collect all incoming letters (and outgoing returns)
				HashSet<LETTER> internalLetters, callLetters,
								returnLettersOutgoing;
				final HashSet<LETTER> returnLetters = new HashSet<LETTER>();
				
				if (naiveSplit) {
					internalLetters = new HashSet<LETTER>();
					callLetters = new HashSet<LETTER>();
					returnLettersOutgoing = new HashSet<LETTER>();
					
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
				}
				else {
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
				if (!mServices.getProgressMonitorService().continueProcessing()) {
					throw new AutomataOperationCanceledException(this.getClass());
				}
			}
			
			// after the first iteration the complicated split is executed
			if (firstIteration) {
				firstIteration = false;
			}
			// termination criterion: complicated split did not change anything
			else {
				if (mPartition.getEquivalenceClasses().size() ==
						equivalenceClasses) {
					break;
				}
				assert (mPartition.getEquivalenceClasses().size() >
						equivalenceClasses);
			}

			naiveSplit = !naiveSplit;
			equivalenceClasses = mPartition.getEquivalenceClasses().size();
			putAllToWorkList(mPartition, naiveSplit);
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
		for (final LETTER letter : alphabet) {
			
			/*
			 * X = predecessor set of A = all states s1
			 * with transition (s1, l, s2) for letter l and s2 in A
			 */
			final PredecessorSet x = predecessorFinder.find(letter);
			
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
		for (final LETTER letter : alphabet) {
			
			// trivial split: every linear predecessor is different
			if (msplitAllReturnsLin) {
				final ReturnPredecessorLinSetFinder finder =
						new ReturnPredecessorLinSetFinder(partition, a);
				final PredecessorSet x = finder.find(letter);
				final Iterator<STATE> iterator = x.iterator();
				while (iterator.hasNext()) {
					final HashSet<STATE> hashSet =
							new HashSet<STATE>(computeHashSetCapacity(1));
					hashSet.add(iterator.next());
					final PredecessorSet x2 = new PredecessorSet(hashSet);
					
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
				final HashMap<EquivalenceClass, HashSet<STATE>> ec2linSet =
						new HashMap<EquivalenceClass, HashSet<STATE>>();
				
				final Iterator<STATE> iterator = a.iterator();
				while (iterator.hasNext()) {
					final STATE state = iterator.next();
					for (final IncomingReturnTransition<LETTER, STATE> inTrans : 
								partition.hierPredIncoming(state, letter)) {
						final EquivalenceClass ec = partition.getEquivalenceClass(
								inTrans.getHierPred());
						HashSet<STATE> linSet = ec2linSet.get(ec);
						if (linSet == null) {
							linSet = new HashSet<STATE>();
							ec2linSet.put(ec, linSet);
						}
						for (final IncomingReturnTransition<LETTER, STATE> inTransInner :
								partition.linPredIncoming(state,
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
		for (final LETTER letter : alphabet) {
			
			// trivial split: every linear predecessor is different
			if (msplitAllReturnsHier) {
				// find all hierarchical predecessors of the states in A
				final Iterator<STATE> iterator = a.iterator();
				final Collection<STATE> hierPreds = new HashSet<STATE>();
				while (iterator.hasNext()) {
					for (final IncomingReturnTransition<LETTER, STATE> inTrans : 
							partition.hierPredIncoming(iterator.next(), letter)) {
						hierPreds.add(inTrans.getHierPred());
					}
				}
				
				for (final STATE hier : hierPreds) {
					final HashSet<STATE> hashSet =
							new HashSet<STATE>(computeHashSetCapacity(1));
					hashSet.add(hier);
					final PredecessorSet x = new PredecessorSet(hashSet);
					
					searchY(partition, a, x);
				}
			}
			/*
			 * only hierarchical predecessors with linear predecessors
			 * from different equivalence classes are split
			 */
			else {
				// distinguish linear predecessors by equivalence classes
				final HashMap<EquivalenceClass, HashSet<STATE>> ec2hierSet =
						new HashMap<EquivalenceClass, HashSet<STATE>>();
				final Iterator<STATE> iterator = a.iterator();
				while (iterator.hasNext()) {
					final STATE state = iterator.next();
					for (final IncomingReturnTransition<LETTER, STATE> inTrans :
							partition.hierPredIncoming(state, letter)) {
						final STATE hier = inTrans.getHierPred();
						final STATE lin = inTrans.getLinPred();
						final EquivalenceClass ec =
								partition.getEquivalenceClass(lin);
						HashSet<STATE> set = ec2hierSet.get(ec);
						if (set == null) {
							set = new HashSet<STATE>();
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
		for (final LETTER letter : alphabet) {
			
			// maps hierarchical states to linear states to return transitions
			final HashMap<EquivalenceClass,
				HashMap<EquivalenceClass, List<Set<ReturnTransition>>>>
					hier2lin2trans = new HashMap<EquivalenceClass,
					HashMap<EquivalenceClass, List<Set<ReturnTransition>>>>();
			
			final Iterator<STATE> iterator = a.iterator();
			// for each successor state 'state' in A:
			while (iterator.hasNext()) {
				final STATE state = iterator.next();
				final HashSet<STATE> hierVisited = new HashSet<STATE>();
				
				// for each hierarchical predecessor 'hier' of 'state':
				for (final IncomingReturnTransition<LETTER, STATE> inTrans :
						partition.hierPredIncoming(state, letter)) {
					final STATE hier = inTrans.getHierPred();
					
					// new change: ignore duplicate work
					if (! hierVisited.add(hier)) {
						continue;
					}
					
					final EquivalenceClass ecHier =
							partition.getEquivalenceClass(hier);
					
					HashMap<EquivalenceClass, List<Set<ReturnTransition>>>
							lin2trans = hier2lin2trans.get(ecHier);
					if (lin2trans == null) {
						lin2trans =  new HashMap<EquivalenceClass,
												List<Set<ReturnTransition>>>();
						hier2lin2trans.put(ecHier, lin2trans);
					}
					
					// for each linear predecessor 'lin' of 'state' and 'hier':
					for (final IncomingReturnTransition<LETTER, STATE> inTransInner :
							partition.linPredIncoming(state, hier, letter)) {
						final STATE lin = inTransInner.getLinPred();
						final EquivalenceClass ecLin =
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
						final ReturnTransition transition =
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
		for (final Set<ReturnTransition> result : similarSetsList) {
			boolean found = true;
			
			// compare with each transition in the set
			for (final ReturnTransition trans : result) {
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
		for (final HashMap<EquivalenceClass, List<Set<ReturnTransition>>> lin2trans :
				hier2lin2trans.values()) {
			for (final List<Set<ReturnTransition>> similarSetsList :
					lin2trans.values()) {
				// for each set of similar states perform a split
				for (final Set<ReturnTransition> similarSet : similarSetsList) {
					// set up linear and hierarchical predecessor sets
					final int size = computeHashSetCapacity(similarSet.size());
					final HashSet<STATE> lins = new HashSet<STATE>(size);
					final HashSet<STATE> hiers = new HashSet<STATE>(size);
					for (final ReturnTransition trans : similarSet) {
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
		for (final LETTER letter : alphabet) {
			/*
			 * X = predecessor set of A in hierarchical view
			 * = all states h with transition (s1, l, h, s2) for s1 in A
			 */
			final PredecessorSet x = predecessorFinder.find(letter);
			
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
		final LinkedList<EquivalenceClass> intersected =
				new LinkedList<EquivalenceClass>();
		
		// iteratively splits equivalence classes with elements from X
		final Iterator<STATE> iterator = x.iterator();
		while (iterator.hasNext()) {
			final STATE state = iterator.next();
			
			// find equivalence class Y
			final EquivalenceClass y = partition.getEquivalenceClass(state);
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
		for (final EquivalenceClass ec : intersected) {
			/*
			 * if Y is empty, then the intersection is not needed
			 * and the states can be restored 
			 */
			if (!ec.isEmpty()) {
				++msplitsWithChange;
				
				// create new equivalence class
				final EquivalenceClass intersection = ec.split(partition);
				
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
					 * NOTE: see note for monlyOneToWorkList
					 */
					if (monlyOneToWorkList) {
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
				++msplitsWithoutChange;
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
			for (final EquivalenceClass ec : partition.getEquivalenceClasses()) {
				if (ec.wasSplitDuringSecondPhase()) {
					partition.addToWorkList(ec);
				}
			}
		}
		// only collect equivalence classes with incoming return transitions
		else {
			for (final EquivalenceClass ec : partition.getEquivalenceClasses()) {
				if (ec.hasIncomingReturns(partition)) {
					partition.addToWorkList(ec);
				}
			}
		}
	}
	
	/**
	 * merges states from computed equivalence classes
	 * 
	 * @param addMapOldState2newState add map old state 2 new state?
	 * @return quotient automaton
	 */
	private QuotientNwaConstructor<LETTER, STATE> merge(
			final boolean addMapOldState2newState) {
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
					"Please report this error to <schillic@informatik.uni-freiburg.de>.");
		}
		
		// construct result with library method
		final QuotientNwaConstructor<LETTER, STATE> quotientNwaConstructor =
				new QuotientNwaConstructor<>(mServices,
						mStateFactoryConstruction, mDoubleDecker, mPartition,
						addMapOldState2newState);
		
		return quotientNwaConstructor;
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
		private final STATE mlin, mhier, msucc;
		
		/**
		 * @param lin linear predecessor state
		 * @param hier hierarchical predecessor state
		 * @param succ successor state
		 */
		protected ReturnTransition(STATE lin, STATE hier, STATE succ) {
			this.mlin = lin;
			this.mhier = hier;
			this.msucc = succ;
		}
		
		/**
		 * @return linear predecessor state
		 */
		public STATE getLin() {
			return mlin;
		}
		
		/**
		 * @return hierarchical predecessor state
		 */
		public STATE getHier() {
			return mhier;
		}
		
		/**
		 * @return successor state
		 */
		public STATE getSucc() {
			return msucc;
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
			STATE lin = transition.mlin;
			STATE hier = this.mhier;
			EquivalenceClass ec =
					partition.getEquivalenceClass(transition.msucc);
			if (! isSimilarHelper(partition, letter, lin, hier, ec)) {
				return false;
			}
			
			// check second hierarchical states pair
			lin = this.mlin;
			hier = transition.mhier;
			ec = partition.getEquivalenceClass(this.msucc);
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
			if (mDoubleDecker.isDoubleDecker(lin, hier)) {
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
		 * @param iterable collection of possible successor states
		 * @param equivalenceClass equivalence class of successor state 
		 * @return true iff there is an equivalent successor state 
		 */
		private boolean checkExistenceOfSimilarTransition(
				Partition partition,
				Iterable<OutgoingReturnTransition<LETTER, STATE>> iterable,
				EquivalenceClass equivalenceClass) {
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
			builder.append(mlin.toString());
			builder.append(", ");
			builder.append(mhier.toString());
			builder.append(", ");
			builder.append(msucc.toString());
			builder.append(")");
			return builder.toString();
		}
	}
	
	/**
	 * finds the predecessor set of a target set with respect to a letter
	 */
	abstract class APredecessorSetFinder {
		// partition object
		Partition mpartition;
		TargetSet ma;
		
		/**
		 * @param partition partition of the states
		 * @param a target set
		 */
		public APredecessorSetFinder(Partition partition,
										TargetSet a) {
			this.mpartition = partition;
			this.ma = a;
		}
		
		/**
		 * finds the predecessor set of A and adds it to X
		 * 
		 * @param letter letter
		 * @return predecessor set X
		 */
		protected PredecessorSet find(LETTER letter) {
			final PredecessorSet x = new PredecessorSet();
			final Iterator<STATE> iterator = ma.iterator();
			while (iterator.hasNext()) {
				final STATE state = iterator.next();
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
			mpartition.addPredInternal(state, letter, x);
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
			mpartition.addPredCall(state, letter, x);
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
		public ReturnPredecessorLinSetFinder(Partition partition, TargetSet a) {
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
		protected void addPred(STATE state, LETTER letter, PredecessorSet x) {
			for (final IncomingReturnTransition<LETTER, STATE> inTrans :
					mpartition.hierPredIncoming(state, letter)) {
				mpartition.addPredReturnLin(state, letter,
						inTrans.getHierPred(), x);
			}
		}
	}
	
	/**
	 * finds the linear predecessor set of a target set given a return letter
	 * and the hierarchical predecessor
	 */
	class ReturnPredecessorLinSetGivenHierFinder extends APredecessorSetFinder {
		// hierarchical predecessor
		STATE mhier;
		
		/**
		 * @param partition partition of the states
		 * @param a target set
		 * @param hier hierarchical predecessor
		 */
		public ReturnPredecessorLinSetGivenHierFinder(Partition partition,
											TargetSet a, STATE hier) {
			super(partition, a);
			this.mhier = hier;
		}
		
		/**
		 * adds linear return predecessor states
		 * 
		 * @param state state
		 * @param letter return letter
		 * @param x predecessor set
		 */
		@Override
		protected void addPred(STATE state, LETTER letter, PredecessorSet x) {
			mpartition.addPredReturnLin(state, letter, mhier, x);
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
		public ReturnSuccessorSetFinder(Partition partition, TargetSet a) {
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
		protected void addPred(STATE state, LETTER letter, PredecessorSet x) {
			mpartition.addSuccReturnHier(state, letter, x);
		}
	}
	
	/**
	 * equivalence class for the merge method
	 * contains the collection of states
	 * = equivalence class and information if the equivalence class is
	 * also contained in work list
	 */
	public class EquivalenceClass implements IBlock<STATE> {
		// collection with equivalence class's elements
		private Set<STATE> mcollection;
		// equivalence class is contained in work list
		private boolean minW;
		// equivalence class is contained in target set
		private boolean minA;
		// representative. Note that this is a state of the resulting NWA.
		private STATE mrepresentative;
		// equivalence class contains final/initial states
		private boolean misFinal, misInitial;
		// intersection collection during the splitting
		private HashSet<STATE> mintersection;
		// individual ID
		private final int mid;
		// incoming returns
		private boolean mincomingReturns;
		// split occurred
		private boolean mwasSplit;
		
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
				this.mcollection = (Set<STATE>) collection;
			}
			else {
				this.mcollection = new HashSet<STATE>(computeHashSetCapacity(
														collection.size()));
				for (final STATE state : collection) {
					this.mcollection.add(state);
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
			this.misFinal = isFinal;
			this.minW = inW;
			this.minA = inA;
			// true because then the real result is computed later
			this.mwasSplit = true;
			// initially intersection is null
			this.mintersection = null;
			this.mid = mEquivalenceClassId++;
		}
		
		/**
		 * @return true iff two equivalence classes are the same objects
		 */
		@SuppressWarnings("unchecked")
		@Override
		public boolean equals(Object o) {
			if (o instanceof MinimizeSevpa.EquivalenceClass) {
				return this.mid == ((EquivalenceClass)o).mid;
			}
			return false;
		}
		
		/**
		 * @return hash code
		 */
		@Override
		public int hashCode() {
			return this.mid;
		}
		
		/**
		 * @return collection of states
		 */
		Collection<STATE> getCollection() {
			return mcollection;
		}
		
		/**
		 * @return true iff equivalence class is in work list
		 */
		boolean isInWorkList() {
			return minW;
		}
		
		/**
		 * should only be called by the partition object
		 * 
		 * @param inW true iff equivalence class is now in the work list
		 */
		private void setInWorkList(boolean inW) {
			this.minW = inW;
		}
		
		/**
		 * @return true iff equivalence class is in target set
		 */
		boolean isInTargetSet() {
			return minA;
		}
		
		/**
		 * @param inA true iff equivalence class is in target set
		 */
		void setInTargetSet(boolean inA) {
			this.minA = inA;
		}
		
		@Override
		public boolean isFinal() {
			return misFinal;
		}
		
		/**
		 * setter
		 */
		void setWasSplit() {
			this.mwasSplit = true;
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
			if (mintersection == null) {
				mintersection = new HashSet<STATE>();
				intersected.add(this);
			}
			return mintersection;
		}
		
		/**
		 * resets the intersection equivalence class to null
		 */
		void resetIntersection() {
			// if collection is empty, intersection can be restored
			if (mcollection.isEmpty()) {
				mcollection = mintersection;
			}
			mintersection = null;
		}
		
		/**
		 * @return representative state (initial if possible)
		 */
		STATE getRepresentative() {
			return mrepresentative;
		}
		
		/**
		 * @return size of the collection
		 */
		int size() {
			return mcollection.size();
		}
		
		/**
		 * @return true iff collection is empty
		 */
		boolean isEmpty() {
			return mcollection.isEmpty();
		}
		
		/**
		 * @param state state to add
		 * @return true iff state was not contained before
		 */
		boolean add(STATE state) {
			return mcollection.add(state);
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
			assert mcollection.contains(state);
			mcollection.remove(state);
			getIntersection(intersected).add(state);
		}
		
		/**
		 * sets the equivalence class as initial
		 */
		void markAsInitial() {
			misInitial = true;
		}
		
		/**
		 * splits an equivalence class into two
		 * 
		 * @param partition partition of the states
		 * @return split equivalence class
		 */
		public EquivalenceClass split(Partition partition) {
			final EquivalenceClass intersection =
					new EquivalenceClass(getIntersection(null), isFinal(),
														isInWorkList());
			partition.addEquivalenceClass(intersection);
			mwasSplit = true;
						
			// refresh state mapping
			for (final STATE state : intersection.getCollection()) {
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
			if (mwasSplit) {
				mwasSplit = false;
				
				mincomingReturns = false;
				for (final STATE state : mcollection) {
					if (partition.hasIncomingReturns(state)) {
						mincomingReturns = true;
						break;
					}
				}
			}
			
			return mincomingReturns;
		}
		
		/**
		 * NOTE: is only correct, since the method is always called with
		 * hasIncomingReturns() alternately and only at certain points
		 * 
		 * @return true iff equivalence class was split during second phase
		 */
		boolean wasSplitDuringSecondPhase() {
			if (mwasSplit) {
				mwasSplit = false;
				return true;
			}
			return false;
		}
		
		/**
		 * @return string representation
		 */
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			
			builder.append("[");
			for (final STATE state : mcollection) {
				builder.append(state.toString());
				builder.append(", ");
			}
			if (builder.length() > 2) {
				builder.delete(builder.length() - 2, builder.length());
			}
			builder.append("]");
			if (misFinal) {
				builder.append("f");
			}
			if (minW) {
				builder.append("w");
			}
			
			return builder.toString();
		}
		
		@Override
		public boolean isInitial() {
			return misInitial;
		}
		
		@Override
		public STATE minimize(final StateFactory<STATE> stateFactory) {
			return stateFactory.minimize(mcollection);
		}
		
		@Override
		public Iterator<STATE> statesIterator() {
			return mcollection.iterator();
		}
		
		@Override
		public boolean isRepresentativeIndependentInternalsCalls() {
			return true;
		}
	}
	
	/**
	 * collection of equivalence classes and a mapping
	 * 'state -> equivalence class' for fast access
	 */
	public class Partition implements IPartition<STATE> {
		// original nested word automaton
		private final INestedWordAutomaton<LETTER, STATE> mparentOperand;
		// equivalence classes
		private final LinkedList<EquivalenceClass> mequivalenceClasses;
		// work list (W) with equivalence classes still to refine
		private final WorkList mworkList;
		// mapping 'state -> equivalence class'
		private final HashMap<STATE,EquivalenceClass> mmapState2EquivalenceClass;
		
		/**
		 * @param operand original nested word automaton
		 * @param states number of states (avoids rehashing)
		 */
		Partition(INestedWordAutomaton<LETTER, STATE> operand, int states) {
			this.mparentOperand = operand;
			this.mequivalenceClasses = new LinkedList<EquivalenceClass>();
			this.mworkList = new WorkList(mparentOperand.size() / 2);
			this.mmapState2EquivalenceClass =
				new HashMap<STATE, EquivalenceClass>(
									computeHashSetCapacity(states));
		}
		
		/**
		 * removes empty equivalence classes
		 */
		public boolean removeEmptyEquivalenceClasses() {
			final ListIterator<EquivalenceClass> it =
					mequivalenceClasses.listIterator();
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
		
		public void splitOccurred(EquivalenceClass ec, EquivalenceClass cap) {
			ec.setWasSplit();
			cap.setWasSplit();
		}
		
		/**
		 * marks all respective equivalence classes as initial
		 */
		public void markInitials() {
			/*
			 * if an equivalence class contains an initial state,
			 * the whole equivalence class should be initial
			 */
			for (final STATE state : mparentOperand.getInitialStates()) {
				final EquivalenceClass ec = mmapState2EquivalenceClass.get(state);
				// null check needed in case state was removed beforehand
				if (ec != null) {
					assert (! ec.isEmpty());
					ec.markAsInitial();
				}
			}
		}
		
		/**
		 * @return all equivalence classes
		 */
		LinkedList<EquivalenceClass> getEquivalenceClasses() {
			return mequivalenceClasses;
		}
		
		@Override
		public IBlock<STATE> getBlock(final STATE state) {
			return mmapState2EquivalenceClass.get(state);
		}
		
		@Override
		public int size() {
			return mequivalenceClasses.size();
		}
		
		/**
		 * @param equivalenceClass new equivalence class
		 */
		void addEquivalenceClass(EquivalenceClass equivalenceClass) {
			mequivalenceClasses.add(equivalenceClass);
			if (equivalenceClass.isInWorkList()) {
				mworkList.add(equivalenceClass);
			}
			for (final STATE state : equivalenceClass.getCollection()) {
				mmapState2EquivalenceClass.put(state, equivalenceClass);
			}
		}
		
		/**
		 * @param state state in equivalence class
		 * @return equivalence class containing the state
		 */
		EquivalenceClass getEquivalenceClass(STATE state) {
			return mmapState2EquivalenceClass.get(state);
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
			mmapState2EquivalenceClass.put(state, equivalenceClass);
		}
		
		/**
		 * @return true iff work list is empty
		 */
		boolean workListIsEmpty() {
			return mworkList.isEmpty();
		}
		
		/**
		 * @param equivalenceClass equivalence class for the work list
		 */
		void addToWorkList(EquivalenceClass equivalenceClass) {
			mworkList.add(equivalenceClass);
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
			final Collection<STATE> collection = equivalenceClass.getCollection();
			final Iterator<STATE> iterator = collection.iterator();
			while (iterator.hasNext()) {
				final STATE state = iterator.next();
				
				// successors via linear edge
				for (final LETTER letter : mparentOperand.lettersReturn(state)) {
					final Iterable<STATE> hierPreds = hierPred(state, letter);
					for (final STATE hier : hierPreds) {
						final Iterable<OutgoingReturnTransition<LETTER, STATE>> succStates =
								succReturn(state, hier, letter);
						for (final OutgoingReturnTransition<LETTER, STATE> trans :
								succStates) {
							final STATE succ = trans.getSucc();
							final EquivalenceClass ec = getEquivalenceClass(succ);
							if (! ec.isInWorkList()) {
								addToWorkList(ec);
							}
						}
					}
				}
				
				// successors via hierarchical edge
				for (final LETTER letter :
					mparentOperand.lettersReturnSummary(state)) {
					final Iterable<SummaryReturnTransition<LETTER, STATE>>
					succs =
					mparentOperand.returnSummarySuccessor(
							letter, state);
					for (final SummaryReturnTransition<LETTER, STATE> t :
						succs) {
						final EquivalenceClass ec = getEquivalenceClass(
								t.getSucc());
						if (! ec.isInWorkList()) {
							addToWorkList(ec);
						}
					}
				}
			}
		}
		
		/**
		 * @return next equivalence class in the work list
		 */
		EquivalenceClass popFromWorkList() {
			final EquivalenceClass ec = mworkList.pop();
			ec.setInWorkList(false);
			return ec;
		}
		
		/**
		 * @param state state
		 * @return true iff state has an incoming return transition
		 */
		public boolean hasIncomingReturns(STATE state) {
			return mparentOperand.lettersReturnIncoming(state).size() > 0;
		}
		
		/**
		 * finds successor states
		 * (for avoiding states that have already been removed)
		 * 
		 * @param states set of target states
		 */
		private Collection<STATE> neighbors(Iterable<STATE> states) {
			final LinkedList<STATE> result = new LinkedList<STATE>();
			for (final STATE s : states) {
				if (mmapState2EquivalenceClass.get(s) != null) {
					result.add(s);
				}
			}
			return result;
		}
		Iterable<OutgoingInternalTransition<LETTER, STATE>> succInternal(
				STATE state, LETTER letter) {
			return mparentOperand.internalSuccessors(state, letter);
		}
		Iterable<OutgoingCallTransition<LETTER, STATE>> succCall(
				STATE state, LETTER letter) {
			return mparentOperand.callSuccessors(state, letter);
		}
		Iterable<OutgoingReturnTransition<LETTER, STATE>> succReturn(
				STATE state, STATE hier, LETTER letter) {
			return mparentOperand.returnSucccessors(state, hier, letter);
		}
		Iterable<STATE> hierPred(STATE state, LETTER letter) {
			return mparentOperand.hierPred(state, letter);
		}
		Iterable<IncomingReturnTransition<LETTER, STATE>> linPredIncoming(
				STATE state, STATE hier, LETTER letter) {
			return mparentOperand.returnPredecessors(hier, letter, state);
		}
		Iterable<IncomingReturnTransition<LETTER, STATE>> hierPredIncoming(
				STATE state, LETTER letter) {
			return mparentOperand.returnPredecessors(letter, state);
		}
		
		/**
		 * finds predecessor states and directly adds elements to the set
		 * 
		 * @param states target states of edges
		 * @param x predecessor set
		 */
		private void addNeighbors(Iterable<STATE> states,
				PredecessorSet x) {
			for (final STATE s : states) {
				if (mmapState2EquivalenceClass.get(s) != null) {
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
			for (final STATE s : states) {
				x.add(s);
			}
		}
		
		private void addNeighborsEfficientLin(
				Iterable<IncomingReturnTransition<LETTER, STATE>> transitions,
					PredecessorSet x) {
			for (final IncomingReturnTransition<LETTER, STATE> inTrans : transitions) {
				x.add(inTrans.getLinPred());
			}
		}
		
		private void addNeighborsEfficientHier(
				Iterable<IncomingReturnTransition<LETTER, STATE>> transitions,
					PredecessorSet x) {
			for (final IncomingReturnTransition<LETTER, STATE> inTrans : transitions) {
				x.add(inTrans.getHierPred());
			}
		}


		
		void addPredInternal(STATE state, LETTER letter, PredecessorSet x) {
				addNeighborsEfficient(new InternalTransitionIterator(
						mparentOperand.internalPredecessors(letter, state)), x);
		}
		void addPredCall(STATE state, LETTER letter, PredecessorSet x) {
				addNeighborsEfficient(new CallTransitionIterator(
						mparentOperand.callPredecessors(letter, state)), x);
		}
		void addPredReturnLin(STATE state, LETTER letter,
				STATE hier, PredecessorSet x) {
				addNeighborsEfficientLin(mparentOperand.returnPredecessors(
						hier, letter, state), x);
		}
		void addPredReturnHier(STATE state, LETTER letter, PredecessorSet x) {
				addNeighborsEfficientHier(
						mparentOperand.returnPredecessors(letter, state), x);
		}
		void addSuccReturnHier(STATE state, LETTER letter, PredecessorSet x) {
			final HashSet<STATE> hierSet = new HashSet<STATE>();
			for (final STATE hier : mparentOperand.hierPred(state, letter)) {
				hierSet.add(hier);
			}
			addNeighborsEfficient(hierSet, x);
		}
		
		/**
		 * Iterable for internal transitions.
		 */
		class InternalTransitionIterator implements Iterable<STATE> {
			final Iterable<IncomingInternalTransition<LETTER, STATE>> mIterable;
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
			final Iterable<IncomingCallTransition<LETTER, STATE>> mIterable;
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
		
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			
			builder.append("{ ");
			for (final EquivalenceClass ec : mequivalenceClasses) {
				builder.append(ec.toString());
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
				Iterator<EquivalenceClass> mIt = mequivalenceClasses.iterator();
				
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
	 * target set 'A' of which the predecessor set is computed
	 * in order to get valid results, the original equivalence class A has to
	 * be remembered somehow, since it can be destroyed during the splitting
	 * 
	 * NOTE: iterator must be used in 'hasNext()-loop'
	 * and with no change to the equivalence classes during iteration
	 */
	class TargetSet {
		LinkedList<EquivalenceClass> mequivalenceClasses;
		
		/**
		 * @param firstEquivalenceClass first equivalence class
		 * 			(must not be null)
		 */
		public TargetSet(EquivalenceClass firstEquivalenceClass) {
			assert firstEquivalenceClass != null;
			this.mequivalenceClasses = new LinkedList<EquivalenceClass>();
			this.mequivalenceClasses.add(firstEquivalenceClass);
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
				private final ListIterator<EquivalenceClass> listIterator =
										mequivalenceClasses.listIterator();
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
					final STATE result = next;
					
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
			mequivalenceClasses.add(equivalenceClass);
			equivalenceClass.setInTargetSet(true);
		}
		
		/**
		 * delete object and reset flag in equivalence class objects
		 */
		void delete() {
			for (final EquivalenceClass ec : mequivalenceClasses) {
				ec.setInTargetSet(false);
			}
			
			mequivalenceClasses = null;
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
			final StringBuilder builder = new StringBuilder();
			builder.append("{");
			
			for (final EquivalenceClass ec : mequivalenceClasses) {
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
		PriorityQueue<EquivalenceClass> mqueue;
		
		/**
		 * constructor
		 */
		public WorkList(int size) {
			if (size == 0) {
				// special case where automaton has no reachable states
				size = 1;
			}
			this.mqueue = new PriorityQueue<EquivalenceClass>(size,
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
			assert (! mqueue.contains(equivalenceClass));
			mqueue.add(equivalenceClass);
		}
		
		/**
		 * @return next equivalence class according to the ordering
		 */
		public EquivalenceClass pop() {
			return mqueue.poll();
		}
		
		/**
		 * @return true iff work list is empty
		 */
		public boolean isEmpty() {
			return mqueue.isEmpty();
		}
		
		/**
		 * @return string representation
		 */
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			
			builder.append("{");
			builder.append(mqueue.toString());
			builder.append("}");
			
			return builder.toString();
		}
	}
	
	/**
	 * representation of the collection of predecessor states
	 */
	class PredecessorSet {
		HashSet<STATE> mcollection;
		
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
			this.mcollection = hashSet;
		}
		
		/**
		 * @return iterator for the collection
		 */
		Iterator<STATE> iterator() {
			return mcollection.iterator();
		}
		
		/**
		 * @param state state to add
		 */
		void add(STATE state) {
			mcollection.add(state);
		}
		
		/**
		 * melds two predecessor sets
		 * 
		 * @param other other predecessor set
		 */
		void meld(PredecessorSet other) {
			mcollection.addAll(other.mcollection);
		}
		
		/**
		 * @return size of the collection
		 */
		int size() {
			return mcollection.size();
		}
		
		/**
		 * @return true iff collection is empty
		 */
		boolean isEmpty() {
			return mcollection.isEmpty();
		}
		
		/**
		 * deletes all stored elements
		 */
		void delete() {
			mcollection = null;
		}
		
		/**
		 * @return string representation
		 */
		@Override
		public String toString() {
			return mcollection.toString();
		}
	}
	
	/**
	 * intermediate data storage for states reachable in the automaton
	 * already distinguishes between final and non-final states
	 * either has a copy of the states or only knows the removed states
	 */
	class StatesContainer {
		// original nested word automaton
		private final INestedWordAutomaton<LETTER, STATE> mparentOperand;
		// states
		private HashSet<STATE> mfinals;
		private HashSet<STATE> mnonfinals;
		// true iff a real copy is made
		private final StatesContainerMode mmode;
		
		/**
		 * constructor
		 */
		StatesContainer(INestedWordAutomaton<LETTER, STATE> operand) {
			this.mparentOperand = operand;
			this.mmode = StatesContainerMode.none;

			
			switch (this.mmode) {
				// if unreachable states shall be removed, make a copy
				case makeCopy :
					this.mfinals =
					new HashSet<STATE>(computeHashSetCapacity(
							mparentOperand.getFinalStates().size()));
					this.mnonfinals =
						new HashSet<STATE>(computeHashSetCapacity(
							mparentOperand.size() -
							mparentOperand.getFinalStates().size()));
					break;
				/*
				 * if only dead ends shall be removed,
				 * only remember removed states
				 */
				case saveRemoved :
					this.mfinals = new HashSet<STATE>();
					this.mnonfinals = new HashSet<STATE>();
					break;
				// else the sets are not needed
				case none :
					this.mfinals = null;
					this.mnonfinals = null;
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
			switch (mmode) {
				case makeCopy :
					return mfinals.size() > 0;
				case saveRemoved :
					return (
						(mparentOperand.getFinalStates().size() -
							mfinals.size()) > 0);
				case none :
					return (mparentOperand.getFinalStates().size() > 0);
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
			assert mmode == StatesContainerMode.makeCopy;
			return mnonfinals;
		}
		
		/**
		 * @return iterator of non-final states
		 */
		Iterator<STATE> getNonfinalsIterator() {
			switch (mmode) {
				case makeCopy :
					return mnonfinals.iterator();
				case saveRemoved :
					return new Iterator<STATE>() {
						private final Iterator<STATE> iterator =
								mparentOperand.getStates().iterator();
						private STATE next = computeNext();
						
						@Override
						public boolean hasNext() {
							return next != null;
						}
						
						@Override
						public STATE next() {
							assert next != null;
							
							// next element already computed before
							final STATE result = next;
							
							// compute next element
							next = computeNext();
							
							return result;
						}
						
						private STATE computeNext() {
							STATE nextFound;
							while (iterator.hasNext()) {
								nextFound = iterator.next();
								if (! mparentOperand.isFinal(nextFound) &&
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
			assert mmode == StatesContainerMode.makeCopy;
			return mfinals;
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
			switch (mmode) {
			case makeCopy :
				return mfinals.iterator();
			case saveRemoved :
				return new Iterator<STATE>() {
					private final Iterator<STATE> iterator =
							mparentOperand.getFinalStates().iterator();
					private STATE next = computeNext();
					
					@Override
					public boolean hasNext() {
						return next != null;
					}
					
					@Override
					public STATE next() {
						assert next != null;
						
						// next element already computed before
						final STATE result = next;
						
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
				return mparentOperand.getFinalStates().iterator();
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
			assert (mmode == StatesContainerMode.saveRemoved);
			
			if (finals) {
				return mfinals.size();
			}
			else {
				return mnonfinals.size();
			}
		}
		
		/**
		 * creates a collection of the non-final states for the merge
		 * in case of an automaton with no word accepted
		 * 
		 * @return collection of non-final states
		 */
		Collection<STATE> getTrivialAutomatonStates() {
			switch (mmode) {
				case makeCopy :
					return mnonfinals;
				case saveRemoved :
					final LinkedList<STATE> result = new LinkedList<STATE>();
					final Iterator<STATE> iterator = getNonfinalsIterator();
					while (iterator.hasNext()) {
						result.add(iterator.next());
					}
					return result;
				case none :
					return mparentOperand.getStates();
				default :
					assert false;
					return null;
			}
		}
		
		/**
		 * @return number of states
		 */
		int size() {
			switch (mmode) {
				case makeCopy :
					return mfinals.size() + mnonfinals.size();
				case saveRemoved :
					return mparentOperand.size() - mfinals.size() -
							mnonfinals.size();
				case none :
					return mparentOperand.size();
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
			switch (mmode) {
				case makeCopy :
					return (mnonfinals.contains(state) ||
							mfinals.contains(state));
				case saveRemoved :
					return (! (mnonfinals.contains(state) ||
							mfinals.contains(state)));
				case none :
					return mparentOperand.getStates().contains(state);
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
			switch (mmode) {
				case makeCopy :
					if (mparentOperand.isFinal(state)) {
						mfinals.add(state);
					}
					else {
						mnonfinals.add(state);
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
			switch (mmode) {
				case makeCopy :
					for (final STATE state : states) {
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
			switch (mmode) {
				case makeCopy :
					if (! mnonfinals.remove(state)) {
						mfinals.remove(state);
					}
					return;
				case saveRemoved :
					if (mparentOperand.isFinal(state)) {
						mfinals.add(state);
					}
					else {
						mnonfinals.add(state);
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
			return mmode == StatesContainerMode.makeCopy;
		}
		
		/**
		 * deletes all stored elements
		 */
		void delete() {
			switch (mmode) {
				case makeCopy :
				case saveRemoved :
					mfinals = null;
					mnonfinals = null;
					return;
				case none :
					return;
				default :
					assert false;
					return;
			}
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
	 * @return map from input automaton states to output automaton states
	 */
	public Map<STATE, STATE> getOldState2newState() {
		return mOldState2newState;
	}
	
	@Override
	public NestedWordAutomaton<LETTER,STATE> getResult() {
		return mNwa;
	}
}
