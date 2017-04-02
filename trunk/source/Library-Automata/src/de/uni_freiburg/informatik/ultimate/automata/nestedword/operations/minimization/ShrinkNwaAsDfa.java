/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation, either version 3 of the License,
 * or (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be
 * useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser
 * General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see
 * <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automata Library, or any covered work, by linking or combining it
 * with Eclipse RCP (or a modified version of Eclipse RCP), containing parts
 * covered by the terms of the Eclipse Public License, the licensors of the
 * ULTIMATE Automata Library grant you additional permission to convey the
 * resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map.Entry;
import java.util.PriorityQueue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.util.IAutomatonStatePartition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.util.IBlock;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.util.PartitionBackedSetOfPairs;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * This class minimizes nested word automata.
 * <p>
 * It is based on Hopcroft's minimization for deterministic finite automata. All nested edges (calls and returns) are
 * seen as fresh symbols consisting of the tuple <code>(symbol, hierarchical state)</code>
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class ShrinkNwaAsDfa<LETTER, STATE> extends AbstractMinimizeNwa<LETTER, STATE> {
	// old automaton
	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	private IDoubleDeckerAutomaton<LETTER, STATE> mDoubleDecker;
	// partition object
	private Partition mPartition;
	// IDs for equivalence classes
	private int mIds;
	// work lists
	private WorkList mWorkList;

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
	public ShrinkNwaAsDfa(final AutomataLibraryServices services, final IMinimizationStateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, null, false, false);
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
	 *            used for Hoare annotation
	 * @param addMapping
	 *            true iff mapping old to new state is needed
	 * @param considerNeutralStates
	 *            true iff neutral states should be considered
	 * @throws AutomataOperationCanceledException
	 *             if cancel signal is received
	 */
	public ShrinkNwaAsDfa(final AutomataLibraryServices services, final IMinimizationStateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final PartitionBackedSetOfPairs<STATE> equivalenceClasses, final boolean addMapping,
			final boolean considerNeutralStates) throws AutomataOperationCanceledException {
		super(services, stateFactory);
		mOperand = operand;

		printStartMessage();
		mDoubleDecker = considerNeutralStates ? (IDoubleDeckerAutomaton<LETTER, STATE>) mOperand : null;
		mPartition = new Partition();
		mIds = 0;
		mWorkList = new WorkList();

		// must be the last part of the constructor
		minimize(equivalenceClasses, addMapping);
		printExitMessage();
	}

	@Override
	protected INestedWordAutomaton<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	protected Pair<Boolean, String> checkResultHelper(final IMinimizationCheckResultStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		return checkLanguageEquivalence(stateFactory);
	}

	// --- [start] main methods --- //

	/**
	 * This is the main method that merges states not distinguishable (based on Hopcroft's algorithm).
	 * 
	 * @param isFiniteAutomaton
	 *            true iff automaton is a finite automaton
	 * @param modules
	 *            predefined modules that must be split
	 * @param addMapping
	 *            true iff mapping old to new state is needed
	 * @throws AutomataOperationCanceledException
	 *             if cancel signal is received
	 */
	private void minimize(final PartitionBackedSetOfPairs<STATE> modules, final boolean addMapping)
			throws AutomataOperationCanceledException {
		// initialize the partition object
		initialize(modules);

		final InternalTransitionIterator internalIterator = new InternalTransitionIterator();
		final CallTransitionIterator callIterator = new CallTransitionIterator();
		final ReturnTransitionIterator returnIterator = new ReturnTransitionIterator();

		// internals and calls
		while (mWorkList.hasNext()) {
			// cancel if signal is received
			if (isCancellationRequested()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}

			final EquivalenceClass a = mWorkList.next();

			// internal split
			if (a.mIncomingInt == IncomingStatus.IN_WL) {
				a.mIncomingInt = IncomingStatus.UNKNOWN;
				splitPredecessors(a, internalIterator, TransitionType.INTERNAL);
			}

			// call split
			if (a.mIncomingCall == IncomingStatus.IN_WL) {
				a.mIncomingCall = IncomingStatus.UNKNOWN;
				splitPredecessors(a, callIterator, TransitionType.CALL);
			}

			// return split
			if (a.mIncomingRet == IncomingStatus.IN_WL) {
				a.mIncomingRet = IncomingStatus.UNKNOWN;
				splitPredecessors(a, returnIterator, TransitionType.RETURN);
			}
		}

		mLogger.info("Finished analysis, constructing result of size " + mPartition.mEquivalenceClasses.size());

		// automaton construction
		constructAutomaton(addMapping);
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
				if (mOperand.isFinal(state)) {
					finals.add(state);
				} else {
					nonfinals.add(state);
				}
			}

			if (!finals.isEmpty()) {
				mPartition.addEcInitialization(finals);
			}
			if (!nonfinals.isEmpty()) {
				mPartition.addEcInitialization(nonfinals);
			}
		} else {
			final Collection<Set<STATE>> modules = modulesWrapped.getRelation();
			// predefined modules are already split with respect to final states
			assert assertStatesSeparation(modules) : "The states in the initial modules are not separated with "
					+ "respect to their final status.";
			for (final Set<STATE> module : modules) {
				mPartition.addEcInitialization(module);
			}
		}
	}

	/**
	 * For each state and symbol respectively do the usual Hopcroft backwards split.
	 * <p>
	 * First all predecessor sets (with respect to a single symbol) are found and then for each such set the states are
	 * split from their equivalence classes.
	 * 
	 * @param block
	 *            the splitter equivalence class
	 * @param iterator
	 *            the iterator abstracting from the letter type
	 * @param isInternal
	 *            true iff split is internal
	 */
	private void splitPredecessors(final EquivalenceClass block, final ITransitionIterator<LETTER, STATE> iterator,
			final TransitionType type) {
		assert (type == TransitionType.INTERNAL && (iterator instanceof ShrinkNwaAsDfa.InternalTransitionIterator)
				&& (block.mIncomingInt != IncomingStatus.IN_WL))
				|| (type == TransitionType.CALL && (iterator instanceof ShrinkNwaAsDfa.CallTransitionIterator)
						&& (block.mIncomingCall != IncomingStatus.IN_WL))
				|| (type == TransitionType.RETURN && (iterator instanceof ShrinkNwaAsDfa.ReturnTransitionIterator)
						&& (block.mIncomingRet != IncomingStatus.IN_WL));

		// create a hash map from letter to respective predecessor states
		final HashMap<Pair<LETTER, STATE>, HashSet<STATE>> letter2states = new HashMap<>();
		for (final STATE state : block.mStates) {
			iterator.nextState(state);
			while (iterator.hasNext()) {
				final Pair<LETTER, STATE> letter = iterator.nextAndLetter();
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
			switch (type) {
				case INTERNAL:
					block.mIncomingInt = IncomingStatus.NONE;
					break;
				case CALL:
					block.mIncomingCall = IncomingStatus.NONE;
					break;
				case RETURN:
					block.mIncomingRet = IncomingStatus.NONE;
					break;
				default:
					throw new IllegalArgumentException();
			}
		} else {
			// split each map value (set of predecessor states)
			for (final Entry<Pair<LETTER, STATE>, HashSet<STATE>> entry : letter2states.entrySet()) {
				final Pair<LETTER, STATE> letter;
				if (mDoubleDecker == null) {
					letter = null;
				} else {
					switch (type) {
						case INTERNAL:
						case CALL:
							letter = null;
							break;
						case RETURN:
							letter = entry.getKey();
							break;
						default:
							throw new IllegalArgumentException("Illegal type.");
					}
				}
				final HashSet<STATE> predecessorSet = entry.getValue();
				assert !predecessorSet.isEmpty();
				mPartition.splitEquivalenceClasses(predecessorSet, letter);
			}
		}
	}

	/**
	 * For each remaining equivalence class create a new state. Also remove all other objects references.
	 * 
	 * @param addMapping
	 *            true iff mapping old to new state is needed
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	private void constructAutomaton(final boolean addMapping) throws AutomataOperationCanceledException {
		// marks all respective equivalence classes as initial
		for (final STATE state : mOperand.getInitialStates()) {
			final EquivalenceClass ec = mPartition.mState2EquivalenceClass.get(state);
			ec.markAsInitial();
		}

		constructResultFromPartition(mPartition, addMapping);

		// clean up
		mPartition = null;
		mWorkList = null;
	}

	// --- [end] main methods --- //

	// --- [start] helper methods and classes --- //

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
	 * Type of a transition/symbol.
	 */
	private enum TransitionType {
		INTERNAL,
		CALL,
		RETURN
	}

	/**
	 * This enum is used to tell for an equivalence class whether it contains incoming transitions. Since it is
	 * expensive to compute this each time, only the answer "no" is correct. This status is inherited by the two
	 * resulting equivalence classes after a split. The idea is to not insert such equivalence classes in the work list
	 * for which it is known that there are no incoming transitions. The status is updated as a byproduct after the
	 * search for transitions.
	 */
	private enum IncomingStatus {
		/** Unknown whether there are incoming transitions. */
		UNKNOWN,

		/** Equivalence class is in work list. */
		IN_WL,

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
		 * @return a tuple with letter and hierarchical state of next transition
		 */
		Pair<LETTER, STATE> nextAndLetter();

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
		public Pair<LETTER, STATE> nextAndLetter() {
			mTransition = mIterator.next();
			// NOTE: the state does not matter, but the value must be non-null
			return new Pair<>(mTransition.getLetter(), mTransition.getPred());
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
		public Pair<LETTER, STATE> nextAndLetter() {
			mTransition = mIterator.next();
			return new Pair<>(mTransition.getLetter(), mTransition.getPred());
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
	 * This is the implementation for return transitions.
	 */
	private class ReturnTransitionIterator implements ITransitionIterator<LETTER, STATE> {
		// iterator of the operand
		private Iterator<IncomingReturnTransition<LETTER, STATE>> mIterator;
		// current transition
		private IncomingReturnTransition<LETTER, STATE> mTransition;

		@Override
		public void nextState(final STATE state) {
			mIterator = mOperand.returnPredecessors(state).iterator();
		}

		@Override
		public Pair<LETTER, STATE> nextAndLetter() {
			mTransition = mIterator.next();
			return new Pair<>(mTransition.getLetter(), mTransition.getHierPred());
		}

		@Override
		public STATE getPred() {
			return mTransition.getLinPred();
		}

		@Override
		public boolean hasNext() {
			return mIterator.hasNext();
		}
	}

	// --- [end] helper methods and classes --- //

	// --- [start] important inner classes --- //

	/**
	 * The partition is the main object of the procedure. It contains and handles the equivalence classes and works as
	 * the resulting automaton.
	 */
	private class Partition implements IAutomatonStatePartition<STATE> {
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
		 * This method adds an equivalence class to the partition that resulted from a split.
		 *
		 * @param parent
		 *            the parent equivalence class
		 * @return the equivalence class
		 */
		private EquivalenceClass addEcSplit(final EquivalenceClass parent) {
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

			splitStateFast(state, ec);
		}

		/**
		 * This method splits a state for a given equivalence class without any further considerations.
		 * 
		 * @param state
		 *            state
		 * @param block
		 *            equivalence class
		 */
		private void splitStateFast(final STATE state, final EquivalenceClass block) {
			// move state to intersection set
			block.mIntersection.add(state);

			// remove state from old set
			block.mStates.remove(state);
		}

		/**
		 * This method finally splits the marked equivalence classes into two (for the internal and call split). The
		 * states have already been split in the equivalence class before. Only if there are states remaining the split
		 * is executed, otherwise the old equivalence class is restored.
		 * 
		 * @param states
		 *            set of states to split
		 * @param letter
		 *            pair (letter, state) used for splitting
		 * @return true iff a split occurred
		 */
		public boolean splitEquivalenceClasses(final Iterable<STATE> states, final Pair<LETTER, STATE> letter) {
			boolean splitOccurred = false;
			final LinkedList<EquivalenceClass> splitEcs = new LinkedList<>();

			// process splits
			for (final STATE state : states) {
				splitState(state, splitEcs);
			}

			// check and finalize splits
			for (final EquivalenceClass block : splitEcs) {
				if ((letter != null) && (!block.mStates.isEmpty())) {
					final STATE hier = letter.getSecond();
					// return split, also add neutral states
					final ArrayList<STATE> ecStates = new ArrayList<>(block.mStates);
					for (final STATE lin : ecStates) {
						if (!mDoubleDecker.isDoubleDecker(lin, hier)) {
							splitStateFast(lin, block);
						}
					}
				}

				// split removed every state, restore equivalence class
				if (block.mStates.isEmpty()) {
					block.mStates = block.mIntersection;
				} else {
					// do a split
					splitOccurred = true;
					addEcSplit(block);
				}

				// reset equivalence class
				block.reset();
			}

			return splitOccurred;
		}

		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			builder.append("{");
			String append = "";
			for (final EquivalenceClass block : mEquivalenceClasses) {
				builder.append(append);
				append = ", ";
				builder.append(block);
			}
			builder.append("}");
			return builder.toString();
		}

		@Override
		public IBlock<STATE> getBlock(final STATE state) {
			return mState2EquivalenceClass.get(state);
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
		// initial state information
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
			mId = ++mIds;
			mStates = states;
			reset();
		}

		/**
		 * This constructor is used for the initialization.
		 * 
		 * @param states
		 *            the set of states for the equivalence class
		 */
		public EquivalenceClass(final Set<STATE> states) {
			this(states, false);
			mIncomingInt = IncomingStatus.IN_WL;
			mIncomingCall = IncomingStatus.IN_WL;
			mIncomingRet = IncomingStatus.IN_WL;
			mWorkList.add(this);
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
			boolean add = false;
			switch (parent.mIncomingInt) {
				case UNKNOWN:
				case IN_WL:
					mIncomingInt = IncomingStatus.IN_WL;
					add = true;
					break;
				case NONE:
					mIncomingInt = IncomingStatus.NONE;
					break;
				default:
					throw new IllegalArgumentException();
			}
			switch (parent.mIncomingCall) {
				case UNKNOWN:
				case IN_WL:
					mIncomingCall = IncomingStatus.IN_WL;
					add = true;
					break;
				case NONE:
					mIncomingCall = IncomingStatus.NONE;
					break;
				default:
					throw new IllegalArgumentException();
			}
			switch (parent.mIncomingRet) {
				case UNKNOWN:
				case IN_WL:
					mIncomingRet = IncomingStatus.IN_WL;
					add = true;
					break;
				case NONE:
					mIncomingRet = IncomingStatus.NONE;
					break;
				default:
					throw new IllegalArgumentException();
			}
			if (add) {
				mWorkList.add(this);
			}
		}

		/**
		 * Sets the equivalence class as initial.
		 */
		private void markAsInitial() {
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
		 * This method resets the intersection set.
		 */
		private void reset() {
			mIntersection = new HashSet<>(computeHashCap(mStates.size()));
		}

		@Override
		public String toString() {
			if (mStates == null) {
				return "negative equivalence class";
			}

			final StringBuilder builder = new StringBuilder();
			String append = "";

			builder.append("<[");
			builder.append(mIncomingInt);
			builder.append(",");
			builder.append(mIncomingCall);
			builder.append(",");
			builder.append(mIncomingRet);
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
		 * @param block
		 *            the equivalence class
		 */
		public void add(final EquivalenceClass block) {
			assert !mQueue.contains(block);
			mQueue.add(block);
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
			for (final EquivalenceClass block : mQueue) {
				builder.append(append);
				append = ", ";
				builder.append(block);
			}
		}
	}

	/**
	 * This class implements the work list.
	 */
	private class WorkList extends AWorkList {
		@Override
		public EquivalenceClass next() {
			return mQueue.poll();
		}

		@Override
		public void add(final EquivalenceClass block) {
			assert (block.mIncomingInt == IncomingStatus.IN_WL) || (block.mIncomingCall == IncomingStatus.IN_WL)
					|| (block.mIncomingRet == IncomingStatus.IN_WL);
			super.add(block);
		}
	}

	// --- [end] important inner classes --- //
}
