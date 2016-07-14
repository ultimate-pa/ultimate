/*
 * Copyright (C) 2016 Matthias Heizmann <heizmann@informatik.uni-freiburg.de>
 * Copyright (C) 2016 University of Freiburg
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
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Detect non-mergeable states quickly.
 * Construct a partition of an automaton's states such that all elements of a
 * equivalence class are potential candidates for merging states without
 * changing the language. This means that each pair whose two elements are in
 * different equivalence classes cannot be used to merge states without
 * changing the language.
 * WARNING: The result is only correct, if the input automaton did not had any
 * dead-end states.
 * We detect non-mergeable states as follows.
 * A pair of states is non-mergeable if both do not have the same outgoing
 * internal symbols.
 * A pair of states is non-mergeable if both do not have the same outgoing
 * call symbols.
 *
 * TODO: Extend this to returns by providing a partition of DoubleDeckers.
 * @author Matthias Heizmann <heizmann@informatik.uni-freiburg.de>
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 */
public class LookaheadPartitionConstructor<LETTER, STATE>  {

	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	private final Set<Set<STATE>> mResult;
	
	/**
	 * @param services Ultimate services
	 * @param operand input automaton
	 */
	public LookaheadPartitionConstructor(AutomataLibraryServices services,
			INestedWordAutomaton<LETTER, STATE> operand) {
		this(services, operand, false);
	}
	
	/**
	 * @param services Ultimate services
	 * @param operand input automaton
	 * @param separateAcceptingStates true iff only accepting or non-accepting
	 *         states can be in a set
	 */
	public LookaheadPartitionConstructor(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final boolean separateAcceptingStates) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mOperand = operand;
		mResult = createPartition(separateAcceptingStates);
	}
	
	private Set<Set<STATE>>
			createPartition(final boolean separateAcceptingStates) {
		// result partition (changed several times)
		Set<Set<STATE>> partition;
		
		// split states which do not have the same outgoing symbols
		partition = splitDifferentSymbols();
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Splitting by different symbols, result:");
			mLogger.debug(partition);
		}
		
		// split states which are not both final or both non-final
		if (separateAcceptingStates) {
			partition = splitAcceptingStates(partition);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("Splitting by accepting states, result:");
				mLogger.debug(partition);
			}
		}
		
		// split states with (unique) split successors wrt. a symbol
		partition = splitSuccessorsDeterministic(partition);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Splitting by different deterministic successors, result:");
			mLogger.debug(partition);
		}
		
		return partition;
	}
	
	private Set<Set<STATE>> splitDifferentSymbols() {
		final HashRelation<OutgoingInCaSymbols<LETTER>, STATE> symbols2states =
				new HashRelation<>();
		for (final STATE inputState : mOperand.getStates()) {
			symbols2states.addPair(computeOutgoingSymbols(inputState), inputState);
		}
		
		final Set<Set<STATE>> partition = new LinkedHashSet<>();
		for(final OutgoingInCaSymbols<LETTER> outgoingSymbols : symbols2states.getDomain()) {
			partition.add(symbols2states.getImage(outgoingSymbols));
		}
		
		return partition;
	}
	
	private OutgoingInCaSymbols<LETTER> computeOutgoingSymbols(final STATE state) {
		final Set<LETTER> lettersInternal = mOperand.lettersInternal(state);
		final Set<LETTER> lettersCall = mOperand.lettersCall(state);
		return new OutgoingInCaSymbols<>(lettersInternal, lettersCall);
	}
	
	private Set<Set<STATE>> splitAcceptingStates(final Set<Set<STATE>> oldPartition) {
		final Set<Set<STATE>> newPartition = new LinkedHashSet<>(2 * oldPartition.size());
		for (final Set<STATE> block : oldPartition) {
			// find final and non-final states
			final Set<STATE> finals = new LinkedHashSet<STATE>(block.size());
			final Set<STATE> nonfinals = new LinkedHashSet<STATE>(block.size());
			for (final STATE state : block) {
				if (mOperand.isFinal(state)) {
					finals.add(state);
				} else {
					nonfinals.add(state);
				}
			}
			
			// add new blocks if non-empty
			if (finals.isEmpty()) {
				assert (! nonfinals.isEmpty()) :
					"The input sets should not be empty.";
				newPartition.add(nonfinals);
			} else {
				newPartition.add(finals);
				if (! nonfinals.isEmpty()) {
					newPartition.add(nonfinals);
				}
			}
		}
		
		return newPartition;
	}
	
	/**
	 * NOTE: The method assumes that all states in the same block have the same
	 * outgoing internal and call symbols.
	 * 
	 * @param inputPartition old partition
	 * @return new partition
	 */
	private Set<Set<STATE>>
			splitSuccessorsDeterministic(final Set<Set<STATE>> inputPartition) {
		Set<Set<STATE>> partition = inputPartition;
		final Map<STATE, Set<STATE>> state2block = new HashMap<>(mOperand.size());
		for (final Set<STATE> block : partition) {
			for (final STATE state : block) {
				state2block.put(state, block);
			}
		}
		
		boolean hasChanged = true;
		while (hasChanged) {
			hasChanged = false;
			
			final Set<Set<STATE>> newPartition =
					new LinkedHashSet<>(partition.size());
			for (final Set<STATE> block : partition) {
				newPartition.add(block);
			}
			
			for (final Set<STATE> block : partition) {
				assert (! block.isEmpty()) : "Blocks should be non-empty.";
				final STATE firstState = block.iterator().next();
				for (final LETTER letter : mOperand.lettersInternal(firstState)) {
					hasChanged |= splitLetterSuccessors(state2block, block,
							letter, newPartition, true);
				}
				for (final LETTER letter : mOperand.lettersCall(firstState)) {
					hasChanged |= splitLetterSuccessors(state2block, block,
							letter, newPartition, false);
				}
			}
			
			partition = newPartition;
		}
		
		return partition;
	}
	
	private boolean splitLetterSuccessors(
			final Map<STATE, Set<STATE>> state2block, final Set<STATE> block,
			final LETTER letter, final Set<Set<STATE>> partition,
			final boolean isInternal) {
		final Map<Set<STATE>, Set<STATE>> targetBlock2state = new HashMap<>();
		for (final STATE state : block) {
			final STATE targetState = getSuccessor(letter, state, isInternal);
			if (targetState == null) {
				// state is nondeterministic wrt. letter
				return false;
			}
			final Set<STATE> targetBlock = state2block.get(targetState);
			Set<STATE> states = targetBlock2state.get(targetBlock);
			if (states == null) {
				states = new LinkedHashSet<STATE>();
				targetBlock2state.put(targetBlock, states);
			}
			states.add(state);
		}
		
		// modify the partition since all states are deterministic wrt. letter
		boolean result = false;
		for (final Set<STATE> newBlock : targetBlock2state.values()) {
			final boolean isNewBlock = partition.add(newBlock);
			if (isNewBlock) {
				result = true;
				// update map
				for (final STATE state : newBlock) {
					final Set<STATE> oldBlock = state2block.put(state, newBlock);
					partition.remove(oldBlock);
				}
			}
		}
		return result;
	}
	
	@SuppressWarnings("unchecked")
	private STATE getSuccessor(final LETTER letter, final STATE state,
			final boolean isInternal) {
		final Iterator<?> it = isInternal
				? mOperand.internalSuccessors(state, letter).iterator()
				: mOperand.callSuccessors(state, letter).iterator();
		assert it.hasNext() :
			"There should be at least one outgoing transition.";
		@SuppressWarnings("squid:S1941")
		final Object trans = it.next();
		if (it.hasNext()) {
			// state is nondeterministic wrt. letter
			return null;
		}
		final STATE targetState = isInternal
				? ((OutgoingInternalTransition<LETTER, STATE>) trans).getSucc()
				: ((OutgoingCallTransition<LETTER, STATE>) trans).getSucc();
		return targetState;
	}
	
	private static class OutgoingInCaSymbols<LETTER> {
		private static final int PRIME = 31;
		private final Set<LETTER> mInternal;
		private final Set<LETTER> mCall;
		public OutgoingInCaSymbols(
				final Set<LETTER> internal,
				final Set<LETTER> call) {
			mInternal = internal;
			mCall = call;
		}
		@Override
		public int hashCode() {
			int result = 1;
			result = PRIME * result + ((mCall == null) ? 0 : mCall.hashCode());
			result = PRIME * result + ((mInternal == null) ? 0 : mInternal.hashCode());
			return result;
		}
		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final OutgoingInCaSymbols<LETTER> other =
					(OutgoingInCaSymbols<LETTER>) obj;
			if (mCall == null) {
				if (other.mCall != null) {
					return false;
				}
			} else if (!mCall.equals(other.mCall)) {
				return false;
			}
			if (mInternal == null) {
				if (other.mInternal != null) {
					return false;
				}
			} else if (!mInternal.equals(other.mInternal)) {
				return false;
			}
			return true;
		}
		@Override
		public String toString() {
			return "OutgoingInCaSymbols [mInternal=" + mInternal + ", mCall=" +
					mCall + "]";
		}
	}
	
	public Collection<Set<STATE>> getResult() {
		return mResult;
	}
}
