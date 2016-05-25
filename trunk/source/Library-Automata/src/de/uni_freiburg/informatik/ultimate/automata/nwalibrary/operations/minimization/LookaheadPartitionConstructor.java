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
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
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
 */
public class LookaheadPartitionConstructor<LETTER, STATE>  {
	
	private final AutomataLibraryServices mServices;
	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	private final Collection<Set<STATE>> mResult;

	public LookaheadPartitionConstructor(AutomataLibraryServices services,
			INestedWordAutomaton<LETTER, STATE> operand) {
		mServices = services;
		mOperand = operand;

		final HashRelation<OutgoingInCaSymbols<STATE, LETTER>, STATE> symbols2states = new HashRelation<>();
		for (final STATE inputState : mOperand.getStates()) {
			symbols2states.addPair(computeOutgoingSymbols(inputState), inputState);
		}
		mResult = new LinkedHashSet<>();
		for(final OutgoingInCaSymbols<STATE, LETTER> outgoingSymbols : symbols2states.getDomain()) {
			mResult.add(Collections.unmodifiableSet(symbols2states.getImage(outgoingSymbols)));
		}
	}
	
	private OutgoingInCaSymbols<STATE,LETTER> computeOutgoingSymbols(STATE state) {
		final Set<LETTER> lettersInternal = mOperand.lettersInternal(state);
		final Set<LETTER> lettersCall = mOperand.lettersCall(state);
		return new OutgoingInCaSymbols<>(lettersInternal, lettersCall);
		
	}
	
	private static class OutgoingInCaSymbols<STATE,LETTER> {
		private final Set<LETTER> mInternal;
		private final Set<LETTER> mCall;
		public OutgoingInCaSymbols(Set<LETTER> internal, Set<LETTER> call) {
			super();
			mInternal = internal;
			mCall = call;
		}
		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((mCall == null) ? 0 : mCall.hashCode());
			result = prime * result + ((mInternal == null) ? 0 : mInternal.hashCode());
			return result;
		}
		@Override
		public boolean equals(Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final OutgoingInCaSymbols other = (OutgoingInCaSymbols) obj;
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
			return "OutgoingInCaSymbols [mInternal=" + mInternal + ", mCall=" + mCall + "]";
		}
		
		

	}
	
	public Collection<Set<STATE>> getResult() {
		return mResult;
	}
	
	

}
