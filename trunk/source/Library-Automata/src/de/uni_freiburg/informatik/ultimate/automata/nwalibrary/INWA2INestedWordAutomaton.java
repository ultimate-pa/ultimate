/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.Collection;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.SummaryReturnTransition;

public class INWA2INestedWordAutomaton<LETTER, STATE> implements
		INestedWordAutomatonOldApi<LETTER, STATE> {
	
	private final INestedWordAutomaton<LETTER, STATE> mNwa;
	
	public INWA2INestedWordAutomaton(INestedWordAutomaton<LETTER, STATE> inwa) {
		mNwa = inwa;
	}

	@Override
	public Set<LETTER> getInternalAlphabet() {
		return mNwa.getInternalAlphabet();
	}

	@Override
	public Set<LETTER> getCallAlphabet() {
		return mNwa.getCallAlphabet();
	}

	@Override
	public Set<LETTER> getReturnAlphabet() {
		return mNwa.getReturnAlphabet();
	}

	@Override
	public Set<STATE> getStates() {
		return mNwa.getStates();
	}

	@Override
	public STATE getEmptyStackState() {
		return mNwa.getEmptyStackState();
	}

	@Override
	public StateFactory<STATE> getStateFactory() {
		return mNwa.getStateFactory();
	}

	@Override
	public int size() {
		return mNwa.size();
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mNwa.getAlphabet();
	}

	@Override
	public Set<STATE> getInitialStates() {
		return mNwa.getInitialStates();
	}

	@Override
	public boolean isInitial(STATE state) {
		return mNwa.isInitial(state);
	}

	@Override
	public boolean isFinal(STATE state) {
		return mNwa.isFinal(state);
	}

	@Override
	public Set<LETTER> lettersInternal(STATE state) {
		return mNwa.lettersInternal(state);
	}

	@Override
	public Set<LETTER> lettersInternalIncoming(STATE state) {
		return mNwa.lettersInternalIncoming(state);
	}

	@Override
	public Set<LETTER> lettersCall(STATE state) {
		return mNwa.lettersCall(state);
	}

	@Override
	public Set<LETTER> lettersCallIncoming(STATE state) {
		return mNwa.lettersCallIncoming(state);
	}

	@Override
	public Set<LETTER> lettersReturn(STATE state) {
		return mNwa.lettersReturn(state);
	}

	@Override
	public Set<LETTER> lettersReturnIncoming(STATE state) {
		return mNwa.lettersReturnIncoming(state);
	}

	@Override
	public Set<LETTER> lettersReturnSummary(STATE state) {
		return mNwa.lettersReturnSummary(state);
	}

	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> returnSummarySuccessor(
			LETTER letter, STATE hier) {
		return mNwa.returnSummarySuccessor(letter, hier);
	}
	
	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> returnSummarySuccessor(
			STATE hier) {
		return mNwa.returnSummarySuccessor(hier);
	}

	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			LETTER letter, STATE succ) {
		return mNwa.internalPredecessors(letter, succ);
	}

	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			STATE succ) {
		return mNwa.internalPredecessors(succ);
	}

	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			LETTER letter, STATE succ) {
		return mNwa.callPredecessors(letter, succ);
	}

	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			STATE succ) {
		return mNwa.callPredecessors(succ);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state, LETTER letter) {
		return mNwa.internalSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state) {
		return mNwa.internalSuccessors(state);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state, LETTER letter) {
		return mNwa.callSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state) {
		return mNwa.callSuccessors(state);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			STATE hier, LETTER letter, STATE succ) {
		return mNwa.returnPredecessors(hier, letter, succ);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			LETTER letter, STATE succ) {
		return mNwa.returnPredecessors(letter, succ);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			STATE succ) {
		return mNwa.returnPredecessors(succ);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			STATE state, STATE hier, LETTER letter) {
		return mNwa.returnSuccessors(state, hier, letter);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			STATE state, LETTER letter) {
		return mNwa.returnSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			STATE state) {
		return mNwa.returnSuccessors(state);
	}

	@Override
	public String sizeInformation() {
		return mNwa.sizeInformation();
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			STATE state, STATE hier) {
		return mNwa.returnSuccessorsGivenHier(state, hier);
	}

	@Override
	public Collection<STATE> getFinalStates() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Iterable<STATE> succInternal(final STATE state, final LETTER letter) {
		return new Iterable<STATE>() {
			Iterable<OutgoingInternalTransition<LETTER,STATE>> mIterable;
			{
				mIterable = mNwa.internalSuccessors(state,letter);
			}
			@Override
			public Iterator<STATE> iterator() {
				final Iterator<STATE> iterator = new Iterator<STATE>() {
				Iterator<OutgoingInternalTransition<LETTER,STATE>> mBackingIterator;
				{
					mBackingIterator = mIterable.iterator();
				}
					@Override
					public boolean hasNext() {
						return mBackingIterator.hasNext();
					}

					@Override
					public STATE next() {
							return mBackingIterator.next().getSucc();
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
				};
				return iterator;
			}
		};
	}

	@Override
	public Iterable<STATE> succCall(final STATE state, final LETTER letter) {
		return new Iterable<STATE>() {
			Iterable<OutgoingCallTransition<LETTER,STATE>> mIterable;
			{
				mIterable = mNwa.callSuccessors(state,letter);
			}
			@Override
			public Iterator<STATE> iterator() {
				final Iterator<STATE> iterator = new Iterator<STATE>() {
				Iterator<OutgoingCallTransition<LETTER,STATE>> mBackingIterator;
				{
					mBackingIterator = mIterable.iterator();
				}
					@Override
					public boolean hasNext() {
						return mBackingIterator.hasNext();
					}

					@Override
					public STATE next() {
							return mBackingIterator.next().getSucc();
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
				};
				return iterator;
			}
		};
	}

	@Override
	public Iterable<STATE> hierPred(STATE state, LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<STATE> succReturn(final STATE state, STATE hier, final LETTER letter) {
		return new Iterable<STATE>() {
			Iterable<OutgoingReturnTransition<LETTER,STATE>> mIterable;
			{
				mIterable = mNwa.returnSuccessors(state,letter);
			}
			@Override
			public Iterator<STATE> iterator() {
				final Iterator<STATE> iterator = new Iterator<STATE>() {
				Iterator<OutgoingReturnTransition<LETTER,STATE>> mBackingIterator;
				{
					mBackingIterator = mIterable.iterator();
				}
					@Override
					public boolean hasNext() {
						return mBackingIterator.hasNext();
					}

					@Override
					public STATE next() {
							return mBackingIterator.next().getSucc();
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
				};
				return iterator;
			}
		};
	}

	@Override
	public Iterable<STATE> predInternal(STATE state, LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<STATE> predCall(STATE state, LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean finalIsTrap() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean isDeterministic() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean isTotal() {
		throw new UnsupportedOperationException();
	}

}
