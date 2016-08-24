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
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.SummaryReturnTransition;

public class INWA2INestedWordAutomaton<LETTER, STATE>
		implements INestedWordAutomaton<LETTER, STATE> {
	
	private final INestedWordAutomaton<LETTER, STATE> mNwa;
	
	/**
	 * @param inwa nested word automaton
	 */
	public INWA2INestedWordAutomaton(
			final INestedWordAutomaton<LETTER, STATE> inwa) {
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
	public boolean isInitial(final STATE state) {
		return mNwa.isInitial(state);
	}

	@Override
	public boolean isFinal(final STATE state) {
		return mNwa.isFinal(state);
	}

	@Override
	public Set<LETTER> lettersInternal(final STATE state) {
		return mNwa.lettersInternal(state);
	}

	@Override
	public Set<LETTER> lettersInternalIncoming(final STATE state) {
		return mNwa.lettersInternalIncoming(state);
	}

	@Override
	public Set<LETTER> lettersCall(final STATE state) {
		return mNwa.lettersCall(state);
	}

	@Override
	public Set<LETTER> lettersCallIncoming(final STATE state) {
		return mNwa.lettersCallIncoming(state);
	}

	@Override
	public Set<LETTER> lettersReturn(final STATE state) {
		return mNwa.lettersReturn(state);
	}

	@Override
	public Set<LETTER> lettersReturnIncoming(final STATE state) {
		return mNwa.lettersReturnIncoming(state);
	}

	@Override
	public Set<LETTER> lettersSummary(final STATE state) {
		return mNwa.lettersSummary(state);
	}

	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> summarySuccessors(
			final STATE hier, final LETTER letter) {
		return mNwa.summarySuccessors(hier, letter);
	}
	
	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> summarySuccessors(
			final STATE hier) {
		return mNwa.summarySuccessors(hier);
	}

	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			final STATE succ, final LETTER letter) {
		return mNwa.internalPredecessors(succ, letter);
	}

	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			final STATE succ) {
		return mNwa.internalPredecessors(succ);
	}

	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			final STATE succ, final LETTER letter) {
		return mNwa.callPredecessors(succ, letter);
	}

	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			final STATE succ) {
		return mNwa.callPredecessors(succ);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final STATE state, final LETTER letter) {
		return mNwa.internalSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final STATE state) {
		return mNwa.internalSuccessors(state);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final STATE state, final LETTER letter) {
		return mNwa.callSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final STATE state) {
		return mNwa.callSuccessors(state);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final STATE succ, final STATE hier, final LETTER letter) {
		return mNwa.returnPredecessors(succ, hier, letter);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final STATE succ, final LETTER letter) {
		return mNwa.returnPredecessors(succ, letter);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final STATE succ) {
		return mNwa.returnPredecessors(succ);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final STATE state, final STATE hier, final LETTER letter) {
		return mNwa.returnSuccessors(state, hier, letter);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final STATE state, final LETTER letter) {
		return mNwa.returnSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final STATE state) {
		return mNwa.returnSuccessors(state);
	}

	@Override
	public String sizeInformation() {
		return mNwa.sizeInformation();
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			final STATE state, final STATE hier) {
		return mNwa.returnSuccessorsGivenHier(state, hier);
	}

	@Override
	public Collection<STATE> getFinalStates() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Iterable<STATE> hierarchicalPredecessorsOutgoing(final STATE state, final LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}
}
