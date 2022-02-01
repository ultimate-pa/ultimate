/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Default implementation for NWAs with epsilon transitions.
 * 
 * 20180122 Matthias: Warning! This is a higly provisional solution. It is yet
 * unclear how we are going to implement epsilon transitions in the long run.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class EpsilonNestedWordAutomaton<LETTER, STATE, A extends INestedWordAutomaton<LETTER, STATE>>
		implements IEpsilonNestedWordAutomaton<LETTER, STATE> {

	private final A mBackingNestedWordAutomaton;
	private final HashRelation<STATE, STATE> mOutgoingEpsilonTransitions;

	public EpsilonNestedWordAutomaton(final A backingNestedWordAutomaton,
			final HashRelation<STATE, STATE> outgoingEpsilonTransitions) {
		super();
		mBackingNestedWordAutomaton = backingNestedWordAutomaton;
		mOutgoingEpsilonTransitions = outgoingEpsilonTransitions;
	}

	@Override
	public Iterable<STATE> epsilonSuccessors(final STATE state) {
		return mOutgoingEpsilonTransitions.getImage(state);
	}

	@Override
	public VpAlphabet<LETTER> getVpAlphabet() {
		return mBackingNestedWordAutomaton.getVpAlphabet();
	}

	@Override
	public STATE getEmptyStackState() {
		return mBackingNestedWordAutomaton.getEmptyStackState();
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mBackingNestedWordAutomaton.getAlphabet();
	}

	@Override
	public boolean isInitial(final STATE state) {
		return mBackingNestedWordAutomaton.isInitial(state);
	}

	@Override
	public boolean isFinal(final STATE state) {
		return mBackingNestedWordAutomaton.isFinal(state);
	}

	@Override
	public int size() {
		return mBackingNestedWordAutomaton.size();
	}

	@Override
	public String sizeInformation() {
		return mBackingNestedWordAutomaton.sizeInformation();
	}

	@Override
	public Set<STATE> getStates() {
		return mBackingNestedWordAutomaton.getStates();
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state,
			final LETTER letter) {
		return mBackingNestedWordAutomaton.internalSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state, final LETTER letter) {
		return mBackingNestedWordAutomaton.callSuccessors(state, letter);
	}

	@Override
	public Set<STATE> getInitialStates() {
		return mBackingNestedWordAutomaton.getInitialStates();
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final STATE hier,
			final LETTER letter) {
		return mBackingNestedWordAutomaton.returnSuccessors(state, hier, letter);
	}

	@Override
	public Collection<STATE> getFinalStates() {
		return mBackingNestedWordAutomaton.getFinalStates();
	}

	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mBackingNestedWordAutomaton.getStateFactory();
	}

	@Override
	public Set<LETTER> lettersReturn(final STATE state) {
		return mBackingNestedWordAutomaton.lettersReturn(state);
	}

	@Override
	public Set<LETTER> lettersInternalIncoming(final STATE state) {
		return mBackingNestedWordAutomaton.lettersInternalIncoming(state);
	}

	@Override
	public Set<LETTER> lettersCallIncoming(final STATE state) {
		return mBackingNestedWordAutomaton.lettersCallIncoming(state);
	}

	@Override
	public Set<LETTER> lettersReturnIncoming(final STATE state) {
		return mBackingNestedWordAutomaton.lettersReturnIncoming(state);
	}

	@Override
	public Set<LETTER> lettersSummary(final STATE state) {
		return mBackingNestedWordAutomaton.lettersSummary(state);
	}

	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(final STATE succ,
			final LETTER letter) {
		return mBackingNestedWordAutomaton.internalPredecessors(succ, letter);
	}

	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(final STATE succ) {
		return mBackingNestedWordAutomaton.internalPredecessors(succ);
	}

	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(final STATE succ, final LETTER letter) {
		return mBackingNestedWordAutomaton.callPredecessors(succ, letter);
	}

	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(final STATE succ) {
		return mBackingNestedWordAutomaton.callPredecessors(succ);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final STATE succ, final STATE hier,
			final LETTER letter) {
		return mBackingNestedWordAutomaton.returnPredecessors(succ, hier, letter);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final STATE succ, final LETTER letter) {
		return mBackingNestedWordAutomaton.returnPredecessors(succ, letter);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final STATE succ) {
		return mBackingNestedWordAutomaton.returnPredecessors(succ);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state) {
		return mBackingNestedWordAutomaton.returnSuccessors(state);
	}

	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> summarySuccessors(final STATE hier, final LETTER letter) {
		return mBackingNestedWordAutomaton.summarySuccessors(hier, letter);
	}

	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> summarySuccessors(final STATE hier) {
		return mBackingNestedWordAutomaton.summarySuccessors(hier);
	}

}
