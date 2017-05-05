/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

/**
 * Interface for a Nested Word Automaton that is defined by its outgoing 
 * transitions. Outgoing transitions are sufficient for the {@link NestedWordAutomatonReachableStates}
 * to construct a {@link IDoubleDeckerAutomaton}
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            Type of objects which can be used as letters of the alphabet.
 * @param <STATE>
 *            Type of objects which can be used as states.
 */
public class NwaSuccessorProvider2TransitionProviderAdapter<LETTER, STATE> implements INestedWordAutomatonSimple<LETTER, STATE> {
	private final INwaSuccessorProvider<LETTER, STATE> mSuccessorProvider;

	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mSuccessorProvider.getStateFactory();
	}

	@Override
	public Set<LETTER> getInternalAlphabet() {
		return mSuccessorProvider.getInternalAlphabet();
	}

	@Override
	public int size() {
		return mSuccessorProvider.size();
	}

	@Override
	public String sizeInformation() {
		return mSuccessorProvider.sizeInformation();
	}

	@Override
	public Set<LETTER> getCallAlphabet() {
		return mSuccessorProvider.getCallAlphabet();
	}

	@Override
	public Set<LETTER> getReturnAlphabet() {
		return mSuccessorProvider.getReturnAlphabet();
	}

	@Override
	public IElement transformToUltimateModel(final AutomataLibraryServices services)
			throws AutomataOperationCanceledException {
		return mSuccessorProvider.transformToUltimateModel(services);
	}

	@Override
	public STATE getEmptyStackState() {
		return mSuccessorProvider.getEmptyStackState();
	}

	@Override
	public Iterable<STATE> getInitialStates() {
		return mSuccessorProvider.getInitialStates();
	}

	@Override
	public boolean isInitial(final STATE state) {
		return mSuccessorProvider.isInitial(state);
	}

	@Override
	public boolean isFinal(final STATE state) {
		return mSuccessorProvider.isFinal(state);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state) {
		return mSuccessorProvider.internalSuccessors(state);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state) {
		return mSuccessorProvider.callSuccessors(state);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(final STATE state, final STATE hier) {
		return mSuccessorProvider.returnSuccessorsGivenHier(state, hier);
	}

	@Override
	public Set<LETTER> getAlphabet() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<LETTER> lettersInternal(final STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<LETTER> lettersCall(final STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<LETTER> lettersReturn(final STATE state, final STATE hier) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<LETTER> lettersReturn(final STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state, final LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state, final LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final STATE hier, final LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}
	
	
	
}