/*
 * Copyright (C) 2015 Carl Kuesters
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating;

import java.util.BitSet;
import java.util.Collections;
import java.util.LinkedList;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

public class AA_DeterminizeReversed<LETTER> implements IOperation<LETTER, BitSet>{

	public AA_DeterminizeReversed(final AutomataLibraryServices ultimateServiceProvider, final AlternatingAutomaton<LETTER, BitSet> alternatingAutomaton){
		resultAutomaton = new NestedWordAutomaton<LETTER, BitSet>(
				ultimateServiceProvider,
				alternatingAutomaton.getAlphabet(),
				Collections.<LETTER>emptySet(),
				Collections.<LETTER>emptySet(),
				alternatingAutomaton.getStateFactory()
			);
		final LinkedList<BitSet> newStates = new LinkedList<BitSet>();
		newStates.add(alternatingAutomaton.getFinalStatesBitVector());
		while(!newStates.isEmpty()){
			final BitSet state = newStates.getFirst();
			final boolean isInitial = (state == alternatingAutomaton.getFinalStatesBitVector());
			final boolean isFinal = alternatingAutomaton.getAcceptingFunction().getResult(state);
			resultAutomaton.addState(isInitial, isFinal, state);
			for(final LETTER letter : alternatingAutomaton.getAlphabet()){
				final BitSet nextState = (BitSet) state.clone();
				alternatingAutomaton.resolveLetter(letter, nextState);
				resultAutomaton.addInternalTransition(state, letter, nextState);
				if(!resultAutomaton.getStates().contains(nextState)){
					if(!newStates.contains(nextState)){
						newStates.add(nextState);
					}
				}
			}
			newStates.removeFirst();
		}
	}
	private final NestedWordAutomaton<LETTER, BitSet> resultAutomaton;
	
	@Override
	public String operationName(){
		return "AA_DeterminizeReversed";
	}

	@Override
	public String startMessage(){
		return "Start: " + operationName();
	}

	@Override
	public String exitMessage(){
		return "Exit: " + operationName();
	}

	@Override
	public INestedWordAutomaton<LETTER, BitSet> getResult() throws AutomataLibraryException{
		return resultAutomaton;
	}

	@Override
	public boolean checkResult(final StateFactory<BitSet> stateFactory) throws AutomataLibraryException{
		return true;
	}
}
