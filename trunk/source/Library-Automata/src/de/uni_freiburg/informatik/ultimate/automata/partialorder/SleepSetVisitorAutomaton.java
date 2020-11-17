/*
 * Copyright (C) 2020 Marcel Ebbinghaus
 * Copyright (C) 2020 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;

public class SleepSetVisitorAutomaton<L, S> implements IPartialOrderVisitor<L, S> {
	
	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;
	private final NestedWordAutomaton<L, S> mReductionAutomaton;

	public SleepSetVisitorAutomaton(final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final AutomataLibraryServices services, final IEmptyStackStateFactory<S> stateFactory) {
		mOperand = operand;
		mReductionAutomaton = new NestedWordAutomaton<>(services, mOperand.getVpAlphabet(), stateFactory);
	}
	@Override
	public void discoverState() {
		// do nothing
		
	}
	@Override
	public boolean discoverTransition(S source, L letter, S target) {
		// add succState to the automaton
		if (!mReductionAutomaton.contains(target)) {
			mReductionAutomaton.addState(false, mOperand.isFinal(target), target);
		}
		// add transition from currentState to succState to the automaton
		mReductionAutomaton.addInternalTransition(source, letter, target);
		return mOperand.isFinal(target);
	}

	@Override
	public void backtrackState(Object state) {
		// do nothing
	}
	
	public NestedWordAutomaton<L, S> getReductionAutomaton(){
		return mReductionAutomaton;
	}
	
	@Override
	public void addStartState(S state) {
		mReductionAutomaton.addState(true, mOperand.isFinal(state), state);
		
	}

}
