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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Represents the complement of a deterministic and total nested word automaton.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class ComplementDeterministicNwa<LETTER, STATE> implements INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> {
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;

	/**
	 * Constructor.
	 * 
	 * @param operand
	 *            operand
	 */
	public ComplementDeterministicNwa(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand) {
		if (operand instanceof DeterminizeNwa) {
			if (!((DeterminizeNwa<LETTER, STATE>) operand).isTotal()) {
				throw new AssertionError("can only complement total automata");
			}
			mOperand = operand;
		} else if ((operand instanceof TotalizeNwa) || isDeterministicTotalNwa(operand)) {
			mOperand = operand;
		} else {
			throw new IllegalArgumentException("input not known to be deterministic");
		}
	}

	private static boolean isDeterministicTotalNwa(final INwaOutgoingLetterAndTransitionProvider<?, ?> operand) {
		throw new UnsupportedOperationException("this check is currently not supported");
	}

	@Override
	public Iterable<STATE> getInitialStates() {
		return mOperand.getInitialStates();
	}

	@Override
	public VpAlphabet<LETTER> getVpAlphabet() {
		return mOperand.getVpAlphabet();
	}

	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mOperand.getStateFactory();
	}

	@Override
	public boolean isInitial(final STATE state) {
		return mOperand.isInitial(state);
	}

	@Override
	public boolean isFinal(final STATE state) {
		return !mOperand.isFinal(state);
	}

	@Override
	public STATE getEmptyStackState() {
		return mOperand.getEmptyStackState();
	}

	@Override
	public Set<LETTER> lettersInternal(final STATE state) {
		return mOperand.getVpAlphabet().getInternalAlphabet();
	}

	@Override
	public Set<LETTER> lettersCall(final STATE state) {
		return mOperand.getVpAlphabet().getCallAlphabet();
	}
	
	@Override
	public Set<LETTER> lettersReturn(final STATE state, final STATE hier) {
		return mOperand.getVpAlphabet().getReturnAlphabet();
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state,
			final LETTER letter) {
		return mOperand.internalSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state) {
		return mOperand.internalSuccessors(state);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state, final LETTER letter) {
		return mOperand.callSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state) {
		return mOperand.callSuccessors(state);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final STATE hier,
			final LETTER letter) {
		return mOperand.returnSuccessors(state, hier, letter);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(final STATE state,
			final STATE hier) {
		return mOperand.returnSuccessorsGivenHier(state, hier);
	}

	@Override
	public int size() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mOperand.getAlphabet();
	}

	@Override
	public String sizeInformation() {
		// TODO Auto-generated method stub
		return null;
	}
}
