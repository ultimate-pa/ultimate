/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Checks whether a nested word automaton is total.
 * <p>
 * An NWA is total if for each state and symbol there is an outgoing transition. For return transitions, we require that
 * for each hierarchical predecessor there is a transition with each return symbol.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class IsTotal<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {
	private final boolean mResult;
	private final INestedWordAutomaton<LETTER, STATE> mOperand;

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            input NWA
	 */
	public IsTotal(final AutomataLibraryServices services, final INestedWordAutomaton<LETTER, STATE> operand) {
		super(services);
		mOperand = operand;
		mResult = computeIsTotal();
		if (mLogger.isInfoEnabled()) {
			mLogger.info("automaton is " + (mResult ? "" : "not ") + "total");
		}
	}

	/**
	 * @return {@code true} iff automaton is total according to contract.
	 */
	private boolean computeIsTotal() {
		for (final STATE state : mOperand.getStates()) {
			if (!isTotal(state)) {
				return false;
			}
		}
		return true;
	}

	/**
	 * @param state
	 *            The state for which totality is tested.
	 * @return {@code true} iff the given state has all outgoing transitions
	 */
	private boolean isTotal(final STATE state) {
		// internals
		for (final LETTER symbol : mOperand.getVpAlphabet().getInternalAlphabet()) {
			final Iterable<OutgoingInternalTransition<LETTER, STATE>> it = mOperand.internalSuccessors(state, symbol);
			if (!it.iterator().hasNext()) {
				return false;
			}
		}

		// calls
		for (final LETTER symbol : mOperand.getVpAlphabet().getCallAlphabet()) {
			final Iterable<OutgoingCallTransition<LETTER, STATE>> it = mOperand.callSuccessors(state, symbol);
			if (!it.iterator().hasNext()) {
				return false;
			}
		}

		// returns
		for (final LETTER symbol : mOperand.getVpAlphabet().getReturnAlphabet()) {
			for (final STATE hier : mOperand.getStates()) {
				// TODO Christian 2016-09-18: Is this what we want? How can we check that 'hier' is a valid candidate?
				final Iterable<OutgoingReturnTransition<LETTER, STATE>> it =
						mOperand.returnSuccessors(state, hier, symbol);
				if (!it.iterator().hasNext()) {
					return false;
				}
			}
		}
		return true;
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}
}
