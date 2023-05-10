/*
 * Copyright (C) 2023 Philipp Müller (pm251@venus.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.automata.rabin;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Converts a Buchi automaton to a Rabin automaton via {@link Buchi2RabinAutomaton} as a General Operation
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 *            type of letter
 * @param <STATE>
 *            type of state
 */
public class ToRabin<LETTER, STATE> extends GeneralOperation<LETTER, STATE, IStateFactory<STATE>> {

	private final IRabinAutomaton<LETTER, STATE> mConversionAutomaton;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mBuchiAutomaton;

	/**
	 * Converts a Buchi automaton to a Rabin automaton via {@link Buchi2RabinAutomaton}, this constructs a General
	 * Operation
	 *
	 * @param services
	 *            services
	 * @param automaton
	 *            Buchi automaton
	 */
	public ToRabin(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> automaton) {
		super(services);
		mConversionAutomaton = new Buchi2RabinAutomaton<>(automaton);
		mBuchiAutomaton = automaton;

	}

	@Override
	public IRabinAutomaton<LETTER, STATE> getResult() {
		return mConversionAutomaton;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataOperationCanceledException {
		return (new IsEmpty<>(mServices, mConversionAutomaton)
				.getResult() == new BuchiIsEmpty<>(mServices, mBuchiAutomaton).getResult());
	}
}
