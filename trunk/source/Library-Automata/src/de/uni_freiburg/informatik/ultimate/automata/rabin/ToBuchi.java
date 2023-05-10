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
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * A GeneralOperation for conversion of a Rabin to a Buchi automaton
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 * @param <CRSF>
 *            state factory with IBlackWhiteState & IEmptyStackState functionality
 */
public class ToBuchi<LETTER, STATE, CRSF extends IBlackWhiteStateFactory<STATE> & IEmptyStackStateFactory<STATE>>
		extends GeneralOperation<LETTER, STATE, IStateFactory<STATE>> {
	private final Rabin2BuchiAutomaton<LETTER, STATE, CRSF> mConversionAutomaton;
	private final IRabinAutomaton<LETTER, STATE> mRabinAutomaton;

	/**
	 * constructor finalizing a Rabin Automaton and State Factory for this conversion
	 *
	 * @param services
	 *            AutomataLibraryServices
	 * @param factory
	 *            state factory with IBlackWhiteState & IEmptyStackState functionality
	 * @param automaton
	 *            Rabin automaton
	 */

	public ToBuchi(final AutomataLibraryServices services, final CRSF factory,
			final IRabinAutomaton<LETTER, STATE> automaton) {
		super(services);
		mConversionAutomaton = new Rabin2BuchiAutomaton<>(automaton, factory);
		mRabinAutomaton = automaton;
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getResult() {
		return mConversionAutomaton;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataOperationCanceledException {
		return (new IsEmpty<>(mServices, mRabinAutomaton)
				.getResult() == new BuchiIsEmpty<>(mServices, mConversionAutomaton).getResult());
	}
}
