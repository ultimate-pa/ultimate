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
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * A GeneralOperation for a Union over two Rabin automata
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 *            type of letter
 * @param <STATE>
 *            type of state
 * @param <CRSF>
 *            a StateFactory implementing {@link IBlackWhiteStateFactory}
 */
public class Union<LETTER, STATE, CRSF extends IBlackWhiteStateFactory<STATE>>
		extends GeneralOperation<LETTER, STATE, IStateFactory<STATE>> {
	private final IRabinAutomaton<LETTER, STATE> mResult;
	private final IRabinAutomaton<LETTER, STATE> mFirst;
	private final IRabinAutomaton<LETTER, STATE> mSecond;

	/**
	 * Constructs a GeneralOperation for uniting two declared Rabin automata
	 *
	 * @param services
	 *            services
	 * @param factory
	 *            some IBlackWhiteStateFactory for STATE
	 * @param firstAutomaton
	 *            first Rabin automaton
	 * @param secondAutomaton
	 *            second Rabin automaton
	 */
	public Union(final AutomataLibraryServices services, final CRSF factory,
			final IRabinAutomaton<LETTER, STATE> firstAutomaton, final IRabinAutomaton<LETTER, STATE> secondAutomaton) {
		super(services);
		mResult = new RabinUnion<>(firstAutomaton, secondAutomaton, factory);
		mFirst = firstAutomaton;
		mSecond = secondAutomaton;
	}

	@Override
	public IRabinAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataOperationCanceledException {
		return (new IsEmpty<>(mServices, mResult).getResult() == (new IsEmpty<>(mServices, mFirst).getResult()
				&& new IsEmpty<>(mServices, mSecond).getResult()));
	}
}
