/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.statefactory;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.MonitorProduct;

/**
 * State factory for {@link MonitorProduct}.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <S1>
 *            State type of monitored automaton
 * @param <S2>
 *            State type of monitor
 * @param <STATE>
 *            State type of product automaton
 */
public interface IMonitorStateFactory<S1, S2, STATE> extends IEmptyStackStateFactory<STATE> {
	/**
	 * Creates a product state.
	 *
	 * @param fst
	 *            The state of the first operand
	 * @param snd
	 *            The state of the second operand (the monitor)
	 * @return the product state
	 */
	STATE product(final S1 fst, final S2 snd);
}
