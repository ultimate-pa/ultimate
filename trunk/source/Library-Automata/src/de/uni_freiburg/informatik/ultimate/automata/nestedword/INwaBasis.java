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

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;


/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <STATE>
 */
public interface INwaBasis<LETTER, STATE> extends IAutomaton<LETTER, STATE> {

	/**
	 * @return StateFactory that was used to construct this automaton.
	 * @deprecated Automata should not provide their state factory anymore.
	 */
	@Deprecated
	IStateFactory<STATE> getStateFactory();

	VpAlphabet<LETTER> getVpAlphabet();

	@Override
	default Set<LETTER> getAlphabet() {
		return getVpAlphabet().getInternalAlphabet();
	}

	/**
	 * @return Auxiliary state used to model the hierarchical predecessor of a pending return in some operations.<br>
	 *         Recall that we generally do not accept nested words with pending returns. This auxiliary state is
	 *         <i>never</i> contained in the set of states. Viewing nested word automata as visibly pushdown automata,
	 *         this state can be seen as a "bottom letter" of the pushdown alphabet.
	 */
	STATE getEmptyStackState();

	/**
	 * @return All initial states of the automaton.
	 */
	Iterable<STATE> getInitialStates();

	/**
	 * @param state
	 *            state
	 * @return true iff the state is initial.
	 */
	boolean isInitial(STATE state);

	/**
	 * @param state
	 *            state
	 * @return true iff the state is final.
	 */
	boolean isFinal(STATE state);

}