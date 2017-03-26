/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DeterminizedState;

/**
 * Interface for state determinizers.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public interface IStateDeterminizer<LETTER, STATE> {
	/**
	 * @return The initial state.
	 */
	DeterminizedState<LETTER, STATE> initialState();

	/**
	 * @param detState
	 *            determinized state
	 * @param letter
	 *            letter
	 * @return Given a DeterminizedState detState, return the successor state under an internal transition labeled with
	 *         symbol.
	 */
	DeterminizedState<LETTER, STATE> internalSuccessor(DeterminizedState<LETTER, STATE> detState, LETTER letter);

	/**
	 * @param detState
	 *            determinized state
	 * @param letter
	 *            letter
	 * @return The successor detState under call transition of a detState and symbol.
	 */
	DeterminizedState<LETTER, STATE> callSuccessor(DeterminizedState<LETTER, STATE> detState, LETTER letter);

	/**
	 * @param detState
	 *            determinized state
	 * @param linPred
	 *            linear predecessor state
	 * @param letter
	 *            letter
	 * @return Given a DeterminizedState detState, return the successor state under a return transition for linear
	 *         predecessor linPred labeled with symbol.
	 */
	DeterminizedState<LETTER, STATE> returnSuccessor(DeterminizedState<LETTER, STATE> detState,
			DeterminizedState<LETTER, STATE> linPred, LETTER letter);

	/**
	 * @return Maximum degree of nondeterminism.
	 */
	int getMaxDegreeOfNondeterminism();

	/**
	 * If {@code true}, the constructed DeterminizedStates are sets of
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker DoubleDecker}, needed, e.g. for exact
	 * determinization of nested word automata. If {@code false}, the constructed DeterminizedStates are sets of
	 * {@link STATE}s. This is sufficient for exact determinization of finite automata. We also use these
	 * DeterminizedStates for determinizations where the resulting automaton recognizes a superset of the input
	 * automaton's language.
	 * 
	 * @return {@code true} iff {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker
	 *         DoubleDecker} is used.
	 */
	boolean useDoubleDeckers();

	/**
	 * @param determinizedState
	 *            A determinized state.
	 * @return the corresponding state
	 */
	STATE getState(DeterminizedState<LETTER, STATE> determinizedState);
}
