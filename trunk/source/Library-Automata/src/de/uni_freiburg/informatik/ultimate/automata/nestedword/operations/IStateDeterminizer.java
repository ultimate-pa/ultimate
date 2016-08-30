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


public interface IStateDeterminizer<LETTER,STATE> {
	
	DeterminizedState<LETTER,STATE> initialState();
	
	/**
	 * Given a DeterminizedState detState, return the successor state under an
	 * internal transition labeled with symbol.
	 */
	DeterminizedState<LETTER,STATE> internalSuccessor(DeterminizedState<LETTER,STATE> detState,
											 LETTER symbol);

	
	/**
	 * Compute successor detState under call transition of a detState
	 * and symbol. 
	 */
	DeterminizedState<LETTER,STATE> callSuccessor(DeterminizedState<LETTER,STATE> detState, 
										 LETTER symbol);

	
	/**
	 * Given a DeterminizedState detState, return the successor state under a
	 * return transition for linear predecessor linPred labeled with symbol.
	 */
	DeterminizedState<LETTER,STATE> returnSuccessor(DeterminizedState<LETTER,STATE> detState,
										   DeterminizedState<LETTER,STATE> linPred,
										   LETTER symbol);

	int getMaxDegreeOfNondeterminism();
	
	/**
	 * If true, the constructed DeterminizedStates are sets of DoubleDecker,
	 * needed, e.g. for exact determinization of nested word automata.
	 * If false, the constructed DeterminziedStates are sets of States. This
	 * is sufficient for exact determinization of finite automata. We also use
	 * these DeterminziedStates for determinizations where the resulting
	 * automaton recognizes a superset of the input automatons language.
	 */
	boolean useDoubleDeckers();
	
	STATE getState(DeterminizedState<LETTER,STATE> determinizedState);
}
