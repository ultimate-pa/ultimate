/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;



public interface INestedWordAutomatonOldApi<LETTER,STATE> 
										extends IAutomaton<LETTER,STATE>, INestedWordAutomaton<LETTER, STATE> {


	
	/**
	 * @return All states succ such that state has an outgoing 
	 * internal transition (state, letter, succ)
	 */
	public Iterable<STATE> succInternal(STATE state, LETTER letter);
	
	/**
	 * @return All states succ such that state has an outgoing 
	 * call transition (state, letter, succ)
	 */
	public Iterable<STATE> succCall(STATE state, LETTER letter);
	
	
	
	/**
	 * @return All states succ such that state has an outgoing 
	 * return transition (state, hier, letter, succ)
	 */
	public Iterable<STATE> succReturn(STATE state, STATE hier, LETTER letter);

	/**
	 * @return All states pred such that there is an incoming 
	 * internal transition (pred, letter, state)
	 */
	public Iterable<STATE> predInternal(STATE state, LETTER letter);

	/**
	 * @return All states pred such that there is an incoming 
	 * call transition (pred, letter, state)
	 */
	public Iterable<STATE> predCall(STATE state, LETTER letter);
	
	
	/**
	 * @return All states pred such that there is an incoming 
	 * return transition (pred, hier, letter, state)
	 */
	public Iterable<STATE> predReturnLin(STATE state, LETTER letter, STATE hier);

	/**
	 * @return All states hier such that there is a state pred such that there 
	 * is an incoming return transition (pred, hier, letter, state)
	 */
	public Iterable<STATE> predReturnHier(STATE state, LETTER letter);
	
	
	
	
	/**
	 * Return true iff we can not leave the set of final states, i.e.,
	 * if q is final and there is a transitions (q,a,q') then q' is final.
	 * Not important. Only used to check correctness of one operation. Might
	 * be moved to this operation.
	 * 
	 */
	public boolean finalIsTrap();
	

	/**
	 * Return true iff there is at most one initial state and for each state q
	 * of the automaton the following holds
	 * <ul>
	 * <li> for each letter a of the internal alphabet there is at most one
	 * transition (q,a,q').
	 * <li> for each letter a of the call alphabet there is at most one
	 * transition (q,a,q').
	 * <li> for each letter a of the return alphabet and each state q̀ of the 
	 * automaton there is at most one transition (q,q̀,a,q').
	 * </ul>
	 */
	public boolean isDeterministic();
	
	
	/**
	 * @return true iff there is at least one initial state and for each state
	 * q and each letter a 
	 * <ul>
	 *  <li> q has an outgoing internal transition labeled with a.
	 *  <li> q has an outgoing call transition labeled with a.
	 *  <li> q has an outgoing return transition labeled with a.
	 * </ul>
	 */
	boolean isTotal();
	
	
}
