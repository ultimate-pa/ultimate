/*
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DoubleDeckerVisitor.ReachFinal;

public class DoubleDeckerAutomaton<LETTER, STATE> extends NestedWordAutomaton<LETTER, STATE> 
							implements IDoubleDeckerAutomaton<LETTER, STATE> {
	
	
	private Map<STATE,Map<STATE,ReachFinal>> mUp2Down;
	
	public DoubleDeckerAutomaton(AutomataLibraryServices services, 
			Set<LETTER> internalAlphabet,
			Set<LETTER> callAlphabet,
			Set<LETTER> returnAlphabet,
			   StateFactory<STATE> stateFactory) {
		super(services, internalAlphabet, callAlphabet, returnAlphabet, stateFactory);
	}
	
	
	public boolean up2DownIsSet() {
		return mUp2Down != null; 
	}
	
	@Override
	@Deprecated
	public Set<STATE> getDownStates(STATE up) {
		return mUp2Down.get(up).keySet();
	}
	
	public void setUp2Down(Map<STATE,Map<STATE,ReachFinal>> up2Down) {
		if (mUp2Down == null) {
			mUp2Down = up2Down;
		} else {
			throw new AssertionError("up2down already set");
		}
	}
	
	
	
	/**
	 * Returns true iff there is a reachable configuration in which the 
	 * automaton is in STATE <i>up</i> and the STATE <i>down</i> is the topmost
	 * stack element.
	 */
	@Override
	public boolean isDoubleDecker(STATE up, STATE down) {
		if (mUp2Down == null) {
			throw new AssertionError("up2down not set");
		} else {
			if (getStates().contains(up)) {
				final Map<STATE, ReachFinal> downStates = mUp2Down.get(up);
				if (getStates().contains(down)) {
					return downStates.get(down) != null;
				} else {
					return false;
				}
			} else {
				return false;
			}
		}
	}
}
