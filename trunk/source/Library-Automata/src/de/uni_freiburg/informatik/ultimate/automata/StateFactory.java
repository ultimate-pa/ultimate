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
package de.uni_freiburg.informatik.ultimate.automata;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.LevelRankingState;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.Condition;

public abstract class StateFactory<STATE> {
	
	public STATE intersection(STATE s1, STATE s2) {
		return null;
	}
	
	public STATE intersectBuchi(STATE s1, STATE s2, int track) {
		return intersection(s1, s2);
	}
	
	public STATE determinize(Map<STATE,Set<STATE>> down2up) {
		return null;
	}
	
	public STATE createSinkStateContent() {
		return null;
	}
	
	public STATE createEmptyStackState() {
		return null;
	}

	public STATE getContentOnPetriNet2FiniteAutomaton(
			Marking<?, STATE> marking) {
		return null;
	}
	
	public STATE getContentOnConcurrentProduct(STATE c1, STATE c2) {
		return intersection(c1, c2);
	}
	
	public STATE getWhiteContent(STATE c) {
		return c;
	}
	
	public STATE getBlackContent(STATE c) {
		return c;
	}
	
	public STATE buchiComplementFKV(LevelRankingState<?, STATE> compl) {
		return null;
	}
	
	public STATE buchiComplementNCSB(LevelRankingState<?, STATE> compl) {
		return null;
	}
	
	public STATE complementBuchiDeterministicNonFinal(STATE c) {
		return null;
	}
	
	public STATE complementBuchiDeterministicFinal(STATE c) {
		return null;
	}
	
	public STATE minimize(Collection<STATE> states) {
		return null;	
	}

	public STATE createDoubleDeckerContent(STATE down, STATE up) {
		return null;
	}
	
	public STATE constructBuchiSVWState(Integer stateNb, Integer tmaNb) {
		return null;
	}
	
	public STATE finitePrefix2net(Condition<?, STATE> c) {
		return null;
	}
	
	public STATE senwa(STATE entry, STATE state) {
		return null;
	}
}
