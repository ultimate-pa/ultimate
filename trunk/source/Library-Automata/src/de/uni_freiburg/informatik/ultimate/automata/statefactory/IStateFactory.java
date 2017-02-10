/*
 * Copyright (C) 2012-2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2016 University of Freiburg
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

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;

/**
 * Abstract factory for states used in typical automata operations.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <STATE>
 *            state type
 */
@SuppressWarnings("squid:S1172")
public interface IStateFactory<STATE> {
	/**
	 * Intersection of two states ("product construction").
	 * 
	 * @param state1
	 *            first state
	 * @param state2
	 *            second state
	 * @return state representing the intersection
	 */
	default STATE intersection(final STATE state1, final STATE state2) {
		return null;
	}
	
	/**
	 * Intersection of two states in Buchi automata ("product construction") with a track.
	 * 
	 * @param state1
	 *            first state
	 * @param state2
	 *            second state
	 * @param track
	 *            track
	 * @return state representing the intersection
	 */
	default STATE intersectBuchi(final STATE state1, final STATE state2, final int track) {
		return intersection(state1, state2);
	}
	
	/**
	 * Determinization of several states.
	 * 
	 * @param down2up
	 *            mapping (down state -> up states)
	 * @return state representing the determinization
	 */
	default STATE determinize(final Map<STATE, Set<STATE>> down2up) {
		return null;
	}
	
	/**
	 * @return The sink state.
	 */
	default STATE createSinkStateContent() {
		return null;
	}
	
	/**
	 * @return The empty stack state/symbol.
	 */
	default STATE createEmptyStackState() {
		return null;
	}
	
	/**
	 * State representation of a Petri net marking used for conversion to a finite automaton.
	 * 
	 * @param marking
	 *            Petri net marking
	 * @return state representing the marking
	 */
	default STATE getContentOnPetriNet2FiniteAutomaton(
			final Marking<?, STATE> marking) {
		return null;
	}
	
	/**
	 * Concurrent product construction of two states.
	 * 
	 * @param content1
	 *            first content
	 * @param content2
	 *            second content
	 * @return state representing the concurrent product
	 */
	default STATE getContentOnConcurrentProduct(final STATE content1, final STATE content2) {
		return intersection(content1, content2);
	}
	
	/**
	 * {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker DoubleDecker} of two states.
	 * 
	 * @param downState
	 *            down state
	 * @param upState
	 *            up state
	 * @return state representing the double decker
	 * @deprecated currently not used
	 */
	@Deprecated
	default STATE createDoubleDeckerContent(final STATE downState, final STATE upState) {
		return null;
	}
	
	/**
	 * State in <tt>SVW</tt> result construction ("TMA") for Buchi automata.
	 * 
	 * @param stateNb
	 *            state number inside the TMA
	 * @param tmaNb
	 *            number of the TMA instance
	 * @return state representing the TMA
	 */
	default STATE constructBuchiSVWState(final Integer stateNb, final Integer tmaNb) {
		return null;
	}
}
