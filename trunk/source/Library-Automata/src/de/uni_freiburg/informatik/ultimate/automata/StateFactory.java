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
package de.uni_freiburg.informatik.ultimate.automata;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.LevelRankingState;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.Condition;

/**
 * Abstract factory for states used in typical automata operations.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <STATE>
 *            state type
 */
public abstract class StateFactory<STATE> {
	/**
	 * Intersection of two states ("product construction").
	 * 
	 * @param state1
	 *            first state
	 * @param state2
	 *            second state
	 * @return state representing the intersection
	 */
	public STATE intersection(final STATE state1, final STATE state2) {
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
	public STATE intersectBuchi(final STATE state1, final STATE state2, final int track) {
		return intersection(state1, state2);
	}
	
	/**
	 * Determinization of several states.
	 * 
	 * @param down2up
	 *            mapping (down state -> up states)
	 * @return state representing the determinization
	 */
	public STATE determinize(final Map<STATE, Set<STATE>> down2up) {
		return null;
	}
	
	/**
	 * @return The sink state.
	 */
	public STATE createSinkStateContent() {
		return null;
	}
	
	/**
	 * @return The empty stack state/symbol.
	 */
	public STATE createEmptyStackState() {
		return null;
	}
	
	/**
	 * State representation of a Petri net marking used for conversion to a finite automaton.
	 * 
	 * @param marking
	 *            Petri net marking
	 * @return state representing the marking
	 */
	public STATE getContentOnPetriNet2FiniteAutomaton(
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
	public STATE getContentOnConcurrentProduct(final STATE content1, final STATE content2) {
		return intersection(content1, content2);
	}
	
	/**
	 * White content for "black and white" construction.
	 * 
	 * @param content
	 *            content
	 * @return state representing the white content
	 */
	public STATE getWhiteContent(final STATE content) {
		return content;
	}
	
	/**
	 * Black content for "black and white" construction.
	 * 
	 * @param content
	 *            content
	 * @return state representing the black content
	 */
	public STATE getBlackContent(final STATE content) {
		return content;
	}
	
	/**
	 * Complement state in <tt>FKV</tt> construction for Buchi automata.
	 * 
	 * @param complementState
	 *            complement state
	 * @return state representing the state in the complement automaton
	 */
	public STATE buchiComplementFKV(final LevelRankingState<?, STATE> complementState) {
		return null;
	}
	
	/**
	 * Complement state in <tt>NCSB</tt> construction for Buchi automata.
	 * 
	 * @param complementState
	 *            complement state
	 * @return state representing the state in the complement automaton
	 */
	public STATE buchiComplementNCSB(final LevelRankingState<?, STATE> complementState) {
		return null;
	}
	
	/**
	 * Complement state in construction for deterministic Buchi automata.
	 * 
	 * @param state
	 *            non-final state
	 * @return state representing the state in the complement automaton
	 */
	public STATE complementBuchiDeterministicNonFinal(final STATE state) {
		return null;
	}
	
	/**
	 * Complement state in construction for deterministic Buchi automata.
	 * 
	 * @param state
	 *            final state
	 * @return state representing the state in the complement automaton
	 */
	public STATE complementBuchiDeterministicFinal(final STATE state) {
		return null;
	}
	
	/**
	 * Minimization ("merging") of several states.
	 * 
	 * @param states
	 *            states
	 * @return state representing the minimization
	 */
	public STATE minimize(final Collection<STATE> states) {
		return null;
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
	public STATE createDoubleDeckerContent(final STATE downState, final STATE upState) {
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
	public STATE constructBuchiSVWState(final Integer stateNb, final Integer tmaNb) {
		return null;
	}
	
	/**
	 * {@link de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.FinitePrefix2PetriNet FinitePrefix2PetriNet}
	 * construction of a condition.
	 * 
	 * @param condition
	 *            condition
	 * @return state representing the condition
	 */
	public STATE finitePrefix2net(final Condition<?, STATE> condition) {
		return null;
	}
	
	/**
	 * State in {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.senwa.Senwa Senwa}.
	 * 
	 * @param entry
	 *            entry
	 * @param state
	 *            state
	 * @return state representing a Senwa state
	 */
	public STATE senwa(final STATE entry, final STATE state) {
		return null;
	}
}
