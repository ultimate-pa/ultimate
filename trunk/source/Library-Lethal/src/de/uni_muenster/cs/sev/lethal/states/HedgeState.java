/*
 * Copyright 2009 Dorothea Jansen <d.jansen@uni-muenster.de>, Martin Mohr <mohrfrosch@uni-muenster.de>, Irene Thesing <i_thes01@uni-muenster.de>, Anton Reis <antonreis@gmx.de>, Maria Schatz <m_scha17@uni-muenster.de>, Philipp Claves <philipp.claves@uni-muenster.de>, Sezar Jarrous <sezar.jarrous@gmail.com>
 *
 * This file is part of LETHAL.
 *
 * LETHAL is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * LETHAL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with LETHAL.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_muenster.cs.sev.lethal.states;


import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

/**
 * Special state to be used in transformed trees.
 * Needed to treat user states and generated one equally.
 * Usually: user state XOR generated state (similar to the BiState).
 *
 * @param <G_State> state type
 * 
 * @author Anton, Maria
 */
public class HedgeState<G_State extends State> implements State {

	/**
	 * Generated state.
	 */
	private final State i;


	/**
	 * User state.
	 */
	private final G_State s;


	/**
	 * Puts the nil symbol in.
	 *
	 * @param user the user state
	 * @param gen	the generated state
	 */
	public HedgeState(final G_State user, final State gen) {
		super();
		this.i = gen;
		this.s = user;
	}


	/**
	 * Getter for the user symbol.
	 *
	 * @return the contained user symbol
	 */
	public G_State getOriginal() {
		if (this.s == null) throw new IllegalAccessError(
		"Tried to unpack a hedge symbol without packed symbol in it.");
		return this.s;
	}


	/**
	 * Getter for the generated state.
	 *
	 * @return the generated state
	 */
	public State getGenerated() {
		if (this.i == null) throw new IllegalAccessError(
		"Tried to get generated symbol, but packed symbol found.");
		return this.i;
	}


	/**
	 * Checks whether its the user symbol.
	 *
	 * @return whether its the user symbol
	 */
	public boolean isPacked() {
		return this.s != null;
	}


	/**
	 * Compares this state to given object.
	 *
	 * @param state the object to compare with this state
	 * @return whether the given object is equal with this state
	 */
	@Override
	public boolean equals(final Object state) {
		if (state == null) return false;
		if (state == this) return true;
		if (state instanceof HedgeState<?>) {
			final HedgeState<?> h_state = (HedgeState<?>) state;
			if (this.isPacked())
				return (h_state.isPacked() && this.getOriginal().equals(h_state.getOriginal()));
			else
				return (!h_state.isPacked() && this.getGenerated().equals(h_state.getGenerated()));
		} else
			return false;
	}


	/**
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		int result = i != null ? i.hashCode() : 0;
		result = 31 * result + (s != null ? s.hashCode() : 0);
		return result;
	}


	/**
	 * Extracts all packed states.
	 *
	 * @param set hedgeStates to extract packed states from
	 * @param <G_State> type of the packed states
	 * @return list of extracted states
	 */
	public static <G_State extends State> List<G_State> extractOriginal(final Iterable<HedgeState<G_State>> set) {
		final List<G_State> ret = new LinkedList<G_State>();
		for (final HedgeState<G_State> s : set)
			if (s.isPacked())
				ret.add(s.getOriginal());
		return ret;
	}


	/**
	 * Transforms a state which is named with a set of hedge states of a type G_State of states
	 * into a state which is named with a set of states of type G_State.
	 *
	 * @param <G_State> type of states
	 * @param set given named state which shall be transformed.
	 * @return state which is named with a set of states of type G_State
	 */
	public static <G_State extends State> NamedState<Set<G_State>> transform(final NamedState<Set<HedgeState<G_State>>> set) {
		final Set<G_State> ret_set = new HashSet<G_State>();
		for (final HedgeState<G_State> s : set.getName())
			ret_set.add(s.getOriginal());
		return new NamedState<Set<G_State>>(ret_set);
	}


	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "h<" + ((this.i != null) ? this.i.toString() : this.s.toString()) + ">";
	}
}
