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
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

/**
 * Part of a {@link NestedWordAutomaton}'s configuration. <tt>up</tt> is the state in which the automaton is.
 * <tt>down</tt> is the state before the last call transition that the automaton has taken.
 * <p>
 * For many algorithms (e.g. determinization) we do not have to use configurations (current state + stack) of the
 * automaton, the {@link DoubleDecker}s are sufficient.<br>
 * In "JACM2009 - Alur,Madhusudan - Adding nesting structure to words" a
 * {@link DoubleDecker} is called "summary state", but to avoid clashes in variable names I decided to use this name.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <STATE>
 *            state type
 */
public class DoubleDecker<STATE> {
	private final STATE mDown;
	private final STATE mUp;
	private final int mHashCode;
	
	/**
	 * Constructor.
	 * 
	 * @param downState
	 *            down state (current hierarchical state)
	 * @param upState
	 *            up state (current linear state)
	 */
	public DoubleDecker(final STATE downState, final STATE upState) {
		mDown = downState;
		mUp = upState;
		mHashCode = computeHashCode(mDown, mUp);
	}
	
	private int computeHashCode(final STATE downState, final STATE upState) {
		final int prime1 = 3;
		final int prime2 = 5;
		return prime1 * downState.hashCode() + prime2 * upState.hashCode();
	}
	
	public STATE getDown() {
		return mDown;
	}
	
	public STATE getUp() {
		return mUp;
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final DoubleDecker<STATE> other = (DoubleDecker<STATE>) obj;
		return mUp.equals(other.mUp) && mDown.equals(other.mDown);
	}
	
	@Override
	public int hashCode() {
		return mHashCode;
	}
	
	@Override
	public String toString() {
		return "Basement: " + mDown + "  Upstairs: " + mUp;
	}
}
