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
/**
 * 
 */
package de.uni_muenster.cs.sev.lethal.treetransducer;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.Variable;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;

/**
 * Encapsulates a state of a certain type and a variable tree used for the right
 * side of the rules of a tree transducer. <br>
 * Helper class for {@link GenTT tree transducers} implementing {@link de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA finite tree 
 * automata}.
 * 
 * @author Irene
 *
 * @param <Q> original state type
 * @param <G> type of symbols in the contained variable tree
 */
public class TTState<Q extends State, G extends RankedSymbol> implements State{

	/** Encapsulated state of the right side of a rule.*/
	protected Q state;

	/** Tree with variables of the right side of a rule.*/
	protected Tree<BiSymbol<G,Variable>> varTree;


	/**
	 * Creates a new state with the given state and an empty variable tree.
	 * 
	 * @param q state that shall be encapsulated
	 */
	public TTState(Q q){
		if (q == null) throw new IllegalArgumentException("TTState(): q must not be null");
		state = q;
		varTree = null;
	}


	/**
	 * Returns the contained variable tree.
	 * 
	 * @return the contained variable tree
	 */
	public Tree<BiSymbol<G,Variable>> getVarTree() {
		return varTree;
	}


	/**
	 * Sets the variable tree in this state.
	 * 
	 * @param varTree the value the contained variable tree is to be set to
	 */
	public void setVarTree(Tree<BiSymbol<G,Variable>> varTree) {
		this.varTree = varTree;
	}


	/**
	 * Returns the contained state.
	 * 
	 * @return the contained state
	 */
	public Q getState() {
		return state;
	}



	/**
	 * Creates a new state with the given state and the given variable tree as content.
	 * 
	 * @param q state that is to be encapsulated
	 * @param tree tree with variables
	 */
	public TTState(Q q,Tree<BiSymbol<G,Variable>> tree){
		state = q;
		varTree = tree;
	}


	/**
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		return state.hashCode();
	}

	/**
	 * Two TTStates are equal, if they contain the same state.
	 * 
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		final TTState<?,?> other = (TTState<?,?>) obj;
		if (state == null) {
			if (other.state != null)
				return false;
		} else if (!state.equals(other.state))
			return false;
		return true;
	}

	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString(){
		return "("+state+","+varTree+")";
	}
}
