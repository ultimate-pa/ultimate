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
package de.uni_muenster.cs.sev.lethal.treeautomata.generic;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;

/**
 * A standard implementation of the FTARule with generic type parameters
 * for the states and symbols.
 * 
 * @param <Q> state type of the rule
 * @param <F> symbol type of the rule
 * 
 * @see FTARule
 * 
 * @author Dorothea, Irene, Martin
 */
public class GenFTARule<F extends RankedSymbol, Q extends State> implements FTARule<F,Q> {

	/**
	 * The symbol f of the rule f(q1,...,qn)->q
	 */
	private final F symbol;

	/**
	 * List of source states necessary to apply this rule like q1,..,qn
	 * for the rule f(q1,...,qn)->q.
	 */
	private final List<Q> srcStates;

	/**
	 * State which a term can be reduced to by applying this rule. <br>
	 * It is on the right side of the rule like q for the rule f(q1,...,qn)->q.
	 */
	private final Q destState;

	/**
	 * Hash code of this rule: Since a rule must not be changed, 
	 * it can be calculated once.
	 */
	private int hashcode;

	
	/***
	 * Constructs a rule from the given symbol, source states and destination state.
	 * 
	 * @param symbol symbol of the rule 
	 * @param srcStates source states of the rule
	 * @param destState destination state of the rule
	 */
	public GenFTARule(F symbol, List<Q> srcStates, Q destState) {
		//preserve invariants
		if (symbol == null) throw new IllegalArgumentException("GenFTARule(): symbol must not be null.");
		if (srcStates == null) throw new IllegalArgumentException("GenFTARule(): srcStates must not be null.");
			
		if (symbol.getArity() != srcStates.size()) throw new IllegalArgumentException("GenFTARule(): Length of srcStates must be the arity of the symbol.");
		for (State s: srcStates){
			if (s==null) throw new IllegalArgumentException("GenFTARule(): States must not be null.");
		}
		if (destState == null) throw new IllegalArgumentException("GenFTARule(): destState must not be null.");

		this.symbol = symbol;
		this.srcStates = new ArrayList<Q>(srcStates);
		this.destState = destState;
		this.hashcode = calcHashCode();
	}


	/**
	 * Returns the symbol of the rule.
	 * 
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule#getSymbol()
	 */
	public F getSymbol() {
		return symbol;
	}


	/**
	 * Returns the source states of the rule.
	 * 
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule#getSrcStates()
	 */
	public List<Q> getSrcStates() {
		return Collections.<Q>unmodifiableList(srcStates);
	}


	/**
	 * Returns the destination state of the rule.
	 * 
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule#getDestState()
	 */
	public Q getDestState() {
		return destState;
	}


	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString(){
		StringBuffer buffer = new StringBuffer();
		buffer.append(this.symbol.toString());
		if (this.srcStates.size() != 0){
			buffer.append('(');
			boolean first = true;
			for (State state : srcStates){
				if (!first) buffer.append(',');
				buffer.append(state.toString());
				first = false;
			}
			buffer.append(')');
		}
		buffer.append(" -> ");
		buffer.append(this.destState.toString());
		return buffer.toString();
	}

	/**
	 * Calculate the hash code once.
	 * 
	 * @return hash code
	 */
	private int calcHashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
		+ ((destState == null) ? 0 : destState.hashCode());
		result = prime * result
		+ ((srcStates == null) ? 0 : srcStates.hashCode());
		result = prime * result
		+ ((symbol == null) ? 0 : symbol.hashCode());
		return result;
	}


	/**
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		return hashcode;
	}


	/**
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	@SuppressWarnings("unchecked")
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (!(obj instanceof GenFTARule))
			return false;
		final GenFTARule other = (GenFTARule) obj;
		if (destState == null) {
			if (other.destState != null)
				return false;
		} else if (!destState.equals(other.destState))
			return false;
		if (srcStates == null) {
			if (other.srcStates != null)
				return false;
		} else if (!srcStates.equals(other.srcStates))
			return false;
		if (symbol == null) {
			if (other.symbol != null)
				return false;
		} else if (!symbol.equals(other.symbol))
			return false;
		return true;
	}

}
