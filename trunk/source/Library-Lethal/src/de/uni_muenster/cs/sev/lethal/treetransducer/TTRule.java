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

import java.util.LinkedList;
import java.util.List;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.Variable;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;


/**
 * Represents a rule for a tree transducer, which has the form
 * f(q1,...qn) -> (q,u), where f is a ranked symbol, q1, ...,qn,q are states 
 * and u is a variable tree with at most n different variables.<br>
 * Note, that if f(q1,...qn)->(q,u) and f(q1,...qn)->(q,v) are two rules, than
 * u and v must be equal. Otherwise it works not in the right way. 
 * For realizing something like this, add one state and
 * an epsilon rule: f(q1,...qn)->(q,u), f(q1,...qn)->(p,v) and p -> q.
 * 
 * @param <F> type of symbols of the start alphabet
 * @param <G> type of symbols of the destination alphabet
 * @param <Q> type of used states
 * 
 * @see EasyTT
 * @see TTEpsRule
 * @see TTRuleSet
 * 
 * @author Dorothea, Irene, Martin
 */
public class TTRule<F extends RankedSymbol, G extends RankedSymbol, Q extends State> implements FTARule<F,TTState<Q,G>>{

	/** Symbol of the rule. */
	protected F symbol;
	
	/** List of source states of the rule. */
	protected List<TTState<Q,G>> srcStates;
	
	/** Destination state of the rule. */
	protected TTState<Q,G> destState;
	
	/** destination tree of the rule with one variable
	 * @see Variable
	 */
	// protected Tree<BiSymbol<G,Variable>> destTree;


	/**
	 * Constructs a new TTRule of the form f(q1,...qn) -> (q,u), 
	 * where f is a ranked symbol, q1,...,qn, q are states and u is a 
	 * variable tree with at most n different variables.
	 * 
	 * @param s symbol of the rule
	 * @param src list of source states of the rule
	 * @param q destination state of the rule
	 * @param tree destination tree of the rule, that is a variable tree with at most n different variables, 
	 * that means the highest number of a variable is arity(s)-1.
	 */
	public TTRule(F s, List<Q> src, Q q, Tree<BiSymbol<G,Variable>> tree){
		if (s == null || src == null || q == null || tree == null) throw new IllegalArgumentException("TTRule(): One of the parameters is null.");
		if (src.size() != s.getArity()){
			throw new IllegalArgumentException("Arity and length of the src states must fit to each other.");
		}
		symbol = s;
		srcStates = new LinkedList<TTState<Q,G>>();
		for (Q p: src){
			if (p == null) throw new IllegalArgumentException("TTRule(): One of the source states is null.");
			srcStates.add(new TTState<Q,G>(p));
		}
		// destTree = tree;
		destState = new TTState<Q,G>(q,tree);
	}
	
	/**
	 * Constructs a new TTRule in the form f(q1,...qn) -> (q,u), 
	 * where f is a ranked symbol, q1,...,qn, q are states and u is a 
	 * variable tree with at most n different variables.
	 * 
	 * @param s function symbol of the rule
	 * @param src list of source states of the rule
	 * @param dest destination state and tree in {@link TTState} of the rule
	 * means the highest number of a variable is arity(s)-1.
	 */
	public TTRule(F s, List<TTState<Q,G>> src, TTState<Q,G> dest){
		if (s == null || src == null || dest == null) throw new IllegalArgumentException("TTRule(): One of the parameters is null.");
		if (dest.getVarTree() == null) throw new IllegalArgumentException("The destination state must contain a variable tree.");
		if (src.size() != s.getArity()){
			throw new IllegalArgumentException("Arity and length of the src states must fit to each other.");
		}
		symbol = s;
		srcStates = src;
		// destTree = tree;
		destState = dest;
	}

	
	/**
	 * Returns the destination state of the rule, i.e.
	 * the state on the right side of the rule.
	 * 
	 * @return destination state of the rule
	 */
	public Q getDestStateAsQ() {
		return destState.getState();
	}

	/**
	 * Returns the destination state of the rule, i.e.
	 * the state on the right side of the rule.
	 * 
	 * @return destination state of the rule
	 */
	public TTState<Q,G> getDestState() {
		return destState;
	}

	/**
	 * Returns the destination tree, i.e. the variable
	 * tree on the right side of the rule.
	 * 
	 * @return destination tree of the rule
	 */
	public Tree<BiSymbol<G,Variable>> getDestTree() {
		return destState.getVarTree();
	}

	/**
	 * Returns the source states, i.e. the list of states
	 * on the left side of the rule, needed for applying the rule.
	 * 
	 * @return source states of the rule
	 */
	public List<TTState<Q,G>> getSrcStates() {
		return srcStates;
	}
	
	/**
	 * Returns the source states, i.e. the list of states
	 * on the left side of the rule, needed for applying the rule.
	 * 
	 * @return source states of the rule
	 */
	public List<Q> getSrcStatesAsQ() {
		List<Q> ret = new LinkedList<Q>();
		for (TTState<Q,G> q: srcStates){
			ret.add(q.getState());
		}
		return ret;
	}

	/**
	 * Returns the symbol of the rule, i.e. the ranked symbol
	 * on the left side of the rule, needed for applying the rule.
	 * 
	 * @return symbol of the rule
	 */
	public F getSymbol() {
		return symbol;
	}

	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString(){
		return symbol + srcStates.toString() + " -> " + destState.toString();
	}

	/**
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((destState == null) ? 0 : destState.hashCode());
		result = prime * result
				+ ((srcStates == null) ? 0 : srcStates.hashCode());
		result = prime * result + ((symbol == null) ? 0 : symbol.hashCode());
		return result;
	}

	/**
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
		final TTRule<?,?,?> other = (TTRule<?,?,?>) obj;
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
