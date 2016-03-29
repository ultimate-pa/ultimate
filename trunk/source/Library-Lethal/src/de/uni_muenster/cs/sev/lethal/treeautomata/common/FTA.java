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
package de.uni_muenster.cs.sev.lethal.treeautomata.common;

import java.util.Set;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;



/**
 * Represents a finite tree automaton with state type Q, symbol type F and rule type R.<br>
 * According to the definition of finite tree automaton it consists of an alphabet,
 * a set of states, a set of final states and a set of rules, where the final states are
 * a subset of the set of states and each symbol of the alphabet has a non-negative arity. 
 * The rules have the form f(q1,...,qn)->q, where q1,...,qn, q are states and f is a symbol 
 * of the alphabet with arity n. <br>
 * With these rules in a run of the tree automaton, recursively subtrees like f(q1,...,qn) are
 * annotated by q, until no rule can be applied or until the root symbol is annotated. 
 * If the state annotating the rule symbol is a final state, 
 * we say that the finite tree automaton accepts or recognizes the tree.<br>
 * <br>
 * Invariants:<br>
 * <ul>
 * <li> States in the rules are also contained in "states". </li>
 * <li> "finalStates" is a subset of "states". </li>
 * <li> The symbols in the rules are also contained in "alphabet".</li>
 * </ul>
 * 
 * @param <Q> state type of this finite tree automaton
 * @param <F> symbol type of the alphabet of this finite tree automaton
 * @param <R> rule type of this finite tree automaton
 * 
 * @author Dorothea, Irene, Martin
 */
public interface FTA<F extends RankedSymbol, Q extends State, R extends FTARule<F,Q>> {


	/**
	 * Returns the states of this finite tree automaton, that is at least all states which
	 * occur in a rule and the final states of this finite tree automaton.
	 * 
	 * @return the states of this finite tree automaton
	 */
	public Set<Q> getStates();

	/**
	 * Returns the final states of this finite tree automaton.<br>
	 * The final states are exactly the states, in which the tree automaton
	 * accepts a tree after a run.
	 * 
	 * @return the final states of this finite tree automaton.
	 */
	public Set<Q> getFinalStates();


	/**
	 * Returns the rules of this finite tree automaton. <br>
	 * Rules are needed to annotate trees by states in a run.
	 * 
	 * @return the rules of this finite tree automaton
	 */
	public Set<? extends R> getRules();


	/**
	 * Returns all rules which have the given symbol as symbol.
	 * 
	 * @param f symbol which the rules shall be found for
	 * @return all rules r with unsing the given symbol.
	 */
	public Set<? extends R> getSymbolRules(F f); 

	/**
	 * Returns the alphabet of this finite tree automaton. This is at least
	 * all symbols which occur in a rule of this finite tree automaton. <br>
	 * An automaton is always defined on an alphabet containing ({@link RankedSymbol ranked symbols}). 
	 * Trees are only accepted if they are defined over the same alphabet. <br>
	 * If the complement is constructed, this is done with respect to this alphabet,
	 * with respect to all possible trees over this alphabet, respectively. 
	 * 
	 * @return the alphabet of this finite tree automaton
	 */
	public Set<F> getAlphabet();

}
