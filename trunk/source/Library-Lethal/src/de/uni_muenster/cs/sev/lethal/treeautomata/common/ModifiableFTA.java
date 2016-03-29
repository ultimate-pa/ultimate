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

import java.util.List;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;

/**
 * Base type for all finite tree automata, which can be modified in a certain way. In particular,
 * states and symbols can be added and final states and rules can be added and removed.
 *
 * @param <F> symbol type of the alphabet of this finite tree automaton
 * @param <Q> state type of this finite tree automaton
 * @param <R> rule type of this finite tree automaton
 * 
 * @author Dorothea, Irene, Martin 
 */
public interface ModifiableFTA<F extends RankedSymbol, Q extends State, R extends FTARule<F,Q>> extends FTA<F,Q,R> {

	/**
	 * Adds a state to the final states.
	 *
	 * @param state state to be made final
	 */
	public void addToFinals(Q state);
	
	
	/**
	 * Removes a state from this finite tree automaton, if it is contained and
	 * one of the following conditions is satisfied:
	 * <ul>
	 * <li> There is no rule containing the specified state and the given flag is not set.</li>
	 * <li> there is a rule containing the specified state and the given flag is set.</li>
	 * </ul>
	 * In the second case, all rules containing the specified state are also deleted. 
	 * @param state state to be removed
	 * @param cascade flag to indicate whether the rules which contain the specified state are 
	 * also to be deleted. 
	 */
	public void removeState(Q state, boolean cascade);
	
	
	/**
	 * Removes a symbol from this finite tree automaton, if it is contained and 
	 * one of the following conditions is
	 * satisfied:
	 * <ul>
	 * <li> There is no rule containing the specified symbol and</li>
	 * <li> there is a rule containing the specified symbol and the given flag is set.</li>
	 * </ul>
	 * In the second case, all rules containing the specified state are also deleted. 
	 * @param symbol state to be removed
	 * @param cascade flag to indicate whether the rules which contain the specified symbol are 
	 * also to be deleted. 
	 */
	public void removeSymbol(F symbol, boolean cascade);
	
	
	/**
	 * Removes a state from the final states.
	 * @param state state to be removed from the final state
	 */
	public void removeFromFinals(Q state);

	/**
	 * Removes a rule from this automaton. <br>
	 * If the states occurring in the rule are not used any longer,
	 * they are also removed.
	 * 
	 * @param rule rule to be removed
	 * @return whether the rule was contained in {@link de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTA#rules}
	 */
	public boolean removeRule(FTARule<F,Q> rule);

	/**
	 * Adds a state to this finite tree automaton.
	 *
	 * @param state state to be added
	 */
	public void addState(Q state);

	/**
	 * Adds a symbol to finite tree automaton
	 *
	 * @param f symbol to be added
	 */
	public void addSymbol(F f);

	/**
	 * Adds a rule to this finite tree automaton and preserves the 
	 * corresponding invariants.<br>
	 * So each state occurring in the rules is also contained in the {@link #getStates() states}.
	 *
	 * @param f symbol of rule to be added
	 * @param srcStates source states of rule to be added
	 * @param destState destination state of rule to be added
	 */
	public void addRule(F f, List<Q> srcStates, Q destState);
	
	
	/**
	 * Adds an epsilon rule to this finite tree automaton. The effect of this method
	 * is that afterwards the finite tree automaton is equivalent to a finite tree
	 * automaton having the additional epsilon rule. That means, that the epsilon rule
	 * must be eliminated before the next call of getStates(), getRules() or getFinalStates().
	 * @param qsrc source state of the epsilon rule to be added
	 * @param qdest destination state of the epsilon rule to be added
	 */
	public void addEpsilonRule(Q qsrc, Q qdest);
}
