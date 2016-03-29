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
 * Encapsulates a tree automaton rule f(q1,...,qn) -> q by storing the
 * relevant data (read-only): the symbol f, the states q1,...,qn which the subterms of
 * a term t have to be annotated with, such that the rule can be applied to
 * t, and the state q which t can be annotated with if it satisfies the
 * precondition. <br>
 * 
 * Invariants: <br>
 * <ul>
 * <li> Symbol is not null. </li>
 * <li> Length of srcStates must be the arity of the symbol. </li>
 * </ul>
 * 
 * @param <Q> state type occurring in this rule
 * @param <F> symbol type occurring in this rule
 * 
 * @author Dorothea, Irene, Martin
 */
public interface FTARule<F extends RankedSymbol, Q extends State> {

	/**
	 * Returns the symbol of the rule.
	 * @return symbol of the rule
	 */
	public F getSymbol();

	/**
	 * Returns the source states of the rule.
	 * @return source states of the rule
	 */
	public List<Q> getSrcStates();

	/**
	 * Returns the destination state of the rule.
	 * @return destination state of the rule
	 */
	public Q getDestState();

}
