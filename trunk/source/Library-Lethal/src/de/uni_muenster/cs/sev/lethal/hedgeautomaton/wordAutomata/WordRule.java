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
package de.uni_muenster.cs.sev.lethal.hedgeautomaton.wordAutomata;

import de.uni_muenster.cs.sev.lethal.hedgeautomaton.internal.HedgeStateCache;
import de.uni_muenster.cs.sev.lethal.states.HedgeState;
import de.uni_muenster.cs.sev.lethal.states.State;

/**
 * An implementation of the rule for the word automaton.
 *
 * @author Anton, Maria
 * @param <G_State> type of states occurring as symbols in word automaton
 */
public class WordRule<G_State extends State> {
	/**
	 * The symbol of the rule.
	 */
	private final HedgeState<G_State> symbol;

	/**
	 * The start state of the rule.
	 */
	private final HedgeState<G_State> sourceState;
	/**
	 * State in which passes the word automaton, by applying of this rule.
	 */
	private final HedgeState<G_State> destState;

	/**
	 * Constructs a rule with the given data.
	 *
	 * @param symbol			the symbol of the rule
	 * @param sourceState the start state of the rule
	 * @param destState	 state in which passes the word automaton, by applying of this rule
	 */
	public WordRule(final G_State symbol, final G_State sourceState, final G_State destState) {
		super();
		this.symbol = HedgeStateCache.getState(symbol);
		this.sourceState = HedgeStateCache.getState(sourceState);
		this.destState = HedgeStateCache.getState(destState);
	}

	/**
	 * Returns the symbol of the rule.
	 * 
	 * @return the symbol of the rule
	 */
	HedgeState<G_State> getHSymbol() {
		return this.symbol;
	}

	/**
	 * Returns the start state of the rule.
	 * 
	 * @return the start state of the rule
	 */
	HedgeState<G_State> getHSourceState() {
		return this.sourceState;
	}

	/**
	 * Returns destination state of the rule.
	 * 
	 * @return state in which passes the wordautomaton, by applying of this rule
	 */
	HedgeState<G_State> getHDestState() {
		return this.destState;
	}

	/**
	 * Returns symbol of the word rule.
	 *
	 * @return symbol of the word rule
	 */
	public G_State getSymbol() {
		return symbol.getOriginal();
	}

	/**
	 * Returns source state of the word rule.
	 *
	 * @return source state of the word rule
	 */
	public G_State getSourceState() {
		return sourceState.getOriginal();
	}

	/**
	 * Returns destination state of the word rule.
	 *
	 * @return destination state of the word rule
	 */
	public G_State getDestState() {
		return destState.getOriginal();
	}

	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "WordRule{" +
				this.symbol +
				"(" + this.sourceState +
				")->" + this.destState +
				'}';
	}
}
