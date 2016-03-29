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

import de.uni_muenster.cs.sev.lethal.factories.StateFactory;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.*;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.internal.*;
import de.uni_muenster.cs.sev.lethal.states.HedgeState;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.special.HedgeSymbol;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTARule;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;


/**
 * An implementation of the word automaton to be used as regular language in the hedge automaton.
 *
 * @author Anton, Maria
 * @param <G_State> type of states occurring in regular language
 * @param <G_Symbol> type of symbols occurring in corresponding{@link HedgeRule rule}
 */
public class WordAutomaton<G_Symbol extends UnrankedSymbol, G_State extends State> implements RegularLanguage<G_Symbol, G_State> {
	/**
	 * the set of states
	 */
	private final Set<G_State> states;
	/**
	 * the set of rules
	 */
	private final Set<WordRule<G_State>> rules;
	/**
	 * the initial state
	 */
	private final G_State startState;
	/**
	 * the set of the final states
	 */
	private final Set<G_State> finalStates;

	/**
	 * Constructs an word automaton with the given data.
	 *
	 * @param states			the set of states
	 * @param rules			 the set of rules
	 * @param startState	the initial state
	 * @param finalStates the set of the final states
	 */
	public WordAutomaton(final Set<G_State> states, final Set<WordRule<G_State>> rules, final G_State startState, final Set<G_State> finalStates) {
		super();
		this.states = states;
		this.rules = rules;
		this.startState = startState;
		this.finalStates = finalStates;
	}

	/**
	 * Returns the set of states of this word automaton.
	 * 
	 * @return the set of states of the word automaton
	 */
	public Set<G_State> getStates() {
		return this.states;
	}

	/**
	 * Returns the set of rules of this word automaton.
	 * 
	 * @return the set of rules of the word automaton
	 */
	public Set<WordRule<G_State>> getRules() {
		return this.rules;
	}

	/**
	 * @return the initial state of the word automaton
	 */
	public G_State getStartState() {
		return this.startState;
	}

	/**
	 * Returns the set of final states of this word automaton.
	 * 
	 * @return the set of the final states of the word automaton
	 */
	public Set<G_State> getFinalStates() {
		return this.finalStates;
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.hedgeautomaton.RegularLanguage#getInitializer()
	 */
	@Override
	public Init<G_Symbol, G_State> getInitializer() {
		return null;
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.hedgeautomaton.RegularLanguage#getFinaliser()
	 */
	@Override
	public Finit<G_Symbol, G_State> getFinaliser() {
		return null;
	}

	/**
	 * Transforms the Expression into a FiniteTreeAutomaton
	 *
	 * @param start State to start from
	 * @param ha		HedgeAutomaton this rule is from
	 * @param sF		StateFactory for creating states
	 * @return transformed Expression
	 */
	@Override
	public Container<G_Symbol, G_State> transform(final HedgeState<G_State> start, final HedgeAutomaton<G_Symbol, G_State> ha, final StateFactory sF) {
		final Set<GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>> consRules = new HashSet<GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>>();
		//final HashSet<HedgeState<G_State>> states = new HashSet<HedgeState<G_State>>();
		final HedgeState<G_State> startState = HedgeStateCache.getState(this.startState);
		for (final WordRule<G_State> rule : this.rules) {
			final List<HedgeState<G_State>> srcStates = new LinkedList<HedgeState<G_State>>();
			HedgeState<G_State> temp = rule.getHSourceState();
			if (temp.equals(startState)) temp = start;
			//states.add(temp);
			srcStates.add(temp);
			temp = rule.getHSymbol();
			if (temp.equals(startState)) temp = start;
			//states.add(temp);
			srcStates.add(temp);
			temp = rule.getHDestState();
			if (temp.equals(startState)) temp = start;
			//states.add(temp);
			consRules.add(new GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>(HedgeSymbolCache.getConsSymbol(ha), srcStates, temp));
		}
		final HashSet<HedgeState<G_State>> finStates = new HashSet<HedgeState<G_State>>();
		for (final G_State st : this.finalStates) {
			if (st.equals(this.startState))
				finStates.add(start);
			else
				finStates.add(HedgeStateCache.getState(st));
		}
		return new Container<G_Symbol, G_State>(consRules, finStates);
	}

	/**
	 * Returns whether this expression is empty.
	 *
	 * @return whether this expression is empty
	 */
	@Override
	public boolean isEmpty() {
		return false;
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.hedgeautomaton.RegularLanguage#acceptsEmptyWord()
	 */
	@Override
	public boolean acceptsEmptyWord() {
		return finalStates.contains(this.startState);
	}

	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "WordAutomaton{" +
				"states=" + this.states +
				", rules=" + this.rules +
				", startState=" + this.startState +
				", finalStates=" + this.finalStates +
				'}';
	}
}
