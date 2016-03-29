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
package de.uni_muenster.cs.sev.lethal.hedgegrammar;

import de.uni_muenster.cs.sev.lethal.hedgeautomaton.HedgeAutomaton;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.HedgeRule;

import java.util.HashSet;
import java.util.Set;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;

/**
 * 
 * 
 * @author Anton, Maria
 * @param <G_Symbol> symbol type of the hedge grammar
 */
public class HedgeGrammar<G_Symbol extends UnrankedSymbol> {

	private final Set<GrammarRule<G_Symbol>> rules;
	private HedgeAutomaton<G_Symbol, State> ha;
	private final Set<Nonterminal<G_Symbol>> end;

	/**
	 * 
	 */
	public HedgeGrammar() {
		super();
		this.rules = new HashSet<GrammarRule<G_Symbol>>();
		this.ha = null;
		this.end = new HashSet<Nonterminal<G_Symbol>>();
	}

	/**
	 * Creates a new hedge grammar
	 * @param rule rules of the hedge grammar
	 * @param start start symbols of the hedge grammar
	 */
	public HedgeGrammar(Set<GrammarRule<G_Symbol>> rule, Set<Nonterminal<G_Symbol>> start) {
		super();
		this.rules = rule;
		this.ha = null;
		end = start;
	}

	/**
	 * Adds a new rule to the hedge grammar.
	 * @param rule rule to add
	 */
	public void add(GrammarRule<G_Symbol> rule) {
		this.rules.add(rule);
		this.ha = null;
	}

	/**
	 * Adds multiple rules to the hedge grammar.
	 * @param rules rules to add
	 */
	public void addAll(Set<GrammarRule<G_Symbol>> rules) {
		this.rules.addAll(rules);
		this.ha = null;
	}

	/**
	 * Adds a start symbol to the hedge grammar
	 * @param start start symbol
	 */
	public void addStart(Nonterminal<G_Symbol> start) {
		end.add(start);
	}

	/**
	 * Adds multiple start symbols to the hedge grammar
	 * @param start start symbols
	 */
	public void addStartAll(Set<Nonterminal<G_Symbol>> start) {
		end.addAll(start);
	}

	/**
	 * 
	 */
	private void generateAutomaton() {
		Set<HedgeRule<G_Symbol, State>> ha_rules = new HashSet<HedgeRule<G_Symbol, State>>();
		Set<State> ha_states = new HashSet<State>();
		Set<State> ha_finalStates = new HashSet<State>();

		HedgeRule<G_Symbol, State> h_rule;
		for (GrammarRule<G_Symbol> rule : rules) {
			// System.out.println(">"+rule);
			h_rule = new HedgeRule<G_Symbol, State>(rule.getTerminal().getSymbol(),
					rule.getExpression().getRegularExpression(), rule
							.getNonterminal().getStates().iterator().next());
			// System.out.println(">>"+h_rule);
			ha_rules.add(h_rule);
			// System.out.println(">>"+rule.getExpression().getRules());
			ha_rules.addAll(rule.getExpression().getRules());
			ha_states.addAll(rule.getStates());
		}
		for (Nonterminal<G_Symbol> n : end)
			ha_finalStates.addAll(n.getStates());

		ha = constructAutmaton(ha_states, ha_finalStates, ha_rules);
	}
	
	protected HedgeAutomaton<G_Symbol, State> constructAutmaton(Set<State> haStates,Set<State> haFinalStates,Set<HedgeRule<G_Symbol, State>> haRules){
		return new HedgeAutomaton<G_Symbol, State>(haStates, haFinalStates, haRules);
	}

	/**
	 * @return The Hedge Automaton specified by this HedgeGrammar 
	 */
	public HedgeAutomaton<G_Symbol, State> getHA() {
		if (ha == null) generateAutomaton();
		return ha;
	}

	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		String ret = "start nonterminals:" + end + "\n";
		for (GrammarRule<G_Symbol> r : rules) {
			ret += r.toString() + "\n";
		}
		return ret;
	}
}
