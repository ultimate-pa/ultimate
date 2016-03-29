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
package de.uni_muenster.cs.sev.lethal.grammars.generic;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import de.uni_muenster.cs.sev.lethal.grammars.RTG;
import de.uni_muenster.cs.sev.lethal.grammars.RTGRule;
import de.uni_muenster.cs.sev.lethal.states.NamedState;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTACreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTARule;
import de.uni_muenster.cs.sev.lethal.utils.CachedConverter;
import de.uni_muenster.cs.sev.lethal.utils.Pair;

/**
 * Standard implementation of {@link de.uni_muenster.cs.sev.lethal.grammars.RTG}.<br>
 * 
 * @param <F> type of symbols occurring in the rules
 * @param <Q> type of non-terminals occurring in the rules
 * 
 * @author Dorothea, Martin, Sezar , Philipp
 */
public class GenRTG<F extends RankedSymbol, Q extends State> implements RTG<F,Q>, FTA<F,NamedState<Object>, GenFTARule<F,NamedState<Object>>> {

	/**
	 * Start symbols of this regular tree grammar.
	 */
	protected HashSet<Q> startSymbols = new HashSet<Q>();


	/**
	 * Start symbols that have been added since the last time 
	 * the underlying finite tree automaton has been computed.
	 */
	protected LinkedList<Q> unprocessedStartSymbols;


	/**
	 * Rules of this regular tree grammar.
	 */
	protected HashSet<RTGRule<F, Q>> rules = new HashSet<RTGRule<F, Q>>();


	/**
	 * Rules that have been added since the last time 
	 * the underlying finite tree automaton has been computed.
	 */
	protected LinkedList<RTGRule<F, Q>> unprocessedRules = null;


	/**
	 * Equivalent finite tree automaton.
	 */
	protected GenFTA<F,NamedState<Object>> equivFTA = null;


	/**
	 * Indicates whether the grammar has been changed since the last time 
	 * the underlying finite tree automaton has been computed.
	 */
	protected boolean dirtyFTA = true;
	
	/**
	 * Creates a new regular tree grammar with the specified start symbols and rules.
	 * @param start start symbols of the regular tree grammar to be created
	 * @param rules rules of the regular tree grammar to be created
	 */
	public GenRTG(Collection<Q> start, Collection<? extends RTGRule<F,Q>> rules) {
		this.unprocessedStartSymbols = new LinkedList<Q>(start);
		this.startSymbols = new HashSet<Q>(start);
		this.unprocessedRules = new LinkedList<RTGRule<F,Q>>(rules);
		this.rules = new HashSet<RTGRule<F,Q>>(rules);
	}


	/**
	 * Creates a new regular tree grammar with the specified start symbols, but without rules.
	 * @param start start symbols of the regular tree grammar to be created
	 */
	public GenRTG(Collection<Q> start) {
		this.unprocessedStartSymbols = new LinkedList<Q>(start);
		this.startSymbols = new HashSet<Q>(start);
		this.unprocessedRules = null;
		this.rules = new HashSet<RTGRule<F,Q>>();
	}


	/**
	 * Updates the grammar if it has not been initialized before 
	 * or if some start symbols or rules have been added.
	 */
	protected void updateGrammar() {

	}


	/**
	 * Updates the underlying finite tree automaton if it has not been initialized before 
	 * or if some start symbols or rules have been added.
	 * As the grammar has to be up to date if the underlying finite tree automaton is,
	 * the grammar also has to be updated.
	 */
	protected void updateFTA() {
		
		final String prefix = "G(";
		final String suffix = ")";
		
		CachedConverter<Object, NamedState<Object>> stateConv = new CachedConverter<Object, NamedState<Object>>() {
			@Override
			public NamedState<Object> uniqueConvert(final Object a) {
				return new NamedState<Object>(a) {
					@Override
					public String toString() {
						return prefix+a.toString()+suffix;
					}
				};
			}

		};
		
		if (unprocessedStartSymbols == null) unprocessedStartSymbols = new LinkedList<Q>(); //initialize the unprocessed symbols list we need it now.
		if (unprocessedRules        == null) unprocessedRules = new LinkedList<RTGRule<F, Q>>(); //initialize the unprocessed rules list we need it now.
		
		if (equivFTA == null) {
			// underlying finite tree automaton has never been computed before
			equivFTA = new GenFTA<F,NamedState<Object>>(this, stateConv);
		} else {
			// underlying finite tree automaton has to be changed
			Pair<Collection<FTARule<F, NamedState<Object>>>, Collection<NamedState<Object>>> helpPair 
					= FTACreator.makeFTAFromGrammar(unprocessedStartSymbols, unprocessedRules, stateConv);
			for (FTARule<F, NamedState<Object>> rule : helpPair.getFirst()) {
				equivFTA.addRule(rule.getSymbol(),rule.getSrcStates(),rule.getDestState());
			}
			for(NamedState<Object> state : helpPair.getSecond()){
				equivFTA.addToFinals(state);
			}
		}
		// the finite tree automaton has been updated
		dirtyFTA = false;
		
		// clear the unprocessed rules and start symbols lists, we have added their content to the automaton.
		unprocessedRules.clear();
		unprocessedStartSymbols.clear();
	}
	
	
	/**
	 * @see de.uni_muenster.cs.sev.lethal.grammars.RTG#getGrammarRules()
	 */
	public Set<RTGRule<F, Q>> getGrammarRules() {
		return rules;
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.grammars.RTG#getStartSymbols()
	 */
	public Set<Q> getStartSymbols() {
		return startSymbols;
	}


	/**
	 * Adds a rule to this regular tree grammar.
	 * @param left left side of the rule to be added
	 * @param right right side of the rule to be added
	 */
	public void addRule(Q left, Tree<BiSymbol<F,Q>> right) {
		GenRTGRule<F,Q> newRule = new GenRTGRule<F,Q>(left,right);
		if(unprocessedRules == null) unprocessedRules = new LinkedList<RTGRule<F, Q>>();
		unprocessedRules.add(newRule);
		rules.add(newRule);
		dirtyFTA = true;
	}


	/**
	 * Adds a start symbol to this regular tree grammar.
	 * @param symbol start symbol that is to be added
	 */
	public void addStartSymbol(Q symbol){
		if (unprocessedStartSymbols == null) unprocessedStartSymbols = new LinkedList<Q>();
		unprocessedStartSymbols.add(symbol);
		startSymbols.add(symbol);
		dirtyFTA = true;
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA#getAlphabet()
	 */
	@Override
	public Set<F> getAlphabet() {
		if (dirtyFTA)
			updateFTA();
		return equivFTA.getAlphabet();
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA#getFinalStates()
	 */
	@Override
	public Set<NamedState<Object>> getFinalStates() {
		if (dirtyFTA)
			updateFTA();
		return equivFTA.getFinalStates();
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA#getRules()
	 */
	@Override
	public Set<? extends GenFTARule<F, NamedState<Object>>> getRules() {
		if (dirtyFTA)
			updateFTA();
		return equivFTA.getRules();
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA#getStates()
	 */
	@Override
	public Set<NamedState<Object>> getStates() {
		if (dirtyFTA)
			updateFTA();
		return equivFTA.getStates();
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA#getSymbolRules(de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol)
	 */
	@Override
	public Set<? extends GenFTARule<F, NamedState<Object>>> getSymbolRules(F f) {
		if (dirtyFTA)
			updateFTA();
		return equivFTA.getSymbolRules(f);
	}

}
