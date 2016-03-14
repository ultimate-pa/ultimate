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
package de.uni_muenster.cs.sev.lethal.treeautomata.easy;


import de.uni_muenster.cs.sev.lethal.grammars.RTG;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.AbstractModFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTACreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAEpsRule;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;
import de.uni_muenster.cs.sev.lethal.utils.Converter;


/**
 * Implements a finite tree automaton without generic types.
 * 
 * @see FTA
 * 
 * @author Dorothea, Irene, Martin
 */
public class EasyFTA extends AbstractModFTA<RankedSymbol,State,EasyFTARule>{

	/**
	 * Creates a new EasyFTA out of an arbitrary regular tree grammar.
	 * @param grammar regular tree grammar out of which the new EasyFTA is to be created
	 * @param stateBuilder creator object, which is used to create states out of non-terminals
	 * and trees in the normalization process
	 * @param <P> type of non-terminals occurring in the grammar rules 
	 * @see FTACreator#makeFTAFromGrammar
	 */
	public <P extends State> EasyFTA(RTG<RankedSymbol, P> grammar,
			Converter<Object, State> stateBuilder) {
		super(grammar, stateBuilder);
	}

	/**
	 * Creates an empty finite tree automaton without any states and rules.
	 */
	public EasyFTA() {
		super();
	}

	/**
	 * Creates a new finite tree automaton from rules and final states.<br>
	 * States and alphabet are calculated from the rules and final states.
	 *
	 * @param rules2 rules for the finite tree automaton
	 * @param finalStates2 final states for the finite tree automaton
	 **/
	public EasyFTA(Collection<? extends FTARule<RankedSymbol,State>> rules2,
			Collection<State> finalStates2) {
		super(rules2, finalStates2);
	}


	/**
	 * Creates a new finite tree automaton from the given alphabet, states, final states and rules.
	 * 
	 * @param newAlphabet alphabet of the new finite tree automaton
	 * @param newStates states of the new finite tree automaton
	 * @param newFinalStates final states of the new finite tree automaton
	 * @param newRules rules of the new finite tree automaton
	 */
	public EasyFTA(Collection<RankedSymbol> newAlphabet,
			Collection<State> newStates, 
			Collection<State> newFinalStates,
			Collection<? extends FTARule<RankedSymbol,State>> newRules) {
		super(newAlphabet, newStates, newFinalStates, newRules);
	}
	
	/**
	 * Creates a new finite tree automaton from rules, final states and additional epsilon rules.
	 * The epsilon rules are eliminated and thus converted into normal rules. 
	 * 
	 * @param newRules rules of the new finite tree automaton
	 * @param newEpsRules epsilon rules of the new finite tree automaton
	 * @param newFinals final states of the new finite tree automaton
	 */
	public EasyFTA(Collection<? extends FTARule<RankedSymbol, State>> newRules,
			Collection<? extends FTAEpsRule<State>> newEpsRules,
			Collection<State> newFinals) {
		super(newRules, newEpsRules, newFinals);
	}
	
	/**
	 * Creates a new finite tree automaton from a given one accepting the same language.
	 * 
	 * @param fta finite tree automaton which the new instance shall be created out of
	 */
	public EasyFTA(FTA<RankedSymbol,State, ? extends FTARule<RankedSymbol,State>> fta) {
		super(fta);
	}


	/**
	 * var arg constructor for convenience
	 * 
	 * @param rules2 rules for the finite tree automaton
	 * @param finalStates2 final states for the finite tree automaton
	 */
	public EasyFTA(Collection<EasyFTARule> rules2, State... finalStates2) {
		this(rules2, Arrays.asList(finalStates2)); 
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.AbstractModFTA#createRule
	 */
	@Override
	public EasyFTARule createRule(RankedSymbol srcSymbol,
			List<State> srcStates, State destState) {
		return new EasyFTARule(srcSymbol, srcStates, destState);
	}
}
