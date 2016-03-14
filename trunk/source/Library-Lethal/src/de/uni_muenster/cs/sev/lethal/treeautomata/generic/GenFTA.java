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
package de.uni_muenster.cs.sev.lethal.treeautomata.generic;

import de.uni_muenster.cs.sev.lethal.grammars.RTG;

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
 * Implements a parametrized finite tree automaton.
 * 
 * @param <F> symbol type of this finite tree automaton
 * @param <Q> state type of this finite tree automaton
 * 
 * @see FTA
 * 
 * @author Dorothea, Martin, Irene
 */
public class GenFTA<F extends RankedSymbol, Q extends State> extends AbstractModFTA<F,Q,GenFTARule<F,Q>> {
	
	/**
	 * Creates a new GenFTA out of an arbitrary regular tree grammar.
	 * @param grammar regular tree grammar out of which the new GenFTA is to be created
	 * @param stateBuilder creator object, which is used to create states out of non-terminals
	 * and trees in the normalization process
	 * @param <P> type of non-terminals occurring in the grammar rules 
	 * @see FTACreator#makeFTAFromGrammar
	 */
	public <P extends State> GenFTA(RTG<F, P> grammar,
			Converter<Object, Q> stateBuilder) {
		super(grammar, stateBuilder);
	}

	/**
	 * Creates an empty finite tree automaton without any states and rules.
	 */
	public GenFTA() {
		super();
	}

	/**
	 * Creates a new finite tree automaton from given rules and final states.
	 * 
	 * @param newRules rules of the new finite tree automaton
	 * @param newFinalStates final states of the new finite tree automaton
	 * 
	 * @see AbstractModFTA#AbstractModFTA(Collection, Collection)
	 */
	public GenFTA(Collection<? extends FTARule<F,Q>> newRules,
			Collection<Q> newFinalStates) {
		super(newRules, newFinalStates);
	}

	/**
	 * Creates a new finite tree automaton from given alphabet, states, final states and rules.
	 * 
	 * @param newAlphabet alphabet of the new finite tree automaton
	 * @param newStates states of the new finite tree automaton
	 * @param newFinalStates final states of the new finite tree automaton
	 * @param newRules rules of the new finite tree automaton
	 * 
	 * @see AbstractModFTA#AbstractModFTA(Collection, Collection, Collection, Collection)
	 */
	public GenFTA(Collection<F> newAlphabet, Collection<Q> newStates,
			Collection<Q> newFinalStates,
			Collection<? extends FTARule<F,Q>> newRules) {
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
	public GenFTA(Collection<? extends FTARule<F, Q>> newRules,
			Collection<? extends FTAEpsRule<Q>> newEpsRules,
			Collection<Q> newFinals) {
		super(newRules, newEpsRules, newFinals);
	}

	/**
	 * Creates a new finite tree automaton out of a given one.
	 * 
	 * @param fta finite tree automaton which the new instance shall be created out of
	 * 
	 * @see AbstractModFTA#AbstractModFTA(FTA)
	 */
	public GenFTA(FTA<F,Q, ? extends FTARule<F,Q>> fta) {
		super(fta);
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.AbstractModFTA#createRule
	 */
	@Override
	public GenFTARule<F,Q> createRule(F srcSymbol, List<Q> srcStates,Q destState) {
		return new GenFTARule<F,Q>(srcSymbol, srcStates, destState);
	}
}
