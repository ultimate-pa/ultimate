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

import java.util.Collection;
import java.util.List;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTACreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;


/**
 * FTACreator for EasyFTA.<br>
 * To create rules and finite tree automata in an easy way without generic type parameters.
 * 
 * @see FTACreator
 * @see EasyFTA
 * 
 * @author Dorothea, Irene, Martin
 */
public class EasyFTACreator extends FTACreator<RankedSymbol,State,EasyFTARule,EasyFTA> {

	
	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTACreator#createFTA(java.util.Collection, java.util.Collection, java.util.Collection, java.util.Collection)
	 */
	@Override
	public EasyFTA createFTA(Collection<RankedSymbol> alphabet, Collection<State> states, Collection<State> finalStates, Collection<? extends FTARule<RankedSymbol,State>> rules) {
		return new EasyFTA(alphabet, states,finalStates,rules);
	}
	
	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTACreator#createFTA(java.util.Collection, java.util.Collection)
	 */
	@Override
	public EasyFTA createFTA(
			Collection<? extends FTARule<RankedSymbol, State>> newRules,
			Collection<State> newFinals) {
		return new EasyFTA(newRules, newFinals);
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTACreator#createRule
	 */
	@Override
	public EasyFTARule createRule(RankedSymbol f, List<State> src, State dest) {
		return new EasyFTARule(f,src,dest);
	}
}
