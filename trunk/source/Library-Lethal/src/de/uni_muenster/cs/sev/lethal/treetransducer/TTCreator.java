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
package de.uni_muenster.cs.sev.lethal.treetransducer;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTACreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;

/**
 * Creates a GenTT<F,G,Q> and corresponding rules.
 * 
 * @author Irene
 * @param <G> type of destination alphabet symbols
 * @param <F> type of start alphabet symbols
 * @param <Q> type of origin states
 *
 */
public class TTCreator<F extends RankedSymbol,G extends RankedSymbol,Q extends State> extends FTACreator<F,TTState<Q,G>,TTRule<F,G,Q>,GenTT<F,G,Q>> {


	
	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTACreator#createFTA(java.util.Collection, java.util.Collection)
	 */
	@Override
	public GenTT<F, G, Q> createFTA(
			Collection<? extends FTARule<F, TTState<Q, G>>> newRules,
			Collection<TTState<Q, G>> newFinals) {
		ArrayList<Q> finals = new ArrayList<Q>();
		for (TTState<Q,G> s: newFinals){
			finals.add(s.getState());
		}
		return new GenTT<F,G,Q>(finals,newRules);
	}
	
	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTACreator#createFTA(java.util.Collection, java.util.Collection, java.util.Collection, java.util.Collection)
	 */
	@Override
	public GenTT<F, G, Q> createFTA(Collection<F> alphabet,
			Collection<TTState<Q, G>> states,
			Collection<TTState<Q, G>> finalStates,
			Collection<? extends FTARule<F, TTState<Q, G>>> rules) {
		ArrayList<Q> finals = new ArrayList<Q>();
		for (TTState<Q,G> s: finalStates){
			finals.add(s.getState());
		}
		GenTT<F,G,Q> temp =  new GenTT<F,G,Q>(finals,rules);
		Collection<G> destAlph = temp.getDestAlphabet();
		return new GenTT<F,G,Q>(finals,alphabet,destAlph,rules);
	}

	
	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTACreator#createRule(de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol, java.util.List, de.uni_muenster.cs.sev.lethal.states.State)
	 */
	@Override
	public TTRule<F, G, Q> createRule(F f, List<TTState<Q, G>> src,	TTState<Q, G> dest) {
		if (dest.getVarTree() == null)
			throw new IllegalArgumentException("The destination state must contain a variable.");
		return new TTRule<F,G,Q>(f,src,dest);
	}

	
	
	
}
