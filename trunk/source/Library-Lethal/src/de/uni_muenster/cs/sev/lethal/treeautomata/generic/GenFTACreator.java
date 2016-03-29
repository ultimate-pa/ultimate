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

import java.util.Collection;
import java.util.List;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTACreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;


/**
 * FTACreator for GenFTA.<br>
 * To create rules and finite tree automata with generic type parameters.
 * 
 * @param <Q> state type of the finite tree automata to be created
 * @param <F> symbol type of the finite tree automata to be created
 * 
 * @author Dorothea, Martin, Irene
 * 
 * @see FTACreator
 * @see GenFTA
 */
public class GenFTACreator<F extends RankedSymbol,Q extends State> extends FTACreator<F,Q,GenFTARule<F,Q>,GenFTA<F,Q>> {

	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTACreator#createFTA(java.util.Collection, java.util.Collection, java.util.Collection, java.util.Collection)
	 */
	@Override
	public GenFTA<F,Q> createFTA(final Collection<F> alphabet, final Collection<Q> states, final Collection<Q> finalStates, final Collection<? extends FTARule<F,Q>> rules) {
		return new GenFTA<F,Q>(alphabet, states, finalStates, rules);
	}
	

	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTACreator#createFTA(java.util.Collection, java.util.Collection)
	 */
	@Override
	public GenFTA<F, Q> createFTA(Collection<? extends FTARule<F, Q>> newRules,
			Collection<Q> newFinals) {
		return new GenFTA<F,Q>(newRules, newFinals);
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTACreator#createRule
	 */
	@Override
	public GenFTARule<F,Q> createRule(F f, List<Q> src, Q dest) {
		return new GenFTARule<F,Q>(f,src,dest);
	}
}
