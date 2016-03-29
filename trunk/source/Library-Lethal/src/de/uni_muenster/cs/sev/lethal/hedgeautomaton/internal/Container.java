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
package de.uni_muenster.cs.sev.lethal.hedgeautomaton.internal;

import de.uni_muenster.cs.sev.lethal.states.HedgeState;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.special.HedgeSymbol;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTARule;

import java.util.Collection;

/**
 * Used as transport package de.uni_muenster.cs.sev.lethal.for the generation of the FTA from HA.
 * <p/>
 * @param <G_Symbol> symbol type of the HA
 * @param <G_State> state type of the HA
 *
 * @author Anton, Maria
 */
public class Container<G_Symbol extends UnrankedSymbol, G_State extends State> {
	final Collection<HedgeState<G_State>> fin;
	final Collection<GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>> rules;

	/**
	 * Creates new package de.uni_muenster.cs.sev.lethal.with parts of the generated FTA.
	 *
	 * @param rules rules of the generated FTA
	 * @param fin	 final states of the generated FTA
	 */
	public Container(final Collection<GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>> rules, final Collection<HedgeState<G_State>> fin) {
		super();
		this.fin = fin;
		this.rules = rules;
	}

	/**
	 * Returns final states of the generated FTA.
	 *
	 * @return final states of the generated FTA
	 */
	public Collection<HedgeState<G_State>> getFinalStates() {
		return this.fin;
	}

	/**
	 * Returns rules of the generated FTA
	 *
	 * @return rules of the generated FTA
	 */
	public Collection<GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>> getRules() {
		return this.rules;
	}
}
