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

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.HedgeAutomaton;

/**
 * Implementation of this interface do all the cleaning and finishing jobs after
 * the transformation of hedge rules into FTA.
 *
 * @author Anton, Maria
 * @param <G_State> state type of hedge automaton to be transformed
 * @param <G_Symbol> symbol type of hedge automaton to be transformed
 */
public interface Finit<G_Symbol extends UnrankedSymbol, G_State extends State> {
	/**
	 * This function will be called after the transformation.
	 *
	 * @param ha the HA, which was transformed
	 */
	void finalize(HedgeAutomaton<G_Symbol, G_State> ha);
}
