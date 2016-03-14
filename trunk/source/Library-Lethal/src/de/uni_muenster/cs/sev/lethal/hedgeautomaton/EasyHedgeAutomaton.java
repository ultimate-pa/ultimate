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
package de.uni_muenster.cs.sev.lethal.hedgeautomaton;

import de.uni_muenster.cs.sev.lethal.states.HedgeState;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.special.HedgeSymbol;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;

import java.util.Set;

/**
 * A simple version of the HedgeAutomaton, where the types of the symbols and 
 * states are of no importance.
 *
 * @author Anton Reis, Maria Schatz
 */
public class EasyHedgeAutomaton extends HedgeAutomaton<UnrankedSymbol, State> {
	/**
	 * Creates an EasyHedgeAutomaton.
	 *
	 * @param States			states for the automaton
	 * @param FinalStates final states for the automaton
	 * @param Rules			 the rules to follow for the automaton
	 */
	public EasyHedgeAutomaton(final Set<State> States,
			final Set<State> FinalStates,
			final Set<HedgeRule<UnrankedSymbol, State>> Rules) {
		super(States, FinalStates, Rules);
	}

	/**
	 * Internal constructor to create hedge automaton from a finite tree automaton.
	 *
	 * @param TA the FTA to create HA from
	 */
	EasyHedgeAutomaton(final FTA<HedgeSymbol<UnrankedSymbol>,
			HedgeState<State>,
			? extends FTARule<HedgeSymbol<UnrankedSymbol>, HedgeState<State>>> TA) {
		super(TA);
	}
}
