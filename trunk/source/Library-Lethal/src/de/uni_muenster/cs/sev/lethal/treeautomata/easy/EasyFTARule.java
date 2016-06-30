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

import java.util.Arrays;
import java.util.List;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTARule;

/**
 * Standard implementation of FTARule without generic types.
 * 
 * @author Dorothea, Irene, Martin
 * 
 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule
 */
public class EasyFTARule extends GenFTARule<RankedSymbol,State>{

	/**
	 * @see GenFTARule#GenFTARule(RankedSymbol, List, State)
	 */
	public EasyFTARule(RankedSymbol symbol, List<State> srcStates,
			State destState) {
		super(symbol, srcStates, destState);
	}


	/**
	 * Constructs a rule from the characteristic data. <br> 
	 * VarArg-constructor for convenience!<br>
	 * Note that the destination state has to be specified <em> before </em> the source states!
	 * 
	 * @param symbol necessary root symbol of a term t
	 * @param destState  destination state
	 * @param states source states of the rule, it can be empty if the symbol is a constant.
	 */
	public EasyFTARule(RankedSymbol symbol, State destState, State... states) {
		super(symbol, Arrays.asList(states),destState);
	}

}
