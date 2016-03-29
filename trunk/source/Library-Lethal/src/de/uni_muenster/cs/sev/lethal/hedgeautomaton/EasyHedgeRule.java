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

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;

/**
 * A simple version of the HedgeRule for the EasyHedgeAutomaton.
 *
 * @author Anton Reis, Maria Schatz
 */
public class EasyHedgeRule extends HedgeRule<UnrankedSymbol, State> {
	/**
	 * Creates a new EasyHedgeRule.
	 *
	 * @param symbol		the symbol for the rule
	 * @param exp			 the source expression for the rule
	 * @param destState the destination state for the rule
	 */
	EasyHedgeRule(final UnrankedSymbol symbol,
								final RegularLanguage<UnrankedSymbol, State> exp,
								final State destState) {
		super(symbol, exp, destState);
	}
}
