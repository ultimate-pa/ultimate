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
package de.uni_muenster.cs.sev.lethal.hedgeautomaton.expressions;

import de.uni_muenster.cs.sev.lethal.hedgeautomaton.internal.Finit;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.HedgeAutomaton;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.internal.Init;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;

/**
 * This class is used in the standard hedge rules to clean the cache after transformation.
 *
 * @author Anton, Maria
 * @param <G_State> state type of hedge automaton to be transformed
 * @param <G_Symbol> symbol type of hedge automaton to be transformed
 */
class InitFinitExpression<G_Symbol extends UnrankedSymbol, G_State extends State> implements Init<G_Symbol, G_State>, Finit<G_Symbol, G_State> {
	/**
	 * @see de.uni_muenster.cs.sev.lethal.hedgeautomaton.internal.Init#initialize(de.uni_muenster.cs.sev.lethal.hedgeautomaton.HedgeAutomaton)
	 */
	@Override
	public void initialize(final HedgeAutomaton<G_Symbol, G_State> ha) {
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.hedgeautomaton.internal.Finit#finalize(de.uni_muenster.cs.sev.lethal.hedgeautomaton.HedgeAutomaton)
	 */
	@Override
	public void finalize(final HedgeAutomaton<G_Symbol, G_State> ha) {
		ExpressionCache.clear(ha);
	}
}
