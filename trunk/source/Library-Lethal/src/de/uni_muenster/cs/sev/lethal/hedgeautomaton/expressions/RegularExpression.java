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

import de.uni_muenster.cs.sev.lethal.factories.StateFactory;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.HedgeAutomaton;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.RegularLanguage;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.internal.Container;
import de.uni_muenster.cs.sev.lethal.states.HedgeState;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;

import java.util.Collection;

/**
 * This interface is used in the hedge rules. It represents a regular expression.
 *
 * @author Anton, Maria
 * @param <G_Symbol> symbol type of this expression
 * @param <G_State> state type of this expression
 */
public interface RegularExpression<G_Symbol extends UnrankedSymbol, G_State extends State> extends RegularLanguage<G_Symbol, G_State> {
	/**
	 * Returns lower border of the multiplication.
	 *
	 * @return lower border of the multiplication.
	 */
	int getLow();

	/**
	 * Returns high border of the multiplication.
	 *
	 * @return high border of the multiplication.
	 */
	int getHigh();

	/**
	 * Returns singleExpression this class is extending.
	 *
	 * @return singleExpression this class is extending.
	 */
	SingleExpression<G_Symbol, G_State> getExpression();

	/**
	 * Transforms the Expression into a FiniteTreeAutomaton.
	 *
	 * @param start set of States to start from
	 * @param end	 set of States to end in
	 * @param ha		HedgeAutomaton this rule is from
	 * @param sF		StateFactory for creating states
	 * @return transformed Expression
	 */
	Container<G_Symbol, G_State> transformTo(Collection<HedgeState<G_State>> start, Collection<HedgeState<G_State>> end, HedgeAutomaton<G_Symbol, G_State> ha, StateFactory sF);

}
