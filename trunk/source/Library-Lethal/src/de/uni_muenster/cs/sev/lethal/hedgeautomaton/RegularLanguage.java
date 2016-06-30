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

import de.uni_muenster.cs.sev.lethal.factories.StateFactory;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.internal.Container;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.internal.Finit;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.internal.Init;
import de.uni_muenster.cs.sev.lethal.states.HedgeState;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;

/**
 * This interface is used in the hedge rules.
 *
 * @author Anton, Maria
 * @param <G_State> type of states occurring in regular language
 * @param <G_Symbol> type of symbols occurring in {@link HedgeRule rules}
 */
public interface RegularLanguage<G_Symbol extends UnrankedSymbol, G_State extends State> {

	/**
	 * Returns the object with the function to be called on first occurrence while running the transformation.
	 *
	 * @return the object with the function to be called on first occurrence while running the transformation
	 */
	Init<G_Symbol, G_State> getInitializer();

	/**
	 * Returns the object with the function to be called after the transformation.
	 *
	 * @return the object with the function to be called after the transformation
	 */
	Finit<G_Symbol, G_State> getFinaliser();

	/**
	 * Transforms the Expression into a FiniteTreeAutomaton shall use the given
	 * StateFactory to generate states and HedgeStateCache for transforming them
	 * into HedgeStates.
	 *
	 * @param start State to start from
	 * @param ha		HedgeAutomaton this rule is from
	 * @param sF		StateFactory for creating states
	 * @return transformed Expression
	 */
	Container<G_Symbol, G_State> transform(
			HedgeState<G_State> start, HedgeAutomaton<G_Symbol, G_State> ha,
			StateFactory sF);

	/**
	 * Returns whether this Expression is empty.
	 *
	 * @return whether this Expression is empty
	 */
	boolean isEmpty();

	/**
	 * Returns whether this language contains the empty word.
	 *
	 * @return whether this language contains the empty word
	 */
	boolean acceptsEmptyWord();
}
