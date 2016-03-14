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
package de.uni_muenster.cs.sev.lethal.hedgegrammar;

import de.uni_muenster.cs.sev.lethal.hedgeautomaton.HedgeRule;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.expressions.RegularExpression;

import java.util.Set;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;

/**
 * This class represents schema expressions and changes them into an hedge
 * automaton with {@link de.uni_muenster.cs.sev.lethal.hedgeautomaton.HedgeRule}s and {@link State}s and a
 * {@link RegularExpression}.
 * <p/>
 * The subclasses represent different ways of producing regular expressions.
 * 
 * @author Anton, Maria
 * @param <G_Symbol> symbol type of the hedge grammar
 */
public abstract class GrammarExpression<G_Symbol extends UnrankedSymbol> {

	Set<HedgeRule<G_Symbol, State>> rules;

	RegularExpression<G_Symbol, State> exp;

	Set<State> states;

	Set<HedgeRule<G_Symbol, State>> getRules() {
		return this.rules;
	}

	RegularExpression<G_Symbol, State> getRegularExpression() {
		return this.exp;
	}

	Set<State> getStates() {
		return this.states;
	}
}
