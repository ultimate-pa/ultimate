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

import java.util.Set;

import de.uni_muenster.cs.sev.lethal.hedgeautomaton.EasyHedgeAutomaton;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.HedgeAutomaton;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.HedgeRule;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;

/**
 * HedgeGrammar subclass that generates EasyHedgeAutomaton
 * @author Philipp
 *
 */
public class EasyHedgeGrammar extends HedgeGrammar<UnrankedSymbol> {

	
	/**
	 * @see HedgeGrammar#HedgeGrammar()
	 */
	public EasyHedgeGrammar() {
		super();
	}

	/**
	 * @see HedgeGrammar#HedgeGrammar(Set, Set)
	 */
	public EasyHedgeGrammar(Set<GrammarRule<UnrankedSymbol>> rule,
			Set<Nonterminal<UnrankedSymbol>> start) {
		super(rule, start);
	}

	@Override
	protected HedgeAutomaton<UnrankedSymbol, State> constructAutmaton(Set<State> haStates, Set<State> haFinalStates, Set<HedgeRule<UnrankedSymbol, State>> haRules) {
		return new EasyHedgeAutomaton(haStates, haFinalStates, haRules);
	}

	/**
	 * @return The Hedge Automaton specified by this HedgeGrammar 
	 */
	@Override
	public EasyHedgeAutomaton getHA() {
		return (EasyHedgeAutomaton)super.getHA(); //Cast is safe because this only returns what was once created by constructAutmaton() which is EasyHedgeAutomaton in this case. 
	}

}
