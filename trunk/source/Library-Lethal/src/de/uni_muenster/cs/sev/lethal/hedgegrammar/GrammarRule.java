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

import java.util.HashSet;
import java.util.Set;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;

/**
 * @author Anton, Maria
 * @param <G_Symbol> symbol type of the hedge grammar
 */
public class GrammarRule<G_Symbol extends UnrankedSymbol> {

	private Nonterminal<G_Symbol> n;
	private Terminal<G_Symbol> t;
	private GrammarExpression<G_Symbol> exp;

	/**
	 * Creates a new grammar rule
	 * @param n the left side Nonterminal of the rule.
	 * @param t the terminal of the right side function of the rule (all grammar rules must start with a function).
	 * @param exp the argument grammar expression for the right side function. 
	 */
	public GrammarRule(Nonterminal<G_Symbol> n, Terminal<G_Symbol> t, GrammarExpression<G_Symbol> exp) {
		super();
		this.n = n;
		this.t = t;
		this.exp = exp;
	}

	/**
	 * Returns the left side Nonterminal of the rule.
	 * @return the left side Nonterminal of the rule.
	 */
	public Nonterminal<G_Symbol> getNonterminal() {
		return n;
	}

	/**
	 * Returns the terminal of the right side function of the rule
	 * @return the terminal of the right side function of the rule
	 */
	public Terminal<G_Symbol> getTerminal() {
		return t;
	}

	/**
	 * Returns the argument grammar expression for the right side function.
	 * @return the argument grammar expression for the right side function.
	 */
	public GrammarExpression<G_Symbol> getExpression() {
		return exp;
	}

	protected Set<State> getStates() {
		Set<State> s = new HashSet<State>();
		s.addAll(exp.getStates());
		s.addAll(n.getStates());
		return s;
	}

	@Override
	public String toString() {
		return n + "-> <" + t + ">" + exp.toString() + "</" + t + ">";
	}

}
