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
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.expressions.BasicExpression;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.expressions.Expression;

import java.util.HashSet;
import java.util.LinkedList;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;

/**
 * @author Anton, Maria
 * @param <G_Symbol> symbol type of the hedge grammar
 */
public class Function<G_Symbol extends UnrankedSymbol> extends GrammarExpression<G_Symbol> {
	private final Terminal<G_Symbol> t;
	// private final Nonterminal n;
	private final GrammarExpression<G_Symbol> f_exp;

	/**
	 * Creates a new Function grammar expression
	 * @param t the terminal symbol (function)
	 * @param exp the grammar expression (function argument)
	 */
	public Function(final Terminal<G_Symbol> t, final GrammarExpression<G_Symbol> exp) {
		super();
		this.t = t;
		Nonterminal<G_Symbol> n = new Nonterminal<G_Symbol>();
		this.f_exp = exp;
		this.rules = new HashSet<HedgeRule<G_Symbol, State>>();
		this.rules.addAll(exp.getRules());

		this.rules.add(new HedgeRule<G_Symbol, State>(t.getSymbol(), exp
				.getRegularExpression(), n.getStates().iterator().next()));
		LinkedList<State> list = new LinkedList<State>();
		list.addAll(n.getStates());
		this.exp = new Expression<G_Symbol, State>(1, 1,
				new BasicExpression<G_Symbol, State>(list));
		states = new HashSet<State>();
		states.addAll(n.getStates());
		states.addAll(exp.getStates());
	}

	/**
	 * returns the terminal symbol of this function
	 * @return the terminal symbol of this function
	 */
	public Terminal<G_Symbol> getTerminal() {
		return t;
	}

	/**
	 * Returns the grammar expression (function argument)
	 * @return the grammar expression (function argument)
	 */
	public GrammarExpression<G_Symbol> getExpression() {
		return f_exp;
	}

	@Override
	public String toString() {
		return "<" + t + ">" + f_exp.toString() + "</" + t + ">";
	}
}
