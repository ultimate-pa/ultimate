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
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.expressions.OrExpression;

import java.util.HashSet;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;

/**
 * This class represents a regular expression which is the alternation of two
 * regular expressions. In Symbols: (E1|E2). This is one way to produce regular
 * expressions.<br>
 * The class is also used to change the regular expressions into a hedge
 * automaton.
 * @param <G_Symbol> symbol type of the hedge grammar
 * 
 * @author Anton, Maria
 */
public class Alternation<G_Symbol extends UnrankedSymbol> extends GrammarExpression<G_Symbol> {

	/**
	 * First alternative expression.
	 */
	private final GrammarExpression<G_Symbol> exp1;
	/**
	 * Second alternative expression.
	 */
	private final GrammarExpression<G_Symbol> exp2;

	/**
	 * Constructs a new Alternation with two regular expressions and calculates
	 * corresponding states and rules for a hedge automaton.
	 * 
	 * @param exp1
	 *            first alternative expression.
	 * @param exp2
	 *            second alternative expression.
	 */
	public Alternation(GrammarExpression<G_Symbol> exp1, GrammarExpression<G_Symbol> exp2) {
		super();
		this.exp1 = exp1;
		this.exp2 = exp2;
		rules = new HashSet<HedgeRule<G_Symbol, State>>();
		rules.addAll(exp1.getRules());
		rules.addAll(exp2.getRules());
		states = new HashSet<State>();
		states.addAll(exp1.getStates());
		states.addAll(exp2.getStates());
		exp = OrExpression.makeOptimizedOr(1, 1, exp1.getRegularExpression(),
				exp2.getRegularExpression());
	}

	/**
	 * Returns the first Expression of the alternation
	 * @return the first Expression of the alternation
	 */
	public GrammarExpression<G_Symbol> getExp1() {
		return exp1;
	}

	/**
	 * Returns the second Expression of the alternation
	 * @return the second Expression of the alternation
	 */
	public GrammarExpression<G_Symbol> getExp2() {
		return exp2;
	}

	@Override
	public String toString() {
		return "(" + exp1.toString() + "|" + exp2.toString() + ")";
	}

}
