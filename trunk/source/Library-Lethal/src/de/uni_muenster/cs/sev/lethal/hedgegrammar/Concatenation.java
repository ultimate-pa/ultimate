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
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.expressions.ConcatExpression;

import java.util.HashSet;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;

/**
 * @author Anton, Maria
 * @param <G_Symbol> symbol type of the hedge grammar
 */
public class Concatenation<G_Symbol extends UnrankedSymbol> extends
		GrammarExpression<G_Symbol> {
	private GrammarExpression<G_Symbol> exp1;
	private GrammarExpression<G_Symbol> exp2;

	/**
	 * Creates a new Concatenation from two expressions
	 * @param exp1 the first Expression of the concatenation
	 * @param exp2 the second Expression of the concatenation
	 */
	public Concatenation(GrammarExpression<G_Symbol> exp1, GrammarExpression<G_Symbol> exp2) {
		super();
		this.exp1 = exp1;
		this.exp2 = exp2;
		rules = new HashSet<HedgeRule<G_Symbol, State>>();
		rules.addAll(exp1.getRules());
		rules.addAll(exp2.getRules());
		states = new HashSet<State>();
		states.addAll(exp1.getStates());
		states.addAll(exp2.getStates());
		exp = ConcatExpression.makeOptimizedConcat(1, 1, exp1
				.getRegularExpression(), exp2.getRegularExpression());
	}

	/**
	 * Returns the first Expression of the concatenation
	 * @return the first Expression of the concatenation
	 */
	public GrammarExpression<G_Symbol> getExp1() {
		return exp1;
	}

	/**
	 * Returns the second Expression of the concatenation
	 * @return the second Expression of the concatenation
	 */
	public GrammarExpression<G_Symbol> getExp2() {
		return exp2;
	}

	@Override
	public String toString() {
		return "(" + exp1.toString() + " " + exp2.toString() + ")";
	}
}
