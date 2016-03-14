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
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.expressions.JoeExpression;

import java.util.HashSet;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;

/**
 * 
 * 
 * @author Anton, Maria
 * @param <G_Symbol> symbol type of the hedge grammar
 */
public class Range<G_Symbol extends UnrankedSymbol> extends GrammarExpression<G_Symbol> {
	private final GrammarExpression<G_Symbol> r_exp;

	/**
	 * Creates a new grammar range expression
	 * @param low minimum count of the contained expression
	 * @param high maximum count of the contained expression
	 * @param exp the contained grammar expression
	 */
	public Range(int low, int high, GrammarExpression<G_Symbol> exp) {
		super();
		this.r_exp = exp;
		rules = new HashSet<HedgeRule<G_Symbol, State>>();
		rules.addAll(exp.getRules());
		states = new HashSet<State>();
		states.addAll(exp.getStates());
		this.exp = JoeExpression.makeOptimizedJoe(low, high, exp
				.getRegularExpression());
	}

	/**
	 * Returns the contained grammar expression
	 * @return the contained grammar expression
	 */
	public GrammarExpression<G_Symbol> getExpression() {
		return r_exp;
	}

	@Override
	public String toString() {
		String ret = "(" + r_exp.toString() + ")";
		if (exp.getHigh() < 0)
			if (exp.getLow() == 0)
				return ret += "*";
			else if (exp.getLow() == 1)
				return ret += "+";
		return ret += "{" + exp.getLow() + "," + exp.getHigh() + "}";
	}
}
