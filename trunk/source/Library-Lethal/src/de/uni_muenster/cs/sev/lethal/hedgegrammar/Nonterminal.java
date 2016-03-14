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

import de.uni_muenster.cs.sev.lethal.factories.StateFactory;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.HedgeRule;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.expressions.BasicExpression;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.expressions.Expression;

import java.util.HashSet;
import java.util.LinkedList;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;

/**
 * represents a nonterminal symbol needed to describe expressions for a schema
 * 
 * @author Anton, Maria
 * @param <G_Symbol> symbol type of the hedge grammar
 */
public class Nonterminal<G_Symbol extends UnrankedSymbol> extends GrammarExpression<G_Symbol> {

	/**
	 * Symbol describing the nonterminal symbol
	 */
	private String name;

	/**
	 * Creates a new nonterminal symbol
	 * @param name name of the nonterminal symbol
	 */
	public Nonterminal(final String name) {
		super();
		rules = new HashSet<HedgeRule<G_Symbol, State>>();
		State state = StateFactory.getStateFactory().makeState(name);
		states = new HashSet<State>();
		states.add(state);
		LinkedList<State> list = new LinkedList<State>();
		list.addAll(states);
		exp = new Expression<G_Symbol, State>(1, 1,
				new BasicExpression<G_Symbol, State>(list));
		this.name = name;
	}

	protected Nonterminal() {
		super();
		rules = new HashSet<HedgeRule<G_Symbol, State>>();
		State state = StateFactory.getStateFactory().makeState();
		states = new HashSet<State>();
		states.add(state);
		LinkedList<State> list = new LinkedList<State>();
		list.addAll(states);
		exp = new Expression<G_Symbol, State>(1, 1,
				new BasicExpression<G_Symbol, State>(list));
		name = "";
	}

	/**
	 * Returns the name of this nonterminal symbol
	 * @return the name of this nonterminal symbol
	 */
	public String getName() {
		return this.name;
	}

	@Override
	public String toString() {
		return this.name;
	}
}
