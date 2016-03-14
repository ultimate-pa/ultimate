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

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;

import java.util.LinkedList;

/**
 * This class represents the empty expression.
 *
 * @author Anton, Maria
 * @param <G_Symbol> symbol type of expression
 * @param <G_State> state type of expression
 */
public class EmptyExpression<G_Symbol extends UnrankedSymbol, G_State extends State> extends Expression<G_Symbol, G_State> {

	/**
	 * Constructs an empty expression.
	 */
	public EmptyExpression() {
		super(0, 0, new BasicExpression<G_Symbol, G_State>(new LinkedList<G_State>()));
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.hedgeautomaton.expressions.Expression#isEmpty()
	 */
	@Override
	public boolean isEmpty() {
		return true;
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.hedgeautomaton.expressions.Expression#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(final Object exp) {
		if (exp == null) return false;
		if (exp == this) return true;
		if (!(exp instanceof Expression<?, ?>)) return false;
		final Expression<?, ?> b_exp = (Expression<?, ?>) exp;
		return b_exp.isEmpty();
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.hedgeautomaton.expressions.Expression#hashCode()
	 */
	@Override
	public int hashCode() {
		return 0;
	}
}
