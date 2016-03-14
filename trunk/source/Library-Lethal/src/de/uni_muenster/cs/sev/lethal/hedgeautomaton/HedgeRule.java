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

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;

/**
 * This class represents hedge rules.
 *
 * @author Anton, Maria
 * @param <G_Symbol> type of symbols occurring in hedge rule
 * @param <G_State> type of states occurring in hedge rule
 */
public class HedgeRule<G_Symbol extends UnrankedSymbol, G_State extends State> {

	/**
	 * Symbol of the rule
	 */
	protected final G_Symbol symbol;
	/**
	 * Information necessary to apply this rule
	 */
	protected final RegularLanguage<G_Symbol, G_State> expression;
	/**
	 * Destination state of the rule
	 */
	protected final G_State state;

	/**
	 * @param symbol		symbol of the rule
	 * @param exp			 information necessary to apply the rule
	 * @param destState destination state of the rule
	 */
	public HedgeRule(final G_Symbol symbol,
									 final RegularLanguage<G_Symbol, G_State> exp,
									 final G_State destState) {
		super();
		this.state = destState;
		this.expression = exp;
		this.symbol = symbol;
	}

	/**
	 * @return information necessary to apply the rule
	 */
	public RegularLanguage<G_Symbol, G_State> getExpression() {
		return this.expression;
	}

	/**
	 * @return symbol of the rule
	 */
	public G_Symbol getSymbol() {
		return this.symbol;
	}

	/**
	 * @return destination state of the rule
	 */
	public G_State getState() {
		return this.state;
	}

	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		final StringBuffer buffer = new StringBuffer();
		buffer.append(symbol.toString()).append("(").append(
				expression.toString()).append(")");
		buffer.append(" -> ").append(state.toString());
		return buffer.toString();
	}

	/**
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(final Object obj) {
		if (obj == null)
			return false;
		if (obj == this)
			return true;
		if (obj instanceof HedgeRule<?, ?>) {
			final HedgeRule<?, ?> t = (HedgeRule<?, ?>) obj;
			return (symbol.equals(t.getSymbol()) && state.equals(t.getState()) && expression
					.equals(t.getExpression()));
		} else
			return false;
	}

	/**
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		int result = this.symbol != null ? symbol.hashCode() : 0;
		result = 31 * result
				+ (this.expression != null ? expression.hashCode() : 0);
		result = 31 * result + (this.state != null ? state.hashCode() : 0);
		return result;
	}
}
