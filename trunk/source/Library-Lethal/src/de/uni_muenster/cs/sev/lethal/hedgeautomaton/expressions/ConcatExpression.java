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

import de.uni_muenster.cs.sev.lethal.factories.StateFactory;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.HedgeAutomaton;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.internal.Container;
import de.uni_muenster.cs.sev.lethal.states.HedgeState;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.special.HedgeSymbol;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTARule;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;

/**
 * This class represents a concatenation of two regular expressions.
 *
 * @author Anton, Maria
 * @param <G_Symbol> type of symbols occurring in the expression
 * @param <G_State> type of states occurring in the expression
 */
public class ConcatExpression<G_Symbol extends UnrankedSymbol, G_State extends State> implements SingleExpression<G_Symbol, G_State> {
	/**First part.*/
	protected final RegularExpression<G_Symbol, G_State> expr2;
	/**Second part.*/
	protected final RegularExpression<G_Symbol, G_State> expr1;

	/**
	 * Creates new expression from two expressions by concatenation
	 *
	 * @param expr1 first expression
	 * @param expr2 second expression
	 */
	public ConcatExpression(final RegularExpression<G_Symbol, G_State> expr1, final RegularExpression<G_Symbol, G_State> expr2) {
		super();
		this.expr1 = expr1;
		this.expr2 = expr2;
	}

	/**
	 * @see SingleExpression#transform(java.util.Collection, de.uni_muenster.cs.sev.lethal.hedgeautomaton.HedgeAutomaton, de.uni_muenster.cs.sev.lethal.factories.StateFactory)
	 */
	@Override
	public Container<G_Symbol, G_State> transform(final Collection<HedgeState<G_State>> start, final HedgeAutomaton<G_Symbol, G_State> ha, final StateFactory sF) {
		final Container<G_Symbol, G_State> result1 = ExpressionCache.transformExp(start, this.expr1, ha, sF);
		final Container<G_Symbol, G_State> result2 = ExpressionCache.transformExp(result1.getFinalStates(), this.expr2, ha, sF);

		//final HashSet<HedgeState<G_State>> TAStates = new HashSet<HedgeState<G_State>>();
		final HashSet<GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>> TARules = new HashSet<GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>>();

		//TAStates.addAll(result1.getStates());
		//TAStates.addAll(result2.getStates());
		TARules.addAll(result1.getRules());
		TARules.addAll(result2.getRules());

		return new Container<G_Symbol, G_State>(TARules, result2.getFinalStates());
	}

	/**
	 * @see SingleExpression#transformTo(java.util.Collection, java.util.Collection, de.uni_muenster.cs.sev.lethal.hedgeautomaton.HedgeAutomaton, de.uni_muenster.cs.sev.lethal.factories.StateFactory)
	 */
	@Override
	public Container<G_Symbol, G_State>
	transformTo(final Collection<HedgeState<G_State>> start, final Collection<HedgeState<G_State>> end, final HedgeAutomaton<G_Symbol, G_State> ha, final StateFactory sF) {
		final HedgeState<G_State> mid = new HedgeState<G_State>(null, sF.makeState());
		final Collection<HedgeState<G_State>> midSet = new HashSet<HedgeState<G_State>>();
		midSet.add(mid);
		final Container<G_Symbol, G_State> result1 = expr1.transformTo(start, midSet, ha, sF);
		final Container<G_Symbol, G_State> result2 = expr2.transformTo(midSet, end, ha, sF);

		//final HashSet<HedgeState<G_State>> TAStates = new HashSet<HedgeState<G_State>>();
		final HashSet<GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>> TARules = new HashSet<GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>>();


		//TAStates.addAll(result1.getStates());
		//TAStates.addAll(result2.getStates());
		//TAStates.add(mid);
		TARules.addAll(result1.getRules());
		TARules.addAll(result2.getRules());

		return new Container<G_Symbol, G_State>(TARules, end);
	}

	/**
	 * @see SingleExpression#isEmpty()
	 */
	@Override
	public boolean isEmpty() {
		return expr1.isEmpty() && expr2.isEmpty();
	}

	/**
	 * Creates a String representation of the expression.
	 *
	 * @return String representation of the expression
	 */
	@Override
	public String toString() {
		final StringBuilder buffer = new StringBuilder();
		//buffer.append(" Co> ");
		buffer.append("(").append(expr1.toString()).append(expr2.toString()).append(")");
		return buffer.toString();
	}

	/**
	 * Creates new Expression from two Expressions by concatenation. <br>
	 * If the Expressions can be merged, the merged Expression is returned
	 * else a new ConcatExpression is returned.
	 *
	 * @param <G_Symbol>  type of symbol occurring in expression
	 * @param <G_State>  type of states occurring in expression
	 * @param low	lower border. Values >= 0 are allowed.
	 * @param high high border. Values <0 represent infinity.
	 * @param exp1 first Expression
	 * @param exp2 second Expression
	 * @return new Expression representing a concatenation of the two Expressions
	 */

	public static <G_Symbol extends UnrankedSymbol, G_State extends State>
	RegularExpression<G_Symbol, G_State> makeOptimizedConcat(final int low, final int high, RegularExpression<G_Symbol, G_State> exp1, final RegularExpression<G_Symbol, G_State> exp2) {
		final SingleExpression<G_Symbol, G_State> e1 = exp1.getExpression();
		final SingleExpression<G_Symbol, G_State> e2 = exp2.getExpression();
		final int e_h1 = exp1.getHigh();
		final int e_h2 = exp2.getHigh();
		if (e1.equals(e2)) {
			final int e_low = exp1.getLow() + exp2.getLow();
			final int e_high;
			if (Math.min(e_h1, e_h2) < 0)
				e_high = -1;
			else
				e_high = e_h1 + e_h2;
			exp1 = new Expression<G_Symbol, G_State>(e_low, e_high, e1);
			if (low == 1 && high == 1) return exp1;
			return new Expression<G_Symbol, G_State>(low, high, new JoeExpression<G_Symbol, G_State>(exp1));
		}
		if (e_h1 == 1 &&
				exp1.getLow() == 1 &&
				e_h2 == 1 &&
				exp2.getLow() == 1 &&
				e1 instanceof BasicExpression<?, ?> &&
				e2 instanceof BasicExpression<?, ?>) {
			final BasicExpression<G_Symbol, G_State> e1_b = (BasicExpression<G_Symbol, G_State>) e1;
			final BasicExpression<G_Symbol, G_State> e2_b = (BasicExpression<G_Symbol, G_State>) e2;
			final LinkedList<G_State> list = new LinkedList<G_State>();
			list.addAll(e1_b.getStates());
			list.addAll(e2_b.getStates());
			return new Expression<G_Symbol, G_State>(low, high, new BasicExpression<G_Symbol, G_State>(list));
		}
		return new Expression<G_Symbol, G_State>(low, high, new ConcatExpression<G_Symbol, G_State>(exp1, exp2));
	}

	/**
	 * Returns first part of the concatenation.
	 * 
	 * @return first part of the concatenation
	 */
	protected RegularExpression<G_Symbol, G_State> getFirst() {
		return this.expr1;
	}

	/**
	 * Returns second part of the concatenation.
	 * 
	 * @return second part of the concatenation
	 */
	protected RegularExpression<G_Symbol, G_State> getSecond() {
		return this.expr2;
	}

	/**
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(final Object exp) {
		if (exp == null) return false;
		if (exp == this) return true;
		if (!(exp instanceof ConcatExpression<?, ?>)) return false;
		final ConcatExpression<?, ?> b_exp = (ConcatExpression<?, ?>) exp;
		return (this.expr1.equals(b_exp.getFirst()) && this.expr2.equals(b_exp.getSecond()));
	}

	/**
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		int result = this.expr2 != null ? expr2.hashCode() : 0;
		result = 31 * result + (this.expr1 != null ? expr1.hashCode() : 0);
		return result;
	}
}
