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


/**
 * Creates an alternative expression out of two expressions. 
 * 
 * @author Anton, Maria
 * @param <G_Symbol> symbol type
 * @param <G_State> state type
 */
public class OrExpression<G_Symbol extends UnrankedSymbol, G_State extends State> implements SingleExpression<G_Symbol, G_State> {
	private final boolean DEBUG = false;
	private final RegularExpression<G_Symbol, G_State> expr1;
	private final RegularExpression<G_Symbol, G_State> expr2;


	/**
	 * Constructs an OrExpression with two expressions.
	 *
	 * @param expr1 first RegularExpression for the OrExpression
	 * @param expr2 second RegularExpression for the OrExpression
	 */
	public OrExpression(final RegularExpression<G_Symbol, G_State> expr1, final RegularExpression<G_Symbol, G_State> expr2) {
		super();
		this.expr1 = expr1;
		this.expr2 = expr2;
	}

	/**
	 * @see SingleExpression#transform(java.util.Collection, de.uni_muenster.cs.sev.lethal.hedgeautomaton.HedgeAutomaton, de.uni_muenster.cs.sev.lethal.factories.StateFactory)
	 */
	@Override
	public Container<G_Symbol, G_State> transform(final Collection<HedgeState<G_State>> start, final HedgeAutomaton<G_Symbol, G_State> ha, final StateFactory sF) {
		if (this.DEBUG) System.out.println("<-- BEGIN: OrExpression.transform -->");
		if (this.DEBUG) System.out.println("<-- OrExpression.transform call cache.transformExp(" + this.expr1 + ") -->");
		final Container<G_Symbol, G_State> result1 = ExpressionCache.transformExp(start, this.expr1, ha, sF);
		if (this.DEBUG)
			System.out.println("<-- OrExpression.transform call cache.transformExp(" + this.expr1 + ") returned -->");
		if (this.DEBUG) System.out.println("<-- OrExpression.transform call cache.transformExp(" + this.expr2 + ") -->");
		final Container<G_Symbol, G_State> result2 = ExpressionCache.transformExp(start, this.expr2, ha, sF);
		if (this.DEBUG)
			System.out.println("<-- OrExpression.transform call cache.transformExp(" + this.expr2 + ") returned -->");

		//final HashSet<HedgeState<G_State>> TAStates = new HashSet<HedgeState<G_State>>();
		final HashSet<GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>> TARules = new HashSet<GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>>();
		final HashSet<HedgeState<G_State>> TAFinState = new HashSet<HedgeState<G_State>>();

		if (this.DEBUG) System.out.println("<-- OrExpression.transform collecting results -->");
		if (this.DEBUG) System.out.println("<-- OrExpression.transform States -->");
		//TAStates.addAll(result1.getStates());
		//TAStates.addAll(result2.getStates());
		if (this.DEBUG) System.out.println("<-- OrExpression.transform Rules -->");
		TARules.addAll(result1.getRules());
		TARules.addAll(result2.getRules());
		if (this.DEBUG) System.out.println("<-- OrExpression.transform FinalStates -->");
		TAFinState.addAll(result1.getFinalStates());
		TAFinState.addAll(result2.getFinalStates());
		if (this.DEBUG) System.out.println("<-- OrExpression.transform collecting results finished-->");

		if (this.DEBUG) System.out.println("<-- END: OrExpression.transform -->");
		return new Container<G_Symbol, G_State>(TARules, TAFinState);
	}

	/**
	 * @see SingleExpression#transformTo(java.util.Collection, java.util.Collection, de.uni_muenster.cs.sev.lethal.hedgeautomaton.HedgeAutomaton, de.uni_muenster.cs.sev.lethal.factories.StateFactory)
	 */
	@Override
	public Container<G_Symbol, G_State>
	transformTo(final Collection<HedgeState<G_State>> start, final Collection<HedgeState<G_State>> end, final HedgeAutomaton<G_Symbol, G_State> ha, final StateFactory sF) {
		if (this.DEBUG) System.out.println("<-- BEGIN: OrExpression.transformTo -->");
		if (this.DEBUG) System.out.println("<-- OrExpression.transformTo call " + this.expr1 + ".transformTo() -->");
		final Container<G_Symbol, G_State> result1 = expr1.transformTo(start, end, ha, sF);
		if (this.DEBUG)
			System.out.println("<-- OrExpression.transformTo call " + this.expr1 + ".transformTo() returned -->");
		if (this.DEBUG) System.out.println("<-- OrExpression.transformTo call " + this.expr2 + ".transformTo() -->");
		final Container<G_Symbol, G_State> result2 = expr2.transformTo(start, end, ha, sF);
		if (this.DEBUG)
			System.out.println("<-- OrExpression.transformTo call " + this.expr2 + ".transformTo() returned -->");

		//final HashSet<HedgeState<G_State>> TAStates = new HashSet<HedgeState<G_State>>();
		final HashSet<GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>> TARules = new HashSet<GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>>();

		if (this.DEBUG) System.out.println("<-- OrExpression.transformTo collecting results -->");
		if (this.DEBUG) System.out.println("<-- OrExpression.transformTo States -->");
		//TAStates.addAll(result1.getStates());
		//TAStates.addAll(result2.getStates());
		if (this.DEBUG) System.out.println("<-- OrExpression.transformTo Rules -->");
		TARules.addAll(result1.getRules());
		TARules.addAll(result2.getRules());
		if (this.DEBUG) System.out.println("<-- OrExpression.transformTo collecting results finished-->");

		if (this.DEBUG) System.out.println("<-- END: OrExpression.transformTo -->");
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
		//buffer.append(" Or> ");
		buffer.append("(").append(expr1.toString()).append("|").append(expr2.toString()).append(")");
		return buffer.toString();
	}


	/**
	 * Constructs an OrExpression while trying to simplify the result.
	 *
	 * @param <G_Symbol>  type of the Symbol
	 * @param <G_State>  type of the State
	 * @param low	lower border. Values >= 0 are allowed.
	 * @param high high border. Values <0 represent infinity.
	 * @param exp1 first RegularExpression for the OrExpression
	 * @param exp2 second RegularExpression for the OrExpression
	 * @return the OrExpression from the two RegularExpressions
	 */
	public static <G_Symbol extends UnrankedSymbol, G_State extends State> RegularExpression<G_Symbol, G_State>
	makeOptimizedOr(final int low, final int high, RegularExpression<G_Symbol, G_State> exp1, final RegularExpression<G_Symbol, G_State> exp2) {
		if (!exp1.equals(exp2)) {
			final SingleExpression<G_Symbol, G_State> e1 = exp1.getExpression();
			final SingleExpression<G_Symbol, G_State> e2 = exp2.getExpression();

			if (e1.equals(e2)) {
				if (exp1.getHigh() < exp2.getLow() + 1 ||
						exp2.getHigh() < exp2.getLow() + 1)
					return new Expression<G_Symbol, G_State>(low, high, new OrExpression<G_Symbol, G_State>(exp1, exp2));

				final int e_low = Math.min(exp1.getLow(), exp2.getLow());
				final int e_high = Math.max(exp1.getHigh(), exp2.getHigh());
				exp1 = new Expression<G_Symbol, G_State>(e_low, e_high, e1);
			} else
				return new Expression<G_Symbol, G_State>(low, high, new OrExpression<G_Symbol, G_State>(exp1, exp2));
		}

		if ((low == 1 && high == 1) ||
				(exp1.getLow() == 0 && exp1.getHigh() == -1 && low == 0 && high == -1))
			return exp1;

		if (exp1.getLow() == 1 && exp1.getHigh() == 1)
			return new Expression<G_Symbol, G_State>(low, high, exp1.getExpression());

		return new Expression<G_Symbol, G_State>(low, high, new JoeExpression<G_Symbol, G_State>(exp1));
	}

	/**
	 * @return first RegularExpression of the OrExpression
	 */
	protected RegularExpression<G_Symbol, G_State> getFirst() {
		return this.expr1;
	}


	/**
	 * @return second RegularExpression of the OrExpression
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
		if (!(exp instanceof OrExpression<?, ?>)) return false;
		if (exp == this) return true;
		final OrExpression<?, ?> b_exp = (OrExpression<?, ?>) exp;
		return (expr1.equals(b_exp.getFirst()) && expr2.equals(b_exp.getSecond())) ||
				(expr2.equals(b_exp.getFirst()) && expr1.equals(b_exp.getSecond()));
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
