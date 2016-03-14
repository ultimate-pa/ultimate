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

import java.util.Collection;

/**
 * This class represents a packed expression. <br>
 * It is used to add another multipicators to an expression.
 *
 * @author Anton, Maria
 * @param <G_Symbol> symbol type
 * @param <G_State> state type
 */
public class JoeExpression<G_Symbol extends UnrankedSymbol, G_State extends State> implements SingleExpression<G_Symbol, G_State> {
	private static final boolean DEBUG = false;
	protected final RegularExpression<G_Symbol, G_State> exp;

	/**
	 * Constructs an SingleExpression from an Expression
	 *
	 * @param exp the RegularExpression to pack into the SingleExpression
	 */
	public JoeExpression(final RegularExpression<G_Symbol, G_State> exp) {
		super();
		this.exp = exp;
	}

	/**
	 * Transforms the expression into a finite tree automaton.
	 *
	 * @param start Set of States to start from
	 * @param ha		HedgeAutomaton this expression belongs to
	 * @param sF		StateFactory for creating states
	 * @return transformed expression
	 */
	@Override
	public Container<G_Symbol, G_State> transform(final Collection<HedgeState<G_State>> start, final HedgeAutomaton<G_Symbol, G_State> ha, final StateFactory sF) {
		if (DEBUG) System.out.println("<-- BEGIN: JoeExpression.transform -->");
		if (DEBUG) System.out.println("<-- JoeExpression.transform call cache.transformExp(" + this.exp + ") -->");
		final Container<G_Symbol, G_State> result1 = ExpressionCache.transformExp(start, this.exp, ha, sF);
		if (DEBUG) System.out.println("<-- JoeExpression.transform call cache.transformExp(" + this.exp + ") returned -->");

		if (DEBUG) System.out.println("<-- END: JoeExpression.transform -->");
		return new Container<G_Symbol, G_State>(result1.getRules(), result1.getFinalStates());
	}

	/**
	 * Transforms the Expression into a finite tree automaton.
	 *
	 * @param start set of states to start from
	 * @param end	 set of states to end in
	 * @param ha		HedgeAutomaton this expression belongs to
	 * @param sF		StateFactory for creating states
	 * @return transformed expression
	 */
	@Override
	public Container<G_Symbol, G_State>
	transformTo(final Collection<HedgeState<G_State>> start, final Collection<HedgeState<G_State>> end, final HedgeAutomaton<G_Symbol, G_State> ha, final StateFactory sF) {
		if (DEBUG) System.out.println("<-- BEGIN: JoeExpression.transformTo -->");
		if (DEBUG) System.out.println("<-- JoeExpression.transformTo call " + this.exp + ".transformTo() -->");
		final Container<G_Symbol, G_State> result1 = exp.transformTo(start, end, ha, sF);
		if (DEBUG) System.out.println("<-- JoeExpression.transformTo call " + this.exp + ".transformTo() returned -->");

		if (DEBUG) System.out.println("<-- END: OrExpression.transformTo -->");
		return new Container<G_Symbol, G_State>(result1.getRules(), end);
	}

	/**
	 * Returns whether this Expression is empty.
	 *
	 * @return whether this Expression is empty
	 */
	@Override
	public boolean isEmpty() {
		return exp.isEmpty();
	}

	/**
	 * Getter for the expression within.
	 *
	 * @return the expression packed in me
	 */
	protected RegularExpression<G_Symbol, G_State> getExp() {
		return this.exp;
	}

	/**
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(final Object exp) {
		if (exp == null) return false;
		if (exp == this) return true;
		if (!(exp instanceof JoeExpression<?, ?>)) return false;
		final JoeExpression<?, ?> j_e = (JoeExpression<?, ?>) exp;
		return j_e.getExp().equals(exp);
	}

	/**
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		return this.exp != null ? exp.hashCode() : 0;
	}

	/**
	 * Creates a String representation of the expression.
	 *
	 * @return String representation of the expression
	 */
	@Override
	public String toString() {
		final StringBuilder buffer = new StringBuilder();
		//buffer.append(" Joe> ");
		buffer.append("(").append(exp.toString()).append(")");
		return buffer.toString();
	}

	/**
	 * Creates optimized 'joe'. It is used to create a more simpler expression.
	 *
	 * @param <G_Symbol>  symbol type of the expression to be created
	 * @param <G_State>  state type of the expression to be created
	 * @param low	lower border. Values >= 0 are allowed.
	 * @param high high border. Values <0 represent infinity.
	 * @param exp	the expression to be packed
	 * @return simplified version of the expression
	 */
	public static <G_Symbol extends UnrankedSymbol, G_State extends State> RegularExpression<G_Symbol, G_State> makeOptimizedJoe(final int low, final int high, final RegularExpression<G_Symbol, G_State> exp) {
		final int e_l = exp.getLow();
		final int e_h = exp.getHigh();
		if (low == 1 && high == 1) return exp;
		if (e_l == 1 && e_h == 1) return new Expression<G_Symbol, G_State>(low, high, exp.getExpression());
		if (low == 0 && high == -1 && e_l == 0 && e_h == -1) return exp;
		return new Expression<G_Symbol, G_State>(low, high, new JoeExpression<G_Symbol, G_State>(exp));
	}
}
