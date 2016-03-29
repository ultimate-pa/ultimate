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
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.internal.Finit;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.HedgeAutomaton;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.internal.Init;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.internal.Container;
import de.uni_muenster.cs.sev.lethal.states.HedgeState;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.special.HedgeSymbol;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTARule;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

/**
 * Represents an regular expression of States (@see states.State).<br>
 * This class adds the multiplies to the singleExpression (@see hedge.expressions.singleExpression).
 *
 * @author Anton, Maria
 * @param <G_Symbol> type of states occurring in expression
 * @param <G_State> type of symbol occurring in expression
 */
public class Expression<G_Symbol extends UnrankedSymbol, G_State extends State> implements RegularExpression<G_Symbol, G_State> {
	private final boolean DEBUG = false;

	private int iHigh;
	private int iLow;
	private SingleExpression<G_Symbol, G_State> sExp;

	/**
	 * Creates a new expression from a single expression with given multiplies.<br>
	 * The Expression represents a repeated concatenation of the singleExpression
	 * The singleExpression repeats 'low' to 'high' times.
	 *
	 * @param low	lower border. Values >= 0 are allowed.
	 * @param high high border. Values <0 represent infinity.
	 * @param exp	singleExpression to repeat
	 */
	public Expression(final int low, final int high, final SingleExpression<G_Symbol, G_State> exp) {
		super();
		if ((low > high && high >= 0) || (low < 0)) {
			throw new IllegalArgumentException("low must be higher than 0 and lower than high unless high is below 0");
		}
		if (exp.isEmpty()) {
			this.iLow = 0;
			this.iHigh = 0;
		} else {
			this.iLow = low;
			this.iHigh = high;
		}
		this.sExp = exp;
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.hedgeautomaton.expressions.RegularExpression#getLow()
	 */
	@Override
	public int getLow() {
		return this.iLow;
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.hedgeautomaton.expressions.RegularExpression#getHigh()
	 */
	@Override
	public int getHigh() {
		return this.iHigh;
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.hedgeautomaton.expressions.RegularExpression#getExpression()
	 */
	@Override
	public SingleExpression<G_Symbol, G_State> getExpression() {
		return this.sExp;
	}

	/**
	 * Transforms the expression into a finite tree automaton.
	 *
	 * @param start set of States to start from
	 * @param end	 set of States to end in
	 * @param ha		HedgeAutomaton this rule is from
	 * @param sF		StateFactory for creating states
	 * @return transformed expression
	 */
	@Override
	public Container<G_Symbol, G_State>
	transformTo(Collection<HedgeState<G_State>> start, final Collection<HedgeState<G_State>> end, final HedgeAutomaton<G_Symbol, G_State> ha, final StateFactory sF) {
		if (this.DEBUG) System.out.println("<-- BEGIN: expressions.transformTo -->");
		//final HashSet<HedgeState<G_State>> TAStates = new HashSet<HedgeState<G_State>>();
		final HashSet<GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>> TARules = new HashSet<GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>>();
		if (this.iLow == 0 && this.iHigh == 0) {
			if (this.DEBUG) System.out.println("<-- BEGIN: expressions.transformTo low=high=0 -->");
			return new Container<G_Symbol, G_State>(TARules, start);
		}
		if (this.DEBUG)
			System.out.println("<-- BEGIN: expressions.transformTo start for (" + this.iLow + "," + this.iHigh + " -->");
		Set<HedgeState<G_State>> endStates;
		Container<G_Symbol, G_State> result;
		for (int h = Math.max(this.iHigh, this.iLow); h > 1; h--) {
			final HedgeState<G_State> newEnd = new HedgeState<G_State>(null, sF.makeState());
			endStates = new HashSet<HedgeState<G_State>>();
			endStates.addAll(end);
			endStates.add(newEnd);
			result = sExp.transformTo(start, endStates, ha, sF);
			//TAStates.addAll(result.getStates());
			TARules.addAll(result.getRules());
			start = new HashSet<HedgeState<G_State>>();
			start.add(newEnd);
		}
		if (this.DEBUG) System.out.println("<-- BEGIN: expressions.transformTo end for -->");
		endStates = new HashSet<HedgeState<G_State>>();
		endStates.addAll(end);
		result = sExp.transformTo(start, endStates, ha, sF);
		//TAStates.addAll(result.getStates());
		TARules.addAll(result.getRules());
		if (this.DEBUG) System.out.println("<-- END: expressions.transformTo -->");
		return new Container<G_Symbol, G_State>(TARules, end);
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.hedgeautomaton.RegularLanguage#getInitializer()
	 */
	@Override
	public Init<G_Symbol, G_State> getInitializer() {
		return null;
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.hedgeautomaton.RegularLanguage#getFinaliser()
	 */
	@Override
	public Finit<G_Symbol, G_State> getFinaliser() {
		return new InitFinitExpression<G_Symbol, G_State>();
	}

	/**
	 * Transforms the expression into a finite tree automaton.
	 *
	 * @param start set of States to start from
	 * @param ha		HedgeAutomaton this rule is from
	 * @param sF		StateFactory for creating states
	 * @return transformed expression
	 */
	@Override
	public Container<G_Symbol, G_State> transform(final HedgeState<G_State> start, final HedgeAutomaton<G_Symbol, G_State> ha, final StateFactory sF) {
		final Collection<HedgeState<G_State>> st = new HashSet<HedgeState<G_State>>();
		st.add(start);
		return ExpressionCache.transformExp(st, this, ha, sF);
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.hedgeautomaton.expressions.RegularExpression#isEmpty()
	 */
	@Override
	public boolean isEmpty() {
		return this.iHigh == 0;
	}

	/**
	 * Creates a String representation of the Expression.
	 *
	 * @return String representation of the Expression
	 */
	@Override
	public String toString() {
		final StringBuilder buffer = new StringBuilder();
		//buffer.append(" 1> ");
		buffer.append(sExp.toString());
		if (this.iLow == 0) {
			if (this.iHigh < 0) {
				buffer.append("*");
			} else if (this.iHigh == 1) {
				buffer.append("?");
			} else if (this.iHigh > 1) {
				buffer.append("^(").append(this.iLow).append("-").append(this.iHigh).append(")");
			}
		} else if (this.iLow == 1) {
			if (this.iHigh < 0) {
				buffer.append("+");
			} else if (this.iHigh > 1) {
				buffer.append("^").append(this.iLow).append("-").append(this.iHigh).append(")");
			}
		} else {
			buffer.append("^(").append(this.iLow).append("-");
			if (this.iHigh < 0) buffer.append("*)");
			else buffer.append(this.iHigh).append(")");
		}
		return buffer.toString();
	}

	/**
	 * Returns whether this Expression is empty.
	 *
	 * @return whether this Expression is empty
	 */
	@Override
	public boolean acceptsEmptyWord() {
		return false;
	}

	/**
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(final Object exp) {
		if (exp == null) return false;
		if (exp == this) return true;
		if (!(exp instanceof Expression<?, ?>)) return false;
		final RegularExpression<?, ?> e_exp = (RegularExpression<?, ?>) exp;
		return (this.iLow == e_exp.getLow() &&
				this.iHigh == e_exp.getHigh() &&
				e_exp.getExpression().equals(this.sExp));
	}

	/**
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		int result = 31 * this.iHigh + this.iLow;
		result = 31 * result + (this.sExp != null ? sExp.hashCode() : 0);
		return result;
	}
}

