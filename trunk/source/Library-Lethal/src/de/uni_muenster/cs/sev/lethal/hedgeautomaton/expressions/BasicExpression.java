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
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.internal.HedgeStateCache;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.internal.HedgeSymbolCache;
import de.uni_muenster.cs.sev.lethal.states.HedgeState;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.special.HedgeSymbol;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTARule;

import java.util.*;

/**
 * This class represents the concatenation of two simple states.
 *
 * @author Anton, Maria
 * @param <G_State> state type
 * @param <G_Symbol> symbol type
 */
public class BasicExpression<G_Symbol extends UnrankedSymbol, G_State extends State> implements SingleExpression<G_Symbol, G_State> {
	private final List<G_State> states;
	private final boolean DEBUG = false;

	/**
	 * Creates an expression from list of states. Equal to the concatenation of them.
	 *
	 * @param states list of states
	 */
	public BasicExpression(final List<G_State> states) {
		super();
		this.states = states;
	}

	/**
	 * @see SingleExpression#transform(java.util.Collection, de.uni_muenster.cs.sev.lethal.hedgeautomaton.HedgeAutomaton, de.uni_muenster.cs.sev.lethal.factories.StateFactory)
	 */
	@Override
	public Container<G_Symbol, G_State> transform(final Collection<HedgeState<G_State>> start, final HedgeAutomaton<G_Symbol, G_State> ha, final StateFactory sF) {
		if (this.DEBUG) System.out.println("<-- BEGIN: BasicExpression.transform -->");
		final HedgeState<G_State> sEnd = new HedgeState<G_State>(null, sF.makeState());
		final Collection<HedgeState<G_State>> end = new HashSet<HedgeState<G_State>>();
		end.add(sEnd);
		if (this.DEBUG) System.out.println("<-- BasicExpression.transform call transformTo -->");
		final Container<G_Symbol, G_State> result = this.transformTo(start, end, ha, sF);
		if (this.DEBUG) System.out.println("<-- BasicExpression.transform call transformTo returned -->");

		//final HashSet<HedgeState<G_State>> TAStates = new HashSet<HedgeState<G_State>>();
		final HashSet<HedgeState<G_State>> TAFinState = new HashSet<HedgeState<G_State>>();
		//TAStates.addAll(result.getStates());
		TAFinState.addAll(result.getFinalStates());
		//TAStates.add(sEnd);
		TAFinState.add(sEnd);

		if (this.DEBUG) System.out.println("<-- END: BasicExpression.transform -->");
		return new Container<G_Symbol, G_State>(result.getRules(), TAFinState);
	}

	/**
	 * @see SingleExpression#transformTo(java.util.Collection, java.util.Collection, de.uni_muenster.cs.sev.lethal.hedgeautomaton.HedgeAutomaton, de.uni_muenster.cs.sev.lethal.factories.StateFactory)
	 */
	@Override
	public Container<G_Symbol, G_State>
	transformTo(final Collection<HedgeState<G_State>> start, final Collection<HedgeState<G_State>> end, final HedgeAutomaton<G_Symbol, G_State> ha, final StateFactory sF) {
		if (this.DEBUG) System.out.println("<-- BEGIN: BasicExpression.transformTo -->");
		//final HashSet<HedgeState<G_State>> TAStates = new HashSet<HedgeState<G_State>>();
		final HashSet<GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>> TARules = new HashSet<GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>>();
		final HashSet<HedgeState<G_State>> TAFinState = new HashSet<HedgeState<G_State>>();
		final HedgeSymbol<G_Symbol> cons = HedgeSymbolCache.getConsSymbol(ha);
		if (this.states.size() == 0) {
			if (this.DEBUG) System.out.println("<-- BasicExpression.transformTo empty expression detected -->");
			for (final HedgeState<G_State> s1 : start) {
				if (this.DEBUG) System.out.println("<-- BasicExpression.transformTo next start -->");
				for (final HedgeState<G_State> s2 : end) {
					if (this.DEBUG) System.out.println("<-- BasicExpression.transformTo next end -->");
					final LinkedList<HedgeState<G_State>> tempStates = new LinkedList<HedgeState<G_State>>();
					tempStates.add(s1);
					TARules.add(new GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>(cons, tempStates, s2));
					if (this.DEBUG)
						System.out.println("<-- BasicExpression.transformTo created cons-rule " + cons + "(" + tempStates + ") -> " + s2 + " -->");
				}
			}
		} else if (this.states.size() == 1) {
			if (this.DEBUG) System.out.println("<-- BasicExpression.transformTo expression with only one state detected -->");
			final HedgeState<G_State> in = HedgeStateCache.getState(this.states.listIterator().next());
			for (final HedgeState<G_State> s1 : start) {
				if (this.DEBUG) System.out.println("<-- BasicExpression.transformTo next start -->");
				for (final HedgeState<G_State> s2 : end) {
					if (this.DEBUG) System.out.println("<-- BasicExpression.transformTo next end -->");
					final LinkedList<HedgeState<G_State>> tempStates = new LinkedList<HedgeState<G_State>>();
					tempStates.add(s1);
					tempStates.add(in);
					TARules.add(new GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>(cons, tempStates, s2));
					if (this.DEBUG)
						System.out.println("<-- BasicExpression.transformTo created cons-rule " + cons + "(" + tempStates + ") -> " + s2 + " -->");
				}
			}
		} else {
			if (this.DEBUG) System.out.println("<-- BasicExpression.transformTo call handleStart -->");
			final GenFTA<HedgeSymbol<G_Symbol>, HedgeState<G_State>> startT = handleStart(start, ha, sF);
			if (this.DEBUG) System.out.println("<-- BasicExpression.transformTo call handleStart returned -->");
			//TAStates.addAll(startT.getStates());
			TARules.addAll(startT.getRules());
			assert (startT.getFinalStates().size() == 1);
			final HedgeState<G_State> second = startT.getFinalStates().iterator().next();

			if (this.DEBUG) System.out.println("<-- BasicExpression.transformTo call handleEnd -->");
			final GenFTA<HedgeSymbol<G_Symbol>, HedgeState<G_State>> endT = handleEnd(second, end, ha, sF);
			if (this.DEBUG) System.out.println("<-- BasicExpression.transformTo call handleEnd returned -->");
			//TAStates.addAll(endT.getStates());
			TARules.addAll(endT.getRules());
			assert (endT.getFinalStates().size() == 1);
			final HedgeState<G_State> last = endT.getFinalStates().iterator().next();
			TAFinState.add(last);
		}
		if (this.DEBUG) System.out.println("<-- END: BasicExpression.transformTo -->");
		return new Container<G_Symbol, G_State>(TARules, TAFinState);
	}

	/**
	 * Create part of transformed Automaton, which handles the start states.
	 *
	 * @param start set of states to start from
	 * @param ha	HedgeAutomaton this expression belongs to
	 * @param sF	StateFactory for creating states
	 * @return transformed part
	 */
	private GenFTA<HedgeSymbol<G_Symbol>, HedgeState<G_State>> handleStart(final Iterable<HedgeState<G_State>> start, final HedgeAutomaton<G_Symbol, G_State> ha, final StateFactory sF) {
		if (this.DEBUG) System.out.println("<-- BEGIN: BasicExpression.handleStart -->");
		final HashSet<HedgeState<G_State>> TAStates = new HashSet<HedgeState<G_State>>();
		final HashSet<GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>> TARules = new HashSet<GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>>();
		final HedgeState<G_State> nState = HedgeStateCache.getState(states.listIterator().next());
		final HedgeState<G_State> lastState = new HedgeState<G_State>(null, sF.makeState());
		TAStates.add(lastState);
		final HedgeSymbol<G_Symbol> cons = HedgeSymbolCache.getConsSymbol(ha);

		for (final HedgeState<G_State> SI : start) {
			final LinkedList<HedgeState<G_State>> tempStates = new LinkedList<HedgeState<G_State>>();
			tempStates.add(SI);
			tempStates.add(nState);
			TARules.add(new GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>(cons, tempStates, lastState));
			if (this.DEBUG)
				System.out.println("<-- BasicExpression.transformTo created cons-rule " + cons + "(" + tempStates + ") -> " + lastState + " -->");
		}
		if (this.DEBUG) System.out.println("<-- END: BasicExpression.handleStart -->");
		return new GenFTA<HedgeSymbol<G_Symbol>, HedgeState<G_State>>(TARules, TAStates);
	}

	/**
	 * Creates part of transformed Automaton, which handles the end states.
	 *
	 * @param start state to start from
	 * @param end	 set of states to end in
	 * @param ha		HedgeAutomaton this expression belongs to
	 * @param sF		StateFactory for creating states
	 * @return transformed part
	 */
	private GenFTA<HedgeSymbol<G_Symbol>, HedgeState<G_State>> handleEnd(final HedgeState<G_State> start, final Iterable<HedgeState<G_State>> end, final HedgeAutomaton<G_Symbol, G_State> ha, final StateFactory sF) {
		if (this.DEBUG) System.out.println("<-- BEGIN: BasicExpression.handleEnd -->");
		//final HashSet<HedgeState<G_State>> TAStates = new HashSet<HedgeState<G_State>>();
		final HashSet<GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>> TARules = new HashSet<GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>>();
		final HashSet<HedgeState<G_State>> TAFinState = new HashSet<HedgeState<G_State>>();
		final HedgeSymbol<G_Symbol> cons = HedgeSymbolCache.getConsSymbol(ha);

		final Iterator<G_State> it = states.iterator();
		it.next();
		HedgeState<G_State> lastState = start;
		int i = states.size();
		HedgeState<G_State> nextState;
		LinkedList<HedgeState<G_State>> tempStates;
		for (; i > 2; i--) {
			nextState = HedgeStateCache.getState(it.next());
			tempStates = new LinkedList<HedgeState<G_State>>();
			tempStates.add(lastState);
			tempStates.add(nextState);
			lastState = new HedgeState<G_State>(null, sF.makeState());
			//TAStates.add(lastState);
			TARules.add(new GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>(cons, tempStates, lastState));
			if (this.DEBUG)
				System.out.println("<-- BasicExpression.transformTo created cons-rule " + cons + "(" + tempStates + ") -> " + lastState + " -->");
		}
		nextState = HedgeStateCache.getState(it.next());
		for (final HedgeState<G_State> endState : end) {
			tempStates = new LinkedList<HedgeState<G_State>>();
			tempStates.add(lastState);
			tempStates.add(nextState);
			TARules.add(new GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>(cons, tempStates, endState));
			if (this.DEBUG)
				System.out.println("<-- BasicExpression.transformTo created cons-rule " + cons + "(" + tempStates + ") -> " + endState + " -->");
			TAFinState.add(endState);
		}
		if (this.DEBUG) System.out.println("<-- END: BasicExpression.handleEnd -->");
		return new GenFTA<HedgeSymbol<G_Symbol>, HedgeState<G_State>>(TARules, TAFinState);
	}

	/**
	 * @see SingleExpression#isEmpty()
	 */
	@Override
	public boolean isEmpty() {
		return states.isEmpty();
	}

	/**
	 * Creates a String representation of the expression.
	 *
	 * @return String representation of the expression
	 */
	@Override
	public String toString() {
		final StringBuilder buffer = new StringBuilder();
		// buffer.append(" B").append(states.size()).append("> ");
		if (this.states.size() > 1) buffer.append("(");
		int count = 1;
		for (final G_State state : this.states) {
			buffer.append(state.toString());
			if (count < this.states.size())
				buffer.append(",");
			count++;
		}
		if (this.states.size() > 1) buffer.append(")");
		return buffer.toString();
	}

	/**
	 * Needed for optimized concatenation 
	 * ({@link ConcatExpression#makeOptimizedConcat}).
	 *
	 * @return list of states in this basic expression
	 */
	protected Collection<G_State> getStates() {
		return this.states;
	}

	/**
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(final Object exp) {
		if (exp == null) return false;
		if (exp == this) return true;
		if (!(exp instanceof BasicExpression<?, ?>)) return false;
		final BasicExpression<?, ?> b_exp = (BasicExpression<?, ?>) exp;
		return (b_exp == this) || (this.states.equals(b_exp.getStates()));
	}

	/**
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		return this.states != null ? states.hashCode() : 0;
	}
}
