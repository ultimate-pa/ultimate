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

import java.util.*;

/**
 * This class is a transformer and a cache for transformation of RegularExpression into a finite tree automaton.<br>
 * This class caches the transformed RegularExpressions and initiates transformation if requested expression is not cached.
 *
 * @author Anton, Maria
 */
final class ExpressionCache {

	private static final boolean DEBUG = false;

	private ExpressionCache() {
		super();
	}

	/**
	 * Contains States which represents recognition of k repetitions of an expression.
	 *
	 * @param <G_State> state type of this entry
	 */
	private static class HashEntry<G_State extends State> {
		/**the State represents recognition of k to infinite repeats of the expression*/
		public HedgeState<G_State> sInf;
		// the State represents recognition of exactly k repeats of the expression
		// has to be multiple since f.e. a|b has 2 ending states:
		//   q_a for a and q_b for b. so {q_a, q_b} represents states where a or b are recognized.
		public final Collection<HedgeState<G_State>> sEnd;

		public HashEntry(final Collection<HedgeState<G_State>> end) {
			super();
			this.sEnd = end;
			this.sInf = null;
		}
	}

	/**
	 * THE CACHE
	 * <p/>
	 * Contains transformed expressions.
	 * <p/>
	 * Each single expression has a set of sets with starting States, where the expression is starting from.
	 * Since this expression is starting from somewhere, we have to distinguish the starting states or we
	 * loose the information.
	 * Since an expression can end in multiple states, we need to use a set of states for the differentiation
	 * so each set of starting States has an Array of ending States.
	 * The n-th entry on ArrayList contains the ending states for an finite tree automaton which recognize n-th repetition
	 * of the expression and the ending state, where the automaton recognize n to infinite loop of the expression
	 * we cannot distinguish all the combinations in a infinite loop, so one recognizing State is enough.
	 *
	 * @param <G_State> state type of expressions stored in cache
	 * @param <G_Symbol>  symbol type of expressions stored in cache
	 */
	private static class cache_int1<G_Symbol extends UnrankedSymbol, G_State extends State> extends WeakHashMap<SingleExpression<G_Symbol, G_State>, cache_int2<G_State>> {
	}

	private static class cache_int2<G_State extends State> extends WeakHashMap<Collection<HedgeState<G_State>>, ArrayList<HashEntry<G_State>>> {
	}

	private static final Map<HedgeAutomaton<? extends UnrankedSymbol, ? extends State>, cache_int1<? extends UnrankedSymbol, ? extends State>> cache =
			Collections.synchronizedMap(new IdentityHashMap<HedgeAutomaton<? extends UnrankedSymbol, ? extends State>, cache_int1<? extends UnrankedSymbol, ? extends State>>());

	/**
	 * Transforms the RegularExpression 'exp' into a finite tree automaton starting from 'start'. <br>
	 * The resulting finite tree automaton contains only the part of the finite tree automaton, which was not generated in previous calls.
	 * For example, if f exp^2 was generated previously and exp^3 is requested, only the exp^2->exp^3 part is returned.
	 * If exp^2 was generated previously and exp is requested, the finite tree automaton will contain no states nor rules.
	 * This affects states and rules, while all matching final states are returned. 
	 *
	 * @param <G_State>   state type of expression to be transformed
	 * @param <G_Symbol>   symbol type of expression to be transformed
	 * @param start where the transformed expression should start from
	 * @param exp	 the expression to be transformed
	 * @param ha		the HedgeAutomaton the expression is from
	 * @param sF		StateFactory for creating states
	 * @return FTA containing generated Rules and States and appropriate final States
	 */
	@SuppressWarnings("unchecked")
	public static <G_Symbol extends UnrankedSymbol, G_State extends State>
	Container<G_Symbol, G_State> transformExp(final Collection<HedgeState<G_State>> start, final RegularExpression<G_Symbol, G_State> exp, final HedgeAutomaton<G_Symbol, G_State> ha, final StateFactory sF) {

		final cache_int1<G_Symbol, G_State> cache_entry;
		if (cache.containsKey(ha)) {
			cache_entry = (cache_int1<G_Symbol, G_State>) cache.get(ha);
		} else {
			cache_entry = new cache_int1<G_Symbol, G_State>();
			ExpressionCache.cache.put(ha, cache_entry);
		}
		if (DEBUG) System.out.println("<-- BEGIN: ExpressionCache.transformExp -->");
		final int iLow = exp.getLow();
		final int iHigh = exp.getHigh();
		if (DEBUG) {
			System.out.print("<-- ExpressionCache.transformExp got expression: ");
			System.out.print(exp);
			System.out.println(" -->");
		}
		// extract the SingleExpression to check in the cache
		final SingleExpression<G_Symbol, G_State> sExp = exp.getExpression();
		if (DEBUG) {
			System.out.print("<-- ExpressionCache.transformExp with SingleExpression: ");
			System.out.print(sExp);
			System.out.println(" (" + iLow + "," + iHigh + ") -->");
		}
		// get the cache entry for the SingleExpression or generate new one
		final cache_int2<G_State> expressionEntry;
		if (!cache_entry.containsKey(sExp)) {
			if (DEBUG) System.out.println("<-- ExpressionCache.transformExp SingleExpression not found -->");
			expressionEntry = new cache_int2<G_State>();
			cache_entry.put(sExp, expressionEntry);
		} else {
			if (DEBUG) System.out.println("<-- ExpressionCache.transformExp SingleExpression found -->");
			expressionEntry = cache_entry.get(sExp);
		}
		if (DEBUG) {
			System.out.print("<-- ExpressionCache.transformExp got start states: ");
			System.out.print(start);
			System.out.println(" -->");
		}
		// get the cache entry for the given starting States or generate new one
		final ArrayList<HashEntry<G_State>> list;
		if (!expressionEntry.containsKey(start)) {
			if (DEBUG) System.out.println("<-- ExpressionCache.transformExp start states not found -->");
			list = new ArrayList<HashEntry<G_State>>();
			expressionEntry.put(start, list);
		} else {
			if (DEBUG) System.out.println("<-- ExpressionCache.transformExp start states found -->");
			list = expressionEntry.get(start);
		}
		Collection<HedgeState<G_State>> lastStates;
		final Collection<HedgeState<G_State>> TAFinStates = new HashSet<HedgeState<G_State>>();
		final Collection<GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>> TARules = new HashSet<GenFTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>>();
		//final Collection<HedgeState<G_State>> TAStates = new HashSet<HedgeState<G_State>>();
		// if the entry is new, add ending States for 0 loops
		// get the ending States of the last generated loop
		if (list.isEmpty()) {
			if (DEBUG) System.out.println("<-- ExpressionCache.transformExp list of end states is empty -->");
			list.add(new HashEntry(start));
			lastStates = start;
		} else {
			lastStates = list.get(list.size() - 1).sEnd;
		}
		final int last = Math.max(iLow, iHigh);
		// generate Rules and States to cover requested amount of loops
		Container<G_Symbol, G_State> temp;
		while (list.size() < last + 1) {
			if (DEBUG) System.out.println("<-- ExpressionCache.transformExp create new round for " + list.size() + " -->");
			temp = sExp.transform(lastStates, ha, sF);
			lastStates = temp.getFinalStates();
			list.add(new HashEntry<G_State>(lastStates));
			// collect the generated Rules and States
			//TAStates.addAll(temp.getStates());
			TARules.addAll(temp.getRules());
		}
		// if request contains an infinite loop, generate one if needed
		if (iHigh < 0) {
			if (DEBUG) System.out.println("<-- ExpressionCache.transformExp infinite high border detected -->");
			if (list.get(iLow).sInf == null) {
				if (DEBUG)
					System.out.println("<-- ExpressionCache.transformExp end state for infinite border, low = " + iLow + " is not set -->");
				final HedgeState<G_State> inf = new HedgeState<G_State>(null, sF.makeState());
				final Collection<HedgeState<G_State>> infSet = new HashSet<HedgeState<G_State>>();
				infSet.add(inf);
				if (DEBUG)
					System.out.println("<-- ExpressionCache.transformExp create a fork to end state of infinite loop -->");
				temp = exp.transformTo(list.get(iLow).sEnd, infSet, ha, sF);
				if (DEBUG) System.out.println("<-- ExpressionCache.transformExp fork created -->");
				//TAStates.addAll(temp.getStates());
				TARules.addAll(temp.getRules());
				if (DEBUG) System.out.println("<-- ExpressionCache.transformExp create infinite loop -->");
				temp = exp.transformTo(infSet, infSet, ha, sF);
				if (DEBUG) System.out.println("<-- ExpressionCache.transformExp loop created -->");
				//TAStates.addAll(temp.getStates());
				TARules.addAll(temp.getRules());
				list.get(iLow).sInf = inf;
			}
			// add the State, recognizing infinite loop, to final States
			TAFinStates.add(list.get(iLow).sInf);
			if (DEBUG)
				System.out.println("<-- ExpressionCache.transformExp end state for infinite border, low = " + iLow + " is " + list.get(iLow).sInf + " -->");
		}
		assert (list.size() >= iLow);
		assert (list.size() >= iHigh);
		// add all recognizing States from 'low' to 'high' loops to final States
		for (int i = iLow; i <= last; i++) {
			if (DEBUG) System.out.println("<-- ExpressionCache.transformExp add end state for low = " + i + " -->");
			TAFinStates.addAll(list.get(i).sEnd);
		}
		if (DEBUG) System.out.println("<-- END: ExpressionCache.transformExp -->");
		return new Container<G_Symbol, G_State>(TARules, TAFinStates);
	}

	/**
	 * Removes a hedge automaton from the cache.
	 * 
	 * @param ha hedge automaton to remove
	 */
	public static void clear(final HedgeAutomaton<? extends UnrankedSymbol, ? extends State> ha) {
		cache.remove(ha);
	}
}
