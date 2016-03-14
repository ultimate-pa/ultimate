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

import de.uni_muenster.cs.sev.lethal.hedgeautomaton.internal.HedgeSymbolCache;
import de.uni_muenster.cs.sev.lethal.hedgeautomaton.internal.TreeCache;
import de.uni_muenster.cs.sev.lethal.states.BiState;
import de.uni_muenster.cs.sev.lethal.states.HedgeState;
import de.uni_muenster.cs.sev.lethal.states.NamedState;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.UnrankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.special.HedgeSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.tree.standard.StdTree;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAOps;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAProperties;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTACreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTAOps;
import de.uni_muenster.cs.sev.lethal.utils.Converter;
import de.uni_muenster.cs.sev.lethal.utils.IdentityConverter;
import de.uni_muenster.cs.sev.lethal.utils.Pair;

import java.util.*;

/**
 * This class offers the operations on the hedge automatons.
 *
 * @author Anton, Maria
 */
public final class HAOps {
	/**
	 * Decides whether a given hedge automaton can reduce a given tree to a
	 * final state.
	 * <p/>
	 * Uses {@link de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAProperties#decide(de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA, de.uni_muenster.cs.sev.lethal.tree.common.Tree)}
	 *
	 * @param ha				 the hedge automaton used to decide
	 * @param tree			 tree for the hedge automaton to decide
	 * @param <G_State>  type of states used in the hedge automaton
	 * @param <G_Symbol> type of the symbols used in the hedge automaton and the tree
	 * @return whether a given hedge automaton can reduce a given tree to a
	 *         final state.
	 */
	public static <G_State extends State, G_Symbol extends UnrankedSymbol> boolean decide(
			final HedgeAutomaton<G_Symbol, G_State> ha,
			final Tree<G_Symbol> tree) {
		final FTA<HedgeSymbol<G_Symbol>, HedgeState<G_State>, ? extends FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>>
				fta = ha.getTA();
		final Tree<HedgeSymbol<G_Symbol>> tree2 = TreeCache.getTree(tree);
		return FTAProperties.decide(fta, tree2);
	}

	/**
	 * Computes the set of states which a finite tree automaton A can reduce a
	 * given tree with ranked symbols to.
	 * <p/>
   * Uses {@link de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAProperties#accessibleStates(de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA, de.uni_muenster.cs.sev.lethal.tree.common.Tree)}
	 *
	 * @param ha				 the hedge automaton used to decide
	 * @param hedge			tree for the hedge automaton to decide
	 * @param <G_State>  type of states used in the hedge automaton
	 * @param <G_Symbol> type of the symbols used in the hedge automaton and the tree
	 * @return set of states which a finite tree automaton A can reduce a given
	 *         tree with ranked symbols to
	 */
	public static <G_State extends State, G_Symbol extends UnrankedSymbol> Set<G_State> accessibleStates(
			final HedgeAutomaton<G_Symbol, G_State> ha,
			final Tree<G_Symbol> hedge) {
		final FTA<HedgeSymbol<G_Symbol>, HedgeState<G_State>, ? extends FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>>
				fta = ha.getTA();
		final Tree<HedgeSymbol<G_Symbol>> tree = TreeCache.getTree(hedge);
		final Set<HedgeState<G_State>> set = FTAProperties.accessibleStates(
				fta, tree);
		set.retainAll(ha.getStates());
		return new HashSet<G_State>(HedgeState.extractOriginal(set));
	}

	/**
	 * Makes hedge automaton which recognizes the complement of the language of
	 * the given automaton
	 * <p/>
   * Uses {@link de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTAOps#complementAlphabet(de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA, java.util.Collection)}
	 *
	 * @param <G_State>  state type of incoming hedge automaton
	 * @param <G_Symbol> symbol type of incoming hedge automaton
	 * @param ha				 hedge automaton
	 * @return hedge automaton which recognizes the complement of the language
	 *         of the given automaton
	 */
	public static <G_State extends State, G_Symbol extends UnrankedSymbol> HedgeAutomaton<G_Symbol, NamedState<Set<HedgeState<G_State>>>> complement(
			final HedgeAutomaton<G_Symbol, G_State> ha) {
		final FTA<HedgeSymbol<G_Symbol>, HedgeState<G_State>, ? extends FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>>
				fta = ha.getTA();
		final Collection<HedgeSymbol<G_Symbol>> cons = new LinkedList<HedgeSymbol<G_Symbol>>();
		cons.add(HedgeSymbolCache.getConsSymbol(ha));
		final GenFTA<HedgeSymbol<G_Symbol>, NamedState<Set<HedgeState<G_State>>>>
				fta2 = GenFTAOps.complementAlphabet(fta, cons);
		final GenFTA<HedgeSymbol<G_Symbol>, HedgeState<NamedState<Set<HedgeState<G_State>>>>> fta3 = FTAOps
				.ftaConverter(
						fta2,
						new SetStateConverter<NamedState<Set<HedgeState<G_State>>>>(),
						new IdentityConverter<HedgeSymbol<G_Symbol>>(),
						new GenFTACreator<HedgeSymbol<G_Symbol>, HedgeState<NamedState<Set<HedgeState<G_State>>>>>());
		return new HedgeAutomaton<G_Symbol, NamedState<Set<HedgeState<G_State>>>>(
				fta3);
	}

  /**
   * Makes hedge automaton which recognizes the complement of the language of
   * the given automaton with respect to the union of its alphabet and some given
	 * alphabet
   * <p/>
   * Uses {@link de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTAOps#complementAlphabet(de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA, java.util.Collection)}
   *
   * @param <G_State>  state type of incoming hedge automaton
   * @param <G_Symbol> symbol type of incoming hedge automaton
   * @param ha				 hedge automaton
   * @param alphabet   alphabet with respect to which the automaton shall be completed
   * @return hedge automaton which recognizes the complement of the language
   *         of the given automaton
   */
	public static <G_State extends State, G_Symbol extends UnrankedSymbol> HedgeAutomaton<G_Symbol, NamedState<Set<HedgeState<G_State>>>> complementAlphabet(
			final HedgeAutomaton<G_Symbol, G_State> ha,
			final Collection<G_Symbol> alphabet) {
		final FTA<HedgeSymbol<G_Symbol>, HedgeState<G_State>, ? extends FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>>
				fta = ha.getTA();
		final Collection<HedgeSymbol<G_Symbol>> al = new LinkedList<HedgeSymbol<G_Symbol>>();
		al.add(HedgeSymbolCache.getConsSymbol(ha));
		for (final G_Symbol s : alphabet) {
			al.add(HedgeSymbolCache.getSymbol(s));
		}
		final GenFTA<HedgeSymbol<G_Symbol>, NamedState<Set<HedgeState<G_State>>>>
				fta2 = GenFTAOps.complementAlphabet(fta, al);
		final GenFTA<HedgeSymbol<G_Symbol>, HedgeState<NamedState<Set<HedgeState<G_State>>>>> fta3 = FTAOps
				.ftaConverter(
						fta2,
						new SetStateConverter<NamedState<Set<HedgeState<G_State>>>>(),
						new IdentityConverter<HedgeSymbol<G_Symbol>>(),
						new GenFTACreator<HedgeSymbol<G_Symbol>, HedgeState<NamedState<Set<HedgeState<G_State>>>>>());
		return new HedgeAutomaton<G_Symbol, NamedState<Set<HedgeState<G_State>>>>(
				fta3);
	}

	/**
	 * Makes a hedge automaton that recognizes the union of the languages of the
	 * given automata.
	 * <p/>
   * Uses {@link de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTAOps#union(de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA, de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA)}
	 *
	 * @param ha1				the first hedge automaton
	 * @param ha2				the second hedge automaton
	 * @param <G_State>  state type of first incoming hedge automaton
	 * @param <G_State2> state type of second incoming hedge automaton
	 * @param <G_Symbol> symbol type of incoming hedge automata
	 * @return hedge automaton that recognizes the union of the languages of the
	 *         given automata
	 */
	public static <G_State extends State, G_State2 extends State, G_Symbol extends UnrankedSymbol> HedgeAutomaton<G_Symbol, BiState<HedgeState<G_State>, HedgeState<G_State2>>> union(
			final HedgeAutomaton<G_Symbol, G_State> ha1,
			final HedgeAutomaton<G_Symbol, G_State2> ha2) {
		final FTA<HedgeSymbol<G_Symbol>, HedgeState<G_State>, ? extends FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>>
				fta = ha1.getTA();
		final FTA<HedgeSymbol<G_Symbol>, HedgeState<G_State2>, ? extends FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State2>>>
				fta2 = ha2.getTA();
		final GenFTA<HedgeSymbol<G_Symbol>, BiState<HedgeState<G_State>, HedgeState<G_State2>>> fta3 = GenFTAOps
				.union(fta, fta2);
		final GenFTA<HedgeSymbol<G_Symbol>, HedgeState<BiState<HedgeState<G_State>, HedgeState<G_State2>>>> fta5 = FTAOps
				.ftaConverter(
						fta3,
						new SetStateConverter<BiState<HedgeState<G_State>, HedgeState<G_State2>>>(),
						new IdentityConverter<HedgeSymbol<G_Symbol>>(),
						new GenFTACreator<HedgeSymbol<G_Symbol>, HedgeState<BiState<HedgeState<G_State>, HedgeState<G_State2>>>>());
		return new HedgeAutomaton<G_Symbol, BiState<HedgeState<G_State>, HedgeState<G_State2>>>(
				fta5);
	}

	/**
	 * Makes a hedge automaton that recognizes the intersection of the languages
	 * of the given automata
	 * <p/>
   * Uses {@link de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTAOps#intersectionBU(de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA, de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA)}
	 *
	 * @param ha1				the first hedge automaton
	 * @param ha2				the second hedge automaton
	 * @param <G_State>  state type of first incoming hedge automaton
	 * @param <G_State2> state type of second incoming hedge automaton
	 * @param <G_Symbol> symbol type of incoming hedge automata
	 * @return hedge automaton that recognizes the intersection of the languages
	 *         of the given automata
	 */
	public static <G_State extends State, G_Symbol extends UnrankedSymbol, G_State2 extends State> HedgeAutomaton<G_Symbol, NamedState<Pair<HedgeState<G_State>, HedgeState<G_State2>>>> intersection(
			final HedgeAutomaton<G_Symbol, G_State> ha1,
			final HedgeAutomaton<G_Symbol, G_State2> ha2) {
		final FTA<HedgeSymbol<G_Symbol>, HedgeState<G_State>, ? extends FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>>
				fta = ha1.getTA();
		final FTA<HedgeSymbol<G_Symbol>, HedgeState<G_State2>, ? extends FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State2>>>
				fta2 = ha2.getTA();
		final GenFTA<HedgeSymbol<G_Symbol>, NamedState<Pair<HedgeState<G_State>, HedgeState<G_State2>>>> fta3 = GenFTAOps
				.intersectionBU(fta, fta2);
		final GenFTA<HedgeSymbol<G_Symbol>, HedgeState<NamedState<Pair<HedgeState<G_State>, HedgeState<G_State2>>>>> fta4 = FTAOps
				.ftaConverter(
						fta3,
						new SetStateConverter<NamedState<Pair<HedgeState<G_State>, HedgeState<G_State2>>>>(),
						new IdentityConverter<HedgeSymbol<G_Symbol>>(),
						new GenFTACreator<HedgeSymbol<G_Symbol>, HedgeState<NamedState<Pair<HedgeState<G_State>, HedgeState<G_State2>>>>>());
		return new HedgeAutomaton<G_Symbol, NamedState<Pair<HedgeState<G_State>, HedgeState<G_State2>>>>(
				fta4);
	}

	/**
	 * Generates a hedge automaton that recognizes all hedges which are
	 * recognized by the first hedge automaton but not by the second hedge
	 * automaton.
	 * <p/>
   * Uses {@link de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTAOps#difference(de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA, de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA)}
	 *
	 * @param <G_State>  state type of first incoming hedge automaton
	 * @param <G_State2> state type of second incoming hedge automaton
	 * @param <G_Symbol> symbol type of incoming hedge automata
	 * @param ha1				first hedge automaton
	 * @param ha2				second hedge automaton
	 * @return hedge automaton that recognizes all hedges which are recognized
	 *         by the first hedge automaton but not by the second hedge
	 *         automaton.
	 */
	public static <G_State extends State, G_Symbol extends UnrankedSymbol, G_State2 extends State> HedgeAutomaton<G_Symbol, NamedState<Pair<HedgeState<G_State>, NamedState<Set<HedgeState<G_State2>>>>>> difference(
			final HedgeAutomaton<G_Symbol, G_State> ha1,
			final HedgeAutomaton<G_Symbol, G_State2> ha2) {
		final FTA<HedgeSymbol<G_Symbol>, HedgeState<G_State>, ? extends FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>>
				fta = ha1.getTA();
		final FTA<HedgeSymbol<G_Symbol>, HedgeState<G_State2>, ? extends FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State2>>>
				fta2 = ha2.getTA();
		final GenFTA<HedgeSymbol<G_Symbol>, NamedState<Pair<HedgeState<G_State>, NamedState<Set<HedgeState<G_State2>>>>>> fta3 = GenFTAOps
				.difference(fta, fta2);
		final GenFTA<HedgeSymbol<G_Symbol>, HedgeState<NamedState<Pair<HedgeState<G_State>, NamedState<Set<HedgeState<G_State2>>>>>>> fta4 = FTAOps
				.ftaConverter(
						fta3,
						new SetStateConverter<NamedState<Pair<HedgeState<G_State>, NamedState<Set<HedgeState<G_State2>>>>>>(),
						new IdentityConverter<HedgeSymbol<G_Symbol>>(),
						new GenFTACreator<HedgeSymbol<G_Symbol>, HedgeState<NamedState<Pair<HedgeState<G_State>, NamedState<Set<HedgeState<G_State2>>>>>>>());
		return new HedgeAutomaton<G_Symbol, NamedState<Pair<HedgeState<G_State>, NamedState<Set<HedgeState<G_State2>>>>>>(
				fta4);
	}

	/**
	 * Checks, whether the language of the given hedge automaton is empty.
	 * <p/>
	 * Uses {@link FTAProperties#emptyLanguage}
	 *
	 * @param <G_State>  state type of incoming hedge automaton
	 * @param <G_Symbol> symbol type of incoming hedge automaton
	 * @param ha				 hedge automaton
	 * @return true if the language of the given hedge automaton is empty
	 */
	public static <G_State extends State, G_Symbol extends UnrankedSymbol> boolean emptyLanguage(
			final HedgeAutomaton<G_Symbol, G_State> ha) {
		final FTA<HedgeSymbol<G_Symbol>, HedgeState<G_State>, ? extends FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>>
				fta = ha.getTA();
		return FTAProperties.emptyLanguage(fta);
	}

	/**
	 * Checks, whether the language of the given hedge automaton is finite.
	 * <p/>
	 * Uses {@link FTAProperties#finiteLanguage}
	 *
	 * @param <G_State>  state type of incoming hedge automaton
	 * @param <G_Symbol> symbol type of incoming hedge automaton
	 * @param ha				 hedge automaton
	 * @return true if the language of the given hedge automaton is finite
	 */
	public static <G_State extends State, G_Symbol extends UnrankedSymbol> boolean finiteLanguage(
			final HedgeAutomaton<G_Symbol, G_State> ha) {
		final FTA<HedgeSymbol<G_Symbol>, HedgeState<G_State>, ? extends FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>>
				fta = ha.getTA();
		return FTAProperties.finiteLanguage(fta);
	}

	/**
	 * Checks, whether the given hedge automata recognize the same language.
	 * <p/>
	 * Uses {@link HAOps#subsetLanguage}
	 *
	 * @param <G_State>  state type of first incoming hedge automaton
	 * @param <G_State2> state type of second incoming hedge automaton
	 * @param <G_Symbol> symbol type of incoming hedge automata
	 * @param ha1				first hedge automaton
	 * @param ha2				second hedge automaton
	 * @return true if the given hedge automata recognize the same language
	 */
	public static <G_State extends State, G_Symbol extends UnrankedSymbol, G_State2 extends State> boolean sameLanguage(
			final HedgeAutomaton<G_Symbol, G_State> ha1,
			final HedgeAutomaton<G_Symbol, G_State2> ha2) {
		return subsetLanguage(ha1, ha2) && subsetLanguage(ha2, ha1);
	}

	/**
	 * Checks, whether the language of the second hedge automaton contains the
	 * language of the first hedge automaton.
	 * <p/>
	 * Uses {@link HAOps#emptyLanguage}, {@link HAOps#difference}
	 *
	 * @param <G_State>  state type of first incoming hedge automaton
	 * @param <G_State2> state type of second incoming hedge automaton
	 * @param <G_Symbol> symbol type of incoming hedge automata
	 * @param ha1				first hedge automaton
	 * @param ha2				second hedge automaton
	 * @return true if the language of the second hedge automaton contains the
	 *         language of the first hedge automaton
	 */
	public static <G_State extends State, G_Symbol extends UnrankedSymbol, G_State2 extends State> boolean subsetLanguage(
			final HedgeAutomaton<G_Symbol, G_State> ha1,
			final HedgeAutomaton<G_Symbol, G_State2> ha2) {
		return emptyLanguage(difference(ha1, ha2));
	}

	/**
	 * Constructs a witness for the non-emptiness of a regular tree language.
	 * <p/>
   * Algorithm:<br>
	 * Creates a graph from the automaton, where the states know in which rules
	 * they are used and rules keep tracking of not reached states.
	 * <br>
	 * Once the collection of unreached states in a rule is empty, the
	 * destination state is informed of its reachablility with the information
	 * of the tree it recognizes. The state, once reached, can signal its rules
	 * the change. the signal itself causes the rule to check the reachability
	 * of its destination state (Recursion).
	 * <br>
	 * If a final state is reached, the tree it recognize is returned.
	 * <br>
	 * Once the graph is constructed, we need to go through the collection of
	 * the rules which have no source states. From each of them we try to get an
	 * example tree starting the recursion in the process. If the final state is
	 * reached, we get the example tree. If not, we return null.
	 *
	 * @param ha				 the hedge automaton to generate tree from
	 * @param <G_State>  type of states used in the hedge automaton
	 * @param <G_Symbol> type of the symbols used in the hedge automaton and the tree
	 * @return a tree the hedge automaton decide to true. null if there are
	 *         none.
	 */

	public static <G_State extends State, G_Symbol extends UnrankedSymbol> Tree<? extends UnrankedSymbol> constructTreeFrom(
			final HedgeAutomaton<G_Symbol, G_State> ha) {
		final FTA<HedgeSymbol<G_Symbol>, HedgeState<G_State>, ? extends FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>>>
				ta = ha.getTA();
		final HashMap<HedgeState<G_State>, G_St<G_State, G_Symbol>> stateMap = new HashMap<HedgeState<G_State>, G_St<G_State, G_Symbol>>();
		final Set<HedgeState<G_State>> finSt = ta.getFinalStates();

		final Collection<G_Rule<G_State, G_Symbol>> startRules = new HashSet<G_Rule<G_State, G_Symbol>>();

		for (final FTARule<HedgeSymbol<G_Symbol>, HedgeState<G_State>> rule : ta.getRules()) {
			final List<G_St<G_State, G_Symbol>> rule_states = new LinkedList<G_St<G_State, G_Symbol>>();
			G_St<G_State, G_Symbol> d_st = stateMap.get(rule.getDestState());
			if (d_st == null)
				d_st = new G_St<G_State, G_Symbol>(rule.getDestState(), finSt.contains(rule.getDestState()));
			stateMap.put(rule.getDestState(), d_st);
			for (final HedgeState<G_State> state : rule.getSrcStates()) {
				G_St<G_State, G_Symbol> g_st = stateMap.get(state);
				if (g_st == null) {
					g_st = new G_St<G_State, G_Symbol>(state, finSt
							.contains(state));
					stateMap.put(state, g_st);
				}
				stateMap.put(state, g_st);
				rule_states.add(g_st);
			}
			final G_Rule<G_State, G_Symbol> newRule = new G_Rule<G_State, G_Symbol>(
					rule.getSymbol(), rule_states, d_st);
			if (rule_states.isEmpty())
				startRules.add(newRule);
		}
		for (final G_Rule<G_State, G_Symbol> rule : startRules) {
			final Tree<HedgeSymbol<G_Symbol>> tree = rule.getTree();
			if (tree != null)
				return TreeCache.getHedge(tree);
		}
		return null;
	}

	/**
	 * Private constructor.
	 */
	private HAOps() {
		super();
	}

  /**
	 * Converter class used to pack the states in HedgeStates.
	 *
	 * @param <S>
	 * type of states to be packed in
	 */
	private static final class SetStateConverter<S extends State> implements
			Converter<S, HedgeState<S>> {

		/**
		 * Converts an object of type A into an object of type B.
		 *
		 * @param state object to be converted
		 * @return converted version of state
		 */
		@Override
		public HedgeState<S> convert(final S state) {
			return new HedgeState<S>(state, null);
		}
	}

	// /**
	// * makes an complete hedge automaton, which is equivalent to the given
	// hedge automaton
	// * <p/>
	// * uses StdFTAOps.complete
	// *
	// * @param ha given hedge automaton
	// * @param qbot dead-end state used as destination state for the completing
	// rules
	// * @param <G_State> state type of incoming hedge automaton
	// * @param <G_Symbol> symbol type of incoming hedge automaton
	// * @return complete hedge automaton
	// */
	// public static <G_State extends State, G_Symbol extends UnrankedSymbol>
	// HedgeAutomaton<G_Symbol,G_State>
	// complete(final HedgeAutomaton<G_Symbol,G_State> ha, final G_State qbot) {
	// GenFTA<HedgeSymbol<G_Symbol>,HedgeState<G_State>> fta = ha.getTA();
	// fta = GenFTAOps.complete(fta, HedgeStateCache.getState(qbot));
	// return new HedgeAutomaton<G_Symbol,G_State>(fta);
	// }
	//
	// /**
	// * Creates an equivalent deterministic hedge automaton
	// * <p/>
	// * uses StdFTAOps.determinize
	// *
	// * @param ha hedge automaton
	// * @param <G_State> state type of incoming hedge automaton
	// * @param <G_Symbol> symbol type of incoming hedge automaton
	// * @return deterministic hedge automaton
	// */
	// public static <G_State extends State, G_Symbol extends UnrankedSymbol>
	// HedgeAutomaton<G_Symbol,NamedState<Set<HedgeState<G_State>>>>
	// determinize(final HedgeAutomaton<G_Symbol,G_State> ha) {
	// final GenFTA<HedgeSymbol<G_Symbol>,HedgeState<G_State>> fta = ha.getTA();
	// final GenFTA<HedgeSymbol<G_Symbol>,NamedState<Set<HedgeState<G_State>>>>
	// fta2 = GenFTAOps.determinize(fta);
	// final
	// GenFTA<HedgeSymbol<G_Symbol>,HedgeState<NamedState<Set<HedgeState<G_State>>>>>
	// fta3 = FTAOps.ftaConverter(fta2,
	// new SetStateConverter<NamedState<Set<HedgeState<G_State>>>>(),
	// new IdentityConverter<HedgeSymbol<G_Symbol>>(),
	// new
	// GenFTACreator<HedgeSymbol<G_Symbol>,HedgeState<NamedState<Set<HedgeState<G_State>>>>>());
	// return new
	// HedgeAutomaton<G_Symbol,NamedState<Set<HedgeState<G_State>>>>(fta3);
	// }
	//
	// /**
	// * Generates an reduced hedge automaton, which is equivalent to the given
	// hedge automaton
	// * <p/>
	// * uses StdFTAOps.reduce
	// *
	// * @param ha hedge automaton
	// * @param <G_State> state type of incoming hedge automaton
	// * @param <G_Symbol> symbol type of incoming hedge automaton
	// * @return reduced hedge automaton
	// */
	// public static <G_State extends State, G_Symbol extends UnrankedSymbol>
	// HedgeAutomaton<G_Symbol,G_State> reduce(final
	// HedgeAutomaton<G_Symbol,G_State> ha) {
	// GenFTA<HedgeSymbol<G_Symbol>,HedgeState<G_State>> fta = ha.getTA();
	// fta = GenFTAOps.reduceBottomUp(fta);
	// return new HedgeAutomaton<G_Symbol,G_State>(fta);
	// }
	//
	// /**
	// * Generates an minimized hedge automaton, which is equivalent to the
	// given hedge automaton
	// * <p/>
	// * uses StdFTAOps.minimize
	// *
	// * @param ha hedge automaton
	// * @param qbot additional state needed for completion
	// * @param <G_State> state type of incoming hedge automaton
	// * @param <G_Symbol> symbol type of incoming hedge automaton
	// * @return minimized hedge automaton
	// */
	// public static <G_State extends State, G_Symbol extends UnrankedSymbol>
	// HedgeAutomaton<G_Symbol,NamedState<Set<HedgeState<G_State>>>>
	// minimize(final HedgeAutomaton<G_Symbol,G_State> ha, HedgeState<G_State>
	// qbot) {
	// final GenFTA<HedgeSymbol<G_Symbol>,HedgeState<G_State>> fta = ha.getTA();
	// final GenFTA<HedgeSymbol<G_Symbol>,NamedState<Set<HedgeState<G_State>>>>
	// fta2 = GenFTAOps.minimize(fta, qbot);
	// final
	// GenFTA<HedgeSymbol<G_Symbol>,HedgeState<NamedState<Set<HedgeState<G_State>>>>>
	// fta3 = FTAOps.ftaConverter(fta2,
	// new SetStateConverter<NamedState<Set<HedgeState<G_State>>>>(),
	// new IdentityConverter<HedgeSymbol<G_Symbol>>(),
	// new
	// GenFTACreator<HedgeSymbol<G_Symbol>,HedgeState<NamedState<Set<HedgeState<G_State>>>>>());
	// return new
	// HedgeAutomaton<G_Symbol,NamedState<Set<HedgeState<G_State>>>>(fta3);
	// }

	/**
	 * Represents a Rule. Assignes trees to states.
	 *
	 * @param <G_State>
	 * state type of the hedge automaton
	 * @param <G_Symbol>
	 * symbol type of the hedge automaton and the contructed tree
	 */
	private static class G_Rule<G_State extends State, G_Symbol extends UnrankedSymbol> {
		private final HedgeSymbol<G_Symbol> sym;
		private final LinkedList<G_St<G_State, G_Symbol>> rule;
		private final HashSet<G_St<G_State, G_Symbol>> unrec_rules;
		private final G_St<G_State, G_Symbol> dest;

		public G_Rule(final HedgeSymbol<G_Symbol> symbol,
									final Collection<G_St<G_State, G_Symbol>> states,
									final G_St<G_State, G_Symbol> dest) {
			super();
			this.sym = symbol;
			this.rule = new LinkedList<G_St<G_State, G_Symbol>>();
			this.unrec_rules = new HashSet<G_St<G_State, G_Symbol>>();
			this.dest = dest;
			for (final G_St<G_State, G_Symbol> state : states) {
				this.unrec_rules.add(state);
				this.rule.add(state);
				state.addRule(this);
			}
		}

		@Override
		public String toString() {
			return "G_Rule{" +
					"sym=" + this.sym +
					", rule=" + this.rule +
					", dest=" + this.dest +
					'}';
		}

		/**
		 * If all the source states have been reached, constructs a tree for the
		 * destination state. If the destination state is a final state, the
		 * example tree is finished and will be returned.
		 *
		 * @return returns the example tree if a final state was reached, null
		 *         otherwise
		 */
		public Tree<HedgeSymbol<G_Symbol>> getTree() {
			if (dest.isReached())
				return null;
			Tree<HedgeSymbol<G_Symbol>> toRet = null;
			if (unrec_rules.isEmpty()) {
				final List<Tree<HedgeSymbol<G_Symbol>>> sub = new LinkedList<Tree<HedgeSymbol<G_Symbol>>>();
				for (final G_St<G_State, G_Symbol> rule : this.rule)
					sub.add(rule.getTree());
				final Tree<HedgeSymbol<G_Symbol>> newTree = new StdTree<HedgeSymbol<G_Symbol>>(
						this.sym, sub);
				if (dest.isFinal())
					return newTree;
				toRet = dest.setTree(newTree, this);
			}
			return toRet;
		}

		/**
		 * Handles the signal indicating a reached state.
		 *
		 * @param state the state which was reached
		 */
		public void signal(final G_St<G_State, G_Symbol> state) {
			assert unrec_rules.contains(state);
			unrec_rules.remove(state);
		}
	}

	/**
	 * Represents a state. Used to store additional information about a state.
	 *
	 * @param <G_State>
	 * state type of the hedge automaton
	 * @param <G_Symbol>
	 * symbol type of the hedge automaton and the contructed tree
	 */
	private static class G_St<G_State extends State, G_Symbol extends UnrankedSymbol> {
		// tree this state recognize
		private Tree<HedgeSymbol<G_Symbol>> tree;
		// the rules containing this state
		private final List<G_Rule<G_State, G_Symbol>> rules;
		// the state this class represents
		private final HedgeState<G_State> state;
		// whether this state is a final state
		private final boolean finalSt;

		public Tree<HedgeSymbol<G_Symbol>> getTree() {
			return this.tree;
		}

		public boolean isReached() {
			return this.tree != null;
		}

		public Tree<HedgeSymbol<G_Symbol>> setTree(
				final Tree<HedgeSymbol<G_Symbol>> tree,
				final G_Rule<G_State, G_Symbol> source) {
			this.tree = tree;
			Tree<HedgeSymbol<G_Symbol>> toRet = null;
			for (final G_Rule<G_State, G_Symbol> rule : this.rules) {
				rule.signal(this);
				if (rule != source) {
					toRet = rule.getTree();
					if (toRet != null)
						return toRet;
				}
			}
			return toRet;
		}

		public boolean isFinal() {
			return this.finalSt;
		}

		public G_St(final HedgeState<G_State> state, final boolean isFinal) {
			super();
			this.state = state;
			this.finalSt = isFinal;
			this.rules = new LinkedList<G_Rule<G_State, G_Symbol>>();
		}

		@Override
		public String toString() {
			return "G_St{" +
					"state=" + this.state +
					", finalSt=" + this.finalSt +
					'}';
		}

		public void addRule(final G_Rule<G_State, G_Symbol> rule) {
			this.rules.add(rule);
		}

		/**
		 * @see java.lang.Object#equals(java.lang.Object)
		 */
		@Override
		public boolean equals(final Object o) {
			if (this == o)
				return true;
			if (o == null || getClass() != o.getClass())
				return false;
			final G_St g_st = (G_St) o;
			return !(this.state != null ? !this.state.equals(g_st.state)
					: g_st.state != null);
		}

		/**
		 * @see java.lang.Object#hashCode()
		 */
		@Override
		public int hashCode() {
			return this.state.hashCode();
		}
	}
}
