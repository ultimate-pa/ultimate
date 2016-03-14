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
public final class EasyHAOps {
	/**
	 * Decides whether a given hedge automaton can reduce a given tree to a
	 * final state.
	 * <p/>
	 * Uses {@link de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAProperties#decide(de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA, de.uni_muenster.cs.sev.lethal.tree.common.Tree)}
	 *
	 * @param ha	 the hedge automaton used to decide
	 * @param tree tree for the hedge automaton to decide
	 * @return whether a given hedge automaton can reduce a given tree to a
	 *         final state.
	 */
	public static boolean decide(
			final HedgeAutomaton<UnrankedSymbol, State> ha,
			final Tree<UnrankedSymbol> tree) {
		final FTA<HedgeSymbol<UnrankedSymbol>, HedgeState<State>, ? extends FTARule<HedgeSymbol<UnrankedSymbol>, HedgeState<State>>>
		fta = ha.getTA();
		final Tree<HedgeSymbol<UnrankedSymbol>> tree2 = TreeCache.getTree(tree);
		return FTAProperties.decide(fta, tree2);
	}

	/**
	 * Computes the set of states which a finite tree automaton A can reduce a
	 * given tree with ranked symbols to.
	 * <p/>
	 * Uses {@link de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAProperties#accessibleStates(de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA, de.uni_muenster.cs.sev.lethal.tree.common.Tree)}
	 *
	 * @param ha		the hedge automaton used to decide
	 * @param hedge tree for the hedge automaton to decide
	 * @return set of states which a finite tree automaton A can reduce a given
	 *         tree with ranked symbols to
	 */
	public static Set<State> accessibleStates(
			final HedgeAutomaton<UnrankedSymbol, State> ha,
			final Tree<UnrankedSymbol> hedge) {
		final FTA<HedgeSymbol<UnrankedSymbol>, HedgeState<State>, ? extends FTARule<HedgeSymbol<UnrankedSymbol>, HedgeState<State>>>
		fta = ha.getTA();
		final Tree<HedgeSymbol<UnrankedSymbol>> tree = TreeCache.getTree(hedge);
		final Set<HedgeState<State>> set = FTAProperties.accessibleStates(
				fta, tree);
		set.retainAll(ha.getStates());
		return new HashSet<State>(HedgeState.extractOriginal(set));
	}

	/**
	 * Makes a hedge automaton which recognizes the complement of the language of
	 * the given automaton.
	 * <p/>
	 * Uses {@link de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTAOps#complementAlphabet(de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA, java.util.Collection)}
	 *
	 * @param ha hedge automaton
	 * @return hedge automaton which recognizes the complement of the language
	 *         of the given automaton
	 */
	public static EasyHedgeAutomaton complement(
			final HedgeAutomaton<UnrankedSymbol, State> ha) {
		final FTA<HedgeSymbol<UnrankedSymbol>, HedgeState<State>, ? extends FTARule<HedgeSymbol<UnrankedSymbol>, HedgeState<State>>>
		fta = ha.getTA();
		final Collection<HedgeSymbol<UnrankedSymbol>> cons = new LinkedList<HedgeSymbol<UnrankedSymbol>>();
		cons.add(HedgeSymbolCache.getConsSymbol(ha));
		final GenFTA<HedgeSymbol<UnrankedSymbol>, NamedState<Set<HedgeState<State>>>> fta2 = GenFTAOps
		.complementAlphabet(fta, cons);
		final GenFTA<HedgeSymbol<UnrankedSymbol>, HedgeState<State>> fta3 = FTAOps
		.ftaConverter(
				fta2,
				new SetConverter(),
				new IdentityConverter<HedgeSymbol<UnrankedSymbol>>(),
				new GenFTACreator<HedgeSymbol<UnrankedSymbol>, HedgeState<State>>());
		return new EasyHedgeAutomaton(fta3);
	}

	/**
	 * Makes hedge automaton which recognizes the complement of the language of
	 * the given automaton with respect to the union of its alphabet and some given
	 * alphabet.
	 * <p/>
	 * Uses {@link de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTAOps#complementAlphabet(de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA, java.util.Collection)}
	 *
	 * @param ha				 hedge automaton
	 * @param alphabet   alphabet with respect to which the automaton shall be completed
	 * @return hedge automaton which recognizes the complement of the language
	 *         of the given automaton
	 */
	public static EasyHedgeAutomaton complementAlphabet(
			final HedgeAutomaton<UnrankedSymbol, State> ha,
			final Collection<UnrankedSymbol> alphabet) {
		final FTA<HedgeSymbol<UnrankedSymbol>, HedgeState<State>, ? extends FTARule<HedgeSymbol<UnrankedSymbol>, HedgeState<State>>>
		fta = ha.getTA();
		final Collection<HedgeSymbol<UnrankedSymbol>> al = new LinkedList<HedgeSymbol<UnrankedSymbol>>();
		al.add(HedgeSymbolCache.getConsSymbol(ha));
		for (final UnrankedSymbol s : alphabet) {
			al.add(HedgeSymbolCache.getSymbol(s));
		}
		final GenFTA<HedgeSymbol<UnrankedSymbol>, NamedState<Set<HedgeState<State>>>> fta2 = GenFTAOps
		.complementAlphabet(fta, al);
		final GenFTA<HedgeSymbol<UnrankedSymbol>, HedgeState<State>> fta3 = FTAOps
		.ftaConverter(
				fta2,
				new SetConverter(),
				new IdentityConverter<HedgeSymbol<UnrankedSymbol>>(),
				new GenFTACreator<HedgeSymbol<UnrankedSymbol>, HedgeState<State>>());
		return new EasyHedgeAutomaton(fta3);
	}

	private static class SetConverter implements Converter<NamedState<Set<HedgeState<State>>>, HedgeState<State>> {

		/**
		 * Converts an object of type A into an object of type B.
		 *
		 * @param setNamedState object to be converted
		 * @return converted version of the given object
		 */
		@Override
		public HedgeState<State> convert(final NamedState<Set<HedgeState<State>>> setNamedState) {
			final Set<HedgeState<State>> s = setNamedState.getName();
			final Set<State> r_g = new HashSet<State>();
			for (final HedgeState<State> state : s) {
				if (state.isPacked())
					r_g.add(state.getOriginal());
				else
					r_g.add(state.getGenerated());
			}
			final NamedState<Set<State>> r_s = new NamedState<Set<State>>(r_g);
			return new HedgeState<State>(r_s, r_s);
		}
	}

	/**
	 * Makes a hedge automaton that recognizes the union of the languages of the
	 * given automata
	 * <p/>
	 * Uses {@link de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTAOps#union(de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA, de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA)}
	 *
	 * @param ha1 the first hedge automaton
	 * @param ha2 the second hedge automaton
	 * @return hedge automaton that recognizes the union of the languages of the
	 *         given automata
	 */
	public static EasyHedgeAutomaton union(
			final HedgeAutomaton<UnrankedSymbol, State> ha1,
			final HedgeAutomaton<UnrankedSymbol, State> ha2) {
		final FTA<HedgeSymbol<UnrankedSymbol>, HedgeState<State>, ? extends FTARule<HedgeSymbol<UnrankedSymbol>, HedgeState<State>>>
		fta = ha1.getTA();
		final FTA<HedgeSymbol<UnrankedSymbol>, HedgeState<State>, ? extends FTARule<HedgeSymbol<UnrankedSymbol>, HedgeState<State>>>
		fta2 = ha2.getTA();
		final GenFTA<HedgeSymbol<UnrankedSymbol>, BiState<HedgeState<State>, HedgeState<State>>> fta3 = GenFTAOps
		.union(fta, fta2);
		final GenFTA<HedgeSymbol<UnrankedSymbol>, HedgeState<State>> fta5 = FTAOps
		.ftaConverter(
				fta3,
				new BiConverter(),
				new IdentityConverter<HedgeSymbol<UnrankedSymbol>>(),
				new GenFTACreator<HedgeSymbol<UnrankedSymbol>, HedgeState<State>>());
		return new EasyHedgeAutomaton(fta5);
	}

	private static class BiConverter implements Converter<BiState<HedgeState<State>, HedgeState<State>>, HedgeState<State>> {

		/**
		 * Converts an object of type A into an object of type B.
		 *
		 * @param State object to be converted
		 * @return converted version of the given object
		 */
		@Override
		public HedgeState<State> convert(final BiState<HedgeState<State>, HedgeState<State>> State) {
			if (State.isFirstKind()) return new HedgeState<State>(State.asFirstKind(), State.asFirstKind());
			else return new HedgeState<State>(State.asSecondKind(), State.asSecondKind());
		}
	}

	/**
	 * Makes a hedge automaton that recognizes the intersection of the languages
	 * of the given automata
	 * <p/>
	 * Uses {@link de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTAOps#intersectionBU(de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA, de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA)}
	 *
	 * @param ha1 the first hedge automaton
	 * @param ha2 the second hedge automaton
	 * @return hedge automaton that recognizes the intersection of the languages
	 *         of the given automata
	 */
	public static EasyHedgeAutomaton intersection(
			final HedgeAutomaton<UnrankedSymbol, State> ha1,
			final HedgeAutomaton<UnrankedSymbol, State> ha2) {
		final FTA<HedgeSymbol<UnrankedSymbol>, HedgeState<State>, ? extends FTARule<HedgeSymbol<UnrankedSymbol>, HedgeState<State>>>
		fta = ha1.getTA();
		final FTA<HedgeSymbol<UnrankedSymbol>, HedgeState<State>, ? extends FTARule<HedgeSymbol<UnrankedSymbol>, HedgeState<State>>>
		fta2 = ha2.getTA();
		final GenFTA<HedgeSymbol<UnrankedSymbol>, NamedState<Pair<HedgeState<State>, HedgeState<State>>>> fta3 = GenFTAOps
		.intersectionBU(fta, fta2);
		final GenFTA<HedgeSymbol<UnrankedSymbol>, HedgeState<State>> fta4 = FTAOps
		.ftaConverter(
				fta3,
				new PairConverter(),
				new IdentityConverter<HedgeSymbol<UnrankedSymbol>>(),
				new GenFTACreator<HedgeSymbol<UnrankedSymbol>, HedgeState<State>>());
		return new EasyHedgeAutomaton(fta4);
	}

	private static class PairConverter implements Converter<NamedState<Pair<HedgeState<State>, HedgeState<State>>>, HedgeState<State>> {

		/**
		 * Converts an object of type A into an object of type B.
		 *
		 * @param setNamedState object to be converted
		 * @return converted version of the given object
		 */
		@Override
		public HedgeState<State> convert(final NamedState<Pair<HedgeState<State>, HedgeState<State>>> setNamedState) {
			final Pair<HedgeState<State>, HedgeState<State>> s = setNamedState.getName();
			final State s1;
			if (s.getFirst().isPacked())
				s1 = s.getFirst().getOriginal();
			else
				s1 = s.getFirst().getGenerated();
			final State s2;
			if (s.getSecond().isPacked())
				s2 = s.getSecond().getOriginal();
			else
				s2 = s.getSecond().getGenerated();
			final Pair<State, State> r_g = new Pair<State, State>(s1, s2);
			final NamedState<Pair<State, State>> r_s = new NamedState<Pair<State, State>>(r_g);
			return new HedgeState<State>(r_s, r_s);
		}
	}

	/**
	 * Generates a hedge automaton that recognizes all hedges which are
	 * recognized by the first hedge automaton but not by the second hedge
	 * automaton.
	 * <p/>
	 * Uses {@link de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTAOps#difference(de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA, de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA)}
	 *
	 * @param ha1 first hedge automaton
	 * @param ha2 second hedge automaton
	 * @return hedge automaton that recognizes all hedges which are recognized
	 *         by the first hedge automaton but not by the second hedge
	 *         automaton.
	 */
	public static EasyHedgeAutomaton difference(
			final HedgeAutomaton<UnrankedSymbol, State> ha1,
			final HedgeAutomaton<UnrankedSymbol, State> ha2) {
		final FTA<HedgeSymbol<UnrankedSymbol>, HedgeState<State>, ? extends FTARule<HedgeSymbol<UnrankedSymbol>, HedgeState<State>>>
		fta = ha1.getTA();
		final FTA<HedgeSymbol<UnrankedSymbol>, HedgeState<State>, ? extends FTARule<HedgeSymbol<UnrankedSymbol>, HedgeState<State>>>
		fta2 = ha2.getTA();
		final GenFTA<HedgeSymbol<UnrankedSymbol>, NamedState<Pair<HedgeState<State>, NamedState<Set<HedgeState<State>>>>>> fta3 = GenFTAOps
		.difference(fta, fta2);
		final GenFTA<HedgeSymbol<UnrankedSymbol>, HedgeState<State>> fta4 = FTAOps
		.ftaConverter(
				fta3,
				new PairSetConverter(),
				new IdentityConverter<HedgeSymbol<UnrankedSymbol>>(),
				new GenFTACreator<HedgeSymbol<UnrankedSymbol>, HedgeState<State>>());
		return new EasyHedgeAutomaton(fta4);
	}

	private static class PairSetConverter implements Converter<NamedState<Pair<HedgeState<State>, NamedState<Set<HedgeState<State>>>>>, HedgeState<State>> {

		/**
		 * Converts an object of type A into an object of type B.
		 *
		 * @param pairNamedState object to be converted
		 * @return converted version of the given object
		 */
		@Override
		public HedgeState<State> convert(final NamedState<Pair<HedgeState<State>, NamedState<Set<HedgeState<State>>>>> pairNamedState) {
			final Pair<HedgeState<State>, NamedState<Set<HedgeState<State>>>> pair = pairNamedState.getName();
			final State s1;
			if (pair.getFirst().isPacked()) s1 = pair.getFirst().getOriginal();
			else s1 = pair.getFirst().getGenerated();
			final Set<HedgeState<State>> s = pair.getSecond().getName();
			final Set<State> r_g = new HashSet<State>();
			for (final HedgeState<State> state : s) {
				if (state.isPacked())
					r_g.add(state.getOriginal());
				else
					r_g.add(state.getGenerated());
			}
			final State s2 = new NamedState<Set<State>>(r_g);
			final Pair<State, State> r_p = new Pair<State, State>(s1, s2);
			final NamedState<Pair<State, State>> r_s = new NamedState<Pair<State, State>>(r_p);
			return new HedgeState<State>(r_s, r_s);
		}
	}

	/**
	 * Checks, whether the language of the given hedge automaton is empty
	 * <p/>
	 * Uses {@link de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAProperties#emptyLanguage}
	 *
	 * @param ha hedge automaton
	 * @return true if the language of the given hedge automaton is empty
	 */
	public static boolean emptyLanguage(
			final HedgeAutomaton<UnrankedSymbol, State> ha) {
		final FTA<HedgeSymbol<UnrankedSymbol>, HedgeState<State>, ? extends FTARule<HedgeSymbol<UnrankedSymbol>, HedgeState<State>>>
		fta = ha.getTA();
		return FTAProperties.emptyLanguage(fta);
	}

	/**
	 * Checks, whether the language of the given hedge automaton is finite
	 * <p/>
	 * Uses {@link de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAProperties#finiteLanguage}
	 *
	 * @param ha hedge automaton
	 * @return true if the language of the given hedge automaton is finite
	 */
	public static boolean finiteLanguage(
			final HedgeAutomaton<UnrankedSymbol, State> ha) {
		final FTA<HedgeSymbol<UnrankedSymbol>, HedgeState<State>, ? extends FTARule<HedgeSymbol<UnrankedSymbol>, HedgeState<State>>>
		fta = ha.getTA();
		return FTAProperties.finiteLanguage(fta);
	}

	/**
	 * Checks, whether the given hedge automata recognize the same language
	 * <p/>
	 * Uses {@link EasyHAOps#subsetLanguage(HedgeAutomaton, HedgeAutomaton)}
	 *
	 * @param ha1 first hedge automaton
	 * @param ha2 second hedge automaton
	 * @return true if the given hedge automata recognize the same language
	 */
	public static boolean sameLanguage(
			final HedgeAutomaton<UnrankedSymbol, State> ha1,
			final HedgeAutomaton<UnrankedSymbol, State> ha2) {
		return subsetLanguage(ha1, ha2) && subsetLanguage(ha2, ha1);
	}

	/**
	 * Checks, whether the language of the second hedge automaton contains the
	 * language of the first hedge automaton
	 * <p/>
	 * Uses {@link EasyHAOps#emptyLanguage}, {@link EasyHAOps#difference}
	 *
	 * @param ha1 first hedge automaton
	 * @param ha2 second hedge automaton
	 * @return true if the language of the second hedge automaton contains the
	 *         language of the first hedge automaton
	 */
	public static boolean subsetLanguage(
			final HedgeAutomaton<UnrankedSymbol, State> ha1,
			final HedgeAutomaton<UnrankedSymbol, State> ha2) {
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
	 * of the tree it recognizes. the state, once reached, can signal its rules
	 * the change. the signal itself causes the rule to check the reachability
	 * of its destination state (Recursion).
	 * <br>
	 * If a final state is reached, the tree it recognize is returned.
	 * <br>
	 * Once the graph is constructed, we need to go through the collection of
	 * the rules which have no source states. From each of them we try to get an
	 * example tree starting the recursion in the process. If the final state is
	 * reached, we get the example tree. Otherwise we return null.
	 *
	 * @param ha the hedge automaton to generate tree from
	 * @return a tree the hedge automaton decide to true. null if there are
	 *         none.
	 */

	public static Tree<? extends UnrankedSymbol> constructTreeFrom(
			final HedgeAutomaton<UnrankedSymbol, State> ha) {
		final FTA<HedgeSymbol<UnrankedSymbol>, HedgeState<State>, ? extends FTARule<HedgeSymbol<UnrankedSymbol>, HedgeState<State>>>
		ta = ha.getTA();
		final HashMap<HedgeState<State>, G_St> stateMap = new HashMap<HedgeState<State>, G_St>();
		final Set<HedgeState<State>> finSt = ta.getFinalStates();

		final Collection<G_Rule> startRules = new HashSet<G_Rule>();

		for (final FTARule<HedgeSymbol<UnrankedSymbol>, HedgeState<State>> rule : ta.getRules()) {
			final List<G_St> rule_states = new LinkedList<G_St>();
			G_St d_st = stateMap.get(rule.getDestState());
			if (d_st == null)
				d_st = new G_St(rule.getDestState(), finSt.contains(rule.getDestState()));
			stateMap.put(rule.getDestState(), d_st);
			for (final HedgeState<State> state : rule.getSrcStates()) {
				G_St g_st = stateMap.get(state);
				if (g_st == null) {
					g_st = new G_St(state, finSt.contains(state));
					stateMap.put(state, g_st);
				}
				stateMap.put(state, g_st);
				rule_states.add(g_st);
			}
			final G_Rule newRule = new G_Rule(
					rule.getSymbol(), rule_states, d_st);
			if (rule_states.isEmpty())
				startRules.add(newRule);
		}
		for (final G_Rule rule : startRules) {
			final Tree<HedgeSymbol<UnrankedSymbol>> tree = rule.getTree();
			if (tree != null)
				return TreeCache.getHedge(tree);
		}
		return null;
	}

	/**
	 * Private constructor.
	 */
	private EasyHAOps() {
		super();
	}

	/**
	 * Represents a Rule. Assignes trees to states.
	 */
	private static class G_Rule {
		private final HedgeSymbol<UnrankedSymbol> sym;
		private final LinkedList<G_St> rule;
		private final HashSet<G_St> unrec_rules;
		private final G_St dest;

		public G_Rule(final HedgeSymbol<UnrankedSymbol> symbol,
				final Collection<G_St> states,
				final G_St dest) {
			super();
			this.sym = symbol;
			this.rule = new LinkedList<G_St>();
			this.unrec_rules = new HashSet<G_St>();
			this.dest = dest;
			for (final G_St state : states) {
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
		 * If all the source states have been reached, this method constructs a tree for the
		 * destination state. If the destination state is a final state, the
		 * example tree is finished and will be returned.
		 *
		 * @return returns the example tree if a final state was reached, null
		 *         otherwise
		 */
		public Tree<HedgeSymbol<UnrankedSymbol>> getTree() {
			if (dest.isReached())
				return null;
			Tree<HedgeSymbol<UnrankedSymbol>> toRet = null;
			if (unrec_rules.isEmpty()) {
				final List<Tree<HedgeSymbol<UnrankedSymbol>>> sub = new LinkedList<Tree<HedgeSymbol<UnrankedSymbol>>>();
				for (final G_St rule : this.rule)
					sub.add(rule.getTree());
				final Tree<HedgeSymbol<UnrankedSymbol>> newTree = new StdTree<HedgeSymbol<UnrankedSymbol>>(
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
		public void signal(final G_St state) {
			assert unrec_rules.contains(state);
			unrec_rules.remove(state);
		}
	}

	/**
	 * Represents a state. Used to store additional information about a state.
	 */
	private static class G_St {
		// tree this state recognize
		private Tree<HedgeSymbol<UnrankedSymbol>> tree;
		// the rules containing this state
		private final List<G_Rule> rules;
		// the state this class represents
		private final HedgeState<State> state;
		// whether this state is a final state
		private final boolean finalSt;

		public Tree<HedgeSymbol<UnrankedSymbol>> getTree() {
			return this.tree;
		}

		public boolean isReached() {
			return this.tree != null;
		}

		public Tree<HedgeSymbol<UnrankedSymbol>> setTree(
				final Tree<HedgeSymbol<UnrankedSymbol>> tree,
				final G_Rule source) {
			this.tree = tree;
			Tree<HedgeSymbol<UnrankedSymbol>> toRet = null;
			for (final G_Rule rule : this.rules) {
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

		public G_St(final HedgeState<State> state, final boolean isFinal) {
			super();
			this.state = state;
			this.finalSt = isFinal;
			this.rules = new LinkedList<G_Rule>();
		}

		@Override
		public String toString() {
			return "G_St{" +
			"state=" + this.state +
			", finalSt=" + this.finalSt +
			'}';
		}

		public void addRule(final G_Rule rule) {
			this.rules.add(rule);
		}

		/**
		 * @see Object#equals(Object)
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
		 * @see Object#hashCode()
		 */
		@Override
		public int hashCode() {
			return this.state.hashCode();
		}
	}
}
