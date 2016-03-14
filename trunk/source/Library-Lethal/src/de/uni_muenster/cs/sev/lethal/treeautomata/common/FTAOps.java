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
/**
 * 
 */
package de.uni_muenster.cs.sev.lethal.treeautomata.common;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.tree.common.TreeCreator;
import de.uni_muenster.cs.sev.lethal.tree.common.TreeOps;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTAEpsRule;
import de.uni_muenster.cs.sev.lethal.utils.Combinator;
import de.uni_muenster.cs.sev.lethal.utils.Converter;
import de.uni_muenster.cs.sev.lethal.utils.Pair;
import de.uni_muenster.cs.sev.lethal.utils.SymmetricBoolTable;
import de.uni_muenster.cs.sev.lethal.utils.Table;
import de.uni_muenster.cs.sev.lethal.utils.Triple;

/**
 * Encapsulates several standard operations on finite tree automata.<br>
 * 
 * The following operations are contained:
 * <ul>
 * <li>change only one finite tree automaton: {@link #complete complete},
 * {@link #completeAlphabet completeAlphabet}, {@link #determinize determinize},
 * {@link #reduceBottomUp reduceBottomUp}, {@link #reduceTopDown reduceTopDown},
 * {@link #reduceFull reduceFull}, {@link #minimize minimize}</li>
 * <li>change language of one finite tree automaton: {@link #complement
 * complement}, {@link #complementAlphabet complementAlphabet}</li>
 * <li>change language with two finite tree automata: {@link #union union},
 * {@link #intersectionBU intersectionBU}, {@link #intersectionTD
 * intersectionTD}, {@link #intersectionWR intersectionWR}, {@link #difference
 * difference}</li>
 * <li>special languages: substitute some languages in a variable tree (
 * {@link #substitute substitute}), 
 * build up a tree automaton which accepts exactly the given tree 
 * ({@link #computeSingletonFTA computeSingletonFTA}),
 * build up a finite tree automaton accepting all trees of a given alphabet 
 * ({@link #computeAlphabetFTA computeAlphabetFTA}), 
 * build up a tree automaton that accepts exactly all trees of a language 
 * which are not higher than specified
 * ({@link #restrictToMaxHeight(FTA, int, FTACreator, Converter)}}) 
 * </li>
 * <li>construct a tree which the given automaton accepts (
 * {@link #constructTreeFrom})</li>
 * </ul>
 * 
 * The algorithms are based on <a href="http://tata.gforge.inria.fr/">TATA</a>.
 * 
 * 
 * @see FTA
 * @see Tree
 * 
 * @see FTACreator
 * @see Converter
 * @see Combinator
 * 
 * @author Dorothea, Irene, Martin
 */
public class FTAOps {

	/**
	 * Given a finite tree automaton, constructs an equivalent complete finite
	 * tree automaton.<br>
	 * A finite tree automaton is called complete, if for each
	 * combination of a symbol f of the alphabet of arity n and each combination
	 * of n states there is a rule containing this symbol and these states as source
	 * states.<br>
	 * <br>
	 * Algorithm:<br>
	 * <ol>
	 * <li>Add a new, fresh state (qbot) to the states of the new automaton.</li>
	 * <li>For each arity n contained in alphabet, generate all n-tuples of
	 * possible source states.</li>
	 * <li>For each Symbol f occurring in rules, store all tuples (q1,...qn),
	 * such that there is a rule with f(q1,..qn) on left side and add this rule
	 * also in the new automaton rules.</li>
	 * <li>for the remaining tuples, add a rule with destination state qbot.</li>
	 * </ol>
	 * 
	 * @param <Q>
	 *            state type of the finite tree automaton to be completed
	 * @param <F>
	 *            symbol type of the finite tree automaton to be completed
	 * @param <R>
	 *            rule type of the finite tree automaton to be completed
	 * @param <T>
	 *            type of the finite tree automaton to be completed
	 * @param fta
	 *            finite tree automaton to be completed
	 * @param qbot
	 *            fresh state for rules to be added
	 * @param fc
	 *            {@link FTACreator} to copy the finite tree automaton
	 * @return complete finite tree automaton equivalent to the given finite
	 *         tree automaton
	 */
	public static <Q extends State, F extends RankedSymbol, R extends FTARule<F, Q>, T extends FTA<F, Q, R>> T complete(
			FTA<F, Q, ? extends FTARule<F, Q>> fta, Q qbot,
					FTACreator<F, Q, R, T> fc) {
		// for each arity n the set of n-tuples
		Map<Integer, Set<List<Q>>> allTuples = new HashMap<Integer, Set<List<Q>>>();

		// for each symbol f of the alphabet the set of lists (q1,...qn)
		// such that there is a rule with f(q1,...,qn) on left side
		Map<F, Set<List<Q>>> defined = new HashMap<F, Set<List<Q>>>();

		// rules for new automaton
		LinkedList<R> newRules = new LinkedList<R>();

		// first step: add new state
		Set<Q> newStates = new HashSet<Q>(fta.getStates());
		newStates.add(qbot);

		// second step: for each arity n contained in alphabet, generate all
		// n-tuples of possible source states
		for (F f : fta.getAlphabet()) {
			int n = f.getArity();
			if (!allTuples.containsKey(f.getArity())) {
				allTuples.put(n, Combinator.combine(newStates, n));
			}
		}

		// third step: for each Symbol f occurring in rules, store all tuples
		// (q1,...qn)
		// such that there is a rule with f(q1,..qn) on left side
		for (FTARule<F, Q> rule : fta.getRules()) {
			Set<List<Q>> def;
			F f = rule.getSymbol();
			List<Q> src = rule.getSrcStates();
			if (!defined.containsKey(f)) {
				def = new HashSet<List<Q>>();
				defined.put(f, def);
			} else
				def = defined.get(f);
			def.add(src);
			newRules.add(fc.createRule(f, src, rule.getDestState()));
		}

		// fourth step: for the remaining tuples, add a rule with destination
		// state qbot
		for (F f : fta.getAlphabet()) {
			for (List<Q> src : allTuples.get(f.getArity())) {
				if (!(defined.containsKey(f) && defined.get(f).contains(src)))
					newRules.add(fc.createRule(f, src, qbot));
			}
		}
		return fc.createFTA(fta.getAlphabet(), newStates, fta.getFinalStates(),
				newRules);
	}

	/**
	 * Given a finite tree automaton, constructs a complete finite tree
	 * automaton with respect to the union of its alphabet and some given
	 * alphabet. <br>
	 * <br>
	 * Algorithm:<br>
	 * First union the alphabets and then use the method {@link #complete
	 * complete}.
	 * 
	 * @param <Q>
	 *            state type of finite tree automaton to be completed
	 * @param <F>
	 *            symbol type of finite tree automaton to be completed
	 * @param <R>
	 *            rule type of finite tree automaton to be completed
	 * @param <T>
	 *            type of finite tree automaton to be completed
	 * @param fta
	 *            finite tree automaton to be completed
	 * @param alphabet
	 *            alphabet with respect to which the automaton shall be
	 *            completed
	 * @param qbot
	 *            fresh state for rules to be added
	 * @param fc
	 *            {@link FTACreator} to copy the finite tree automaton
	 * 
	 * @return complete finite tree automaton equivalent to the given finite
	 *         tree automaton w.r.t. the given alphabet
	 * 
	 * @see #complete
	 */
	public static <Q extends State, F extends RankedSymbol, R extends FTARule<F, Q>, T extends FTA<F, Q, R>> T completeAlphabet(
			FTA<F, Q, ? extends FTARule<F, Q>> fta, Collection<F> alphabet,
					Q qbot, FTACreator<F, Q, R, T> fc) {
		// union of the alphabets
		HashSet<F> alphabet2 = new HashSet<F>(alphabet);
		alphabet2.addAll(fta.getAlphabet());
		// corresponding automaton with new alphabet
		T A2 = fc.createFTA(alphabet2, fta.getStates(), fta.getFinalStates(),
				fta.getRules());
		return complete(A2, qbot, fc);
	}

	/**
	 * Given a given finite tree automaton A, computes an equivalent
	 * deterministic finite tree automaton. <br>
	 * <br>
	 * <em>Algorithm:</em><br>
	 * Firstly, the sets of states (='setstates') are created that shall become
	 * a state of the new finite tree automaton. Also triples containing a
	 * symbol, a list of setstates (these will become the list of source states)
	 * and a setstate (this will become a destination state) are created in two
	 * steps: These triples will become the rules of the new finite tree
	 * automaton.<br>
	 * <em>1. Step</em>: Considering only constants.<br>
	 * If there are no constants, the language is empty and an empty automaton
	 * is returned. <br>
	 * Otherwise, for each constant all states that can be reached by this
	 * constant are collected. These states form a setstate. .* If this setstate
	 * hasn't been created before, the toDo-stack must be extended by all
	 * possible pairs consisting of a symbol having an arity >= 1 and a list of
	 * setstates containing this new setstate, whereas the length of this list
	 * is the same es the arity of the symbol. (
	 * {@link Combinator#allListsContainingXCombine})<br>
	 * The triple (constant, empty list, setstate) is stored.<br>
	 * <em> 2. Step </em>: Consider all other symbols.<br>
	 * Until the toDoStack is empty, take an element of it, that is a symbol and
	 * a list of setstates. Consider all rules with this symbol, such that the
	 * first state of the source states is contained in the first set of the
	 * list, the second state is contained in the second set of the list, and so
	 * on, and collect the destination states of the rules. <br>
	 * The triple (symbol, list of setstates, set of destination states) is
	 * stored. <br>
	 * If this setstate has not been created before, the toDo-list is extended
	 * as described above.
	 * 
	 * @param <Q>
	 *            state type of the finite tree automaton to be determinized
	 * @param <Q0>
	 *            state type of the determinized finite tree automaton
	 * @param <F>
	 *            symbol type of the finite tree automaton to be determinized
	 * @param <R0>
	 *            rule type of the determinized finite tree automaton
	 * @param <U>
	 *            type of the determinized finite tree automaton
	 * @param fta
	 *            automaton to be determinized
	 * @param fc
	 *            {@link FTACreator} to create the determinized finite tree
	 *            automaton and fitting rules
	 * @param sc
	 *            state converter which converts sets of states of type Q to
	 *            states of type Q0. It must be injective, that means if s1 and
	 *            s2 are different sets of Q, then sc.convert(s1) and
	 *            sc.convert(s2) must also be different!
	 * 
	 * @return deterministic finite tree automaton equivalent to the given one
	 */
	public static <Q extends State, Q0 extends State, F extends RankedSymbol, R0 extends FTARule<F, Q0>, U extends FTA<F, Q0, R0>> U determinize(
			FTA<F, Q, ? extends FTARule<F, Q>> fta,
					FTACreator<F, Q0, R0, U> fc, Converter<Set<Q>, Q0> sc) {

		// this shall become the new tree automaton
		LinkedList<Q0> newStates = new LinkedList<Q0>();
		LinkedList<Q0> newFinals = new LinkedList<Q0>();
		LinkedList<R0> newRules = new LinkedList<R0>();

		// and to create this new automaton, we first work with sets of states
		Set<Set<Q>> setStates = new HashSet<Set<Q>>();
		Set<Set<Q>> setFinals = new HashSet<Set<Q>>();

		// and use a set to store what symbols with which list of sets of states
		// create which set of state;
		// because this determines the new rules
		HashSet<Triple<F, List<Set<Q>>, Set<Q>>> helpRules = new HashSet<Triple<F, List<Set<Q>>, Set<Q>>>();

		// alphabet
		Collection<F> alphabet = fta.getAlphabet();

		// we need a list the arities of the symbols of the alphabet
		Set<Integer> arities = new HashSet<Integer>();
		for (RankedSymbol f : alphabet) {
			arities.add(f.getArity());
		}

		// If the alphabet of the automaton contains no constants,
		// it's language is empty, so we return an empty automaton
		if (!arities.contains(0))
			return fc.createFTA(alphabet, newStates, newFinals, newRules);

		// otherwise it is a bit more complicated ;-)
		// But, 0 is contained in arities, and that is a good thing!
		else {
			// in the following we distinguish between symbols of different
			// arities
			// so we create a set that gives to an arity all symbols with this
			// arity
			HashMap<Integer, Set<F>> symbols = new HashMap<Integer, Set<F>>();
			for (Integer ar : arities) {
				// set that shall contain all symbols with the arity ar
				Set<F> arSymbols = new HashSet<F>();
				for (F f : alphabet) {
					if (f.getArity() == ar)
						arSymbols.add(f);
				}
				symbols.put(ar, arSymbols);
			}
			// we will not need the arity 0 later on, so we remove it from
			// 'arities'
			arities.remove(0);

			// all pairs of symbols and lists of sets of states, that are still
			// to consider
			Stack<Pair<F, List<Set<Q>>>> toDo = new Stack<Pair<F, List<Set<Q>>>>();

			// we need to consider all constants (symbols with arity 0);
			// constants do not need any source states,
			// so we make pairs (symbol, empty list)
			for (F c : symbols.get(0)) {
				List<Set<Q>> srcStates = new LinkedList<Set<Q>>();
				Pair<Set<Q>, Boolean> resultedPair = getDestStates(fta, c,
						srcStates);
				Set<Q> destState = resultedPair.getFirst();

				// no destination states, we have a dead end; ignore!
				if (destState.isEmpty())
					continue;

				// if the state is not already contained in setStates,
				boolean isContained = setStates.contains(destState);
				// it must be added to the new set of states
				if (!isContained) {
					setStates.add(destState);
					// and, maybe, it must be added to the new set of final
					// states
					if (resultedPair.getSecond()) {
						setFinals.add(destState);
					}
					// and if the destState is not already contained in
					// setStates,
					// the toDo-stack must be extended by new pairs of symbol
					// and list of
					// sets of states containing this state
					for (int n : arities) {
						for (List<Set<Q>> srcState : Combinator
								.allListsContainingXCombine(setStates,
										destState, n)) {
							for (F f : symbols.get(n)) {
								toDo
								.push(new Pair<F, List<Set<Q>>>(f,
										srcState));
							}
						}
					}
				}
				// and later on we need to create a new rule with this symbol c
				// and the destState
				helpRules.add(new Triple<F, List<Set<Q>>, Set<Q>>(c, srcStates,
						destState));
			}

			// add reachable states as long as possible
			while (!toDo.isEmpty()) {
				Pair<F, List<Set<Q>>> consideredPair = toDo.pop();
				Pair<Set<Q>, Boolean> resultedPair = getDestStates(fta,
						consideredPair.getFirst(), consideredPair.getSecond());

				Set<Q> destState = resultedPair.getFirst();

				// no destination states, we have a dead end; ignore!
				if (destState.isEmpty())
					continue;

				// add computed rule
				helpRules.add(new Triple<F, List<Set<Q>>, Set<Q>>(
						consideredPair.getFirst(), consideredPair.getSecond(),
						resultedPair.getFirst()));

				// if this state has not already been created
				if (!setStates.contains(destState)) {
					// then it must be added to the new set of states
					setStates.add(destState);
					// and, maybe, it must be added to the new set of final
					// states
					if (resultedPair.getSecond()) {
						setFinals.add(destState);
					}
					// and the toDo-stack must be extended by new pairs of
					// symbol and list of sets of states containing this state

					for (int n : arities) {

						for (List<Set<Q>> srcState : Combinator
								.allListsContainingXCombine(setStates,
										destState, n)) {
							for (F f : symbols.get(n)) {
								toDo
								.push(new Pair<F, List<Set<Q>>>(f,
										srcState));
							}
						}
					}
				}
				// if this state has been created before, go on with the next
				// element of toDo
				// until toDo is empty
			}

			// convert the set of states (states and final states) into
			// setstates
			// we use a HasMap because we later want to create the rules
			HashMap<Set<Q>, Q0> save = new HashMap<Set<Q>, Q0>();

			for (Set<Q> set : setStates) {
				Q0 newstate = sc.convert(set);
				newStates.add(newstate);
				save.put(set, newstate);
				if (setFinals.contains(set))
					newFinals.add(newstate);
			}

			// create new rules
			List<Q0> srcStates = new LinkedList<Q0>();
			for (Triple<F, List<Set<Q>>, Set<Q>> triple : helpRules) {
				// function symbol of the rule
				F symbol = triple.getFirst();
				// source states of the rule
				srcStates.clear();
				for (Set<Q> set : triple.getSecond()) {
					srcStates.add(save.get(set));
				}
				// dest state of the rule
				Q0 destState = save.get(triple.getThird());
				// create the new rule and add it
				R0 rule = fc.createRule(symbol, srcStates, destState);
				newRules.add(rule);
			}

			// return the deterministic tree Automaton
			return fc.createFTA(fta.getAlphabet(), newStates, newFinals,
					newRules);
		}
	}

	/**
	 * For a given finite tree automaton, a list (s1,...,sn) of state sets and a
	 * symbol f, computes all states for which there is a rule f(q1,...,qn) with
	 * qi \in s_i for i=1,...,n <br>
	 * Used as helper method for determinize.
	 * 
	 * @param fta
	 *            finite tree automaton to examine
	 * @param combi
	 *            list of set of states to examine every combination from
	 * @param symbol
	 *            symbol to examine
	 * @param <Q>
	 *            state type of finite tree automaton to be analysed
	 * @param <F>
	 *            symbol type of finite tree automaton to be analysed
	 * @return the set of all states q, for which there is a rule f(q1,...,qn)
	 *         with (q1,...,qn) \in combi(0)x...xcombi(combi.length()-1)
	 * 
	 * @see #determinize(FTA, FTACreator, Converter)
	 */
	private static <Q extends State, F extends RankedSymbol> Pair<Set<Q>, Boolean> getDestStates(
			FTA<F, Q, ? extends FTARule<F, Q>> fta, F symbol, List<Set<Q>> combi) {
		// states that can be reached by using the given symbol and source
		// states
		Set<Q> destSet = new HashSet<Q>();
		// indicates, whether destSet contains a final state of the finite tree
		// automaton
		boolean finState = false;
		// consider each rule that uses the given symbol
		for (FTARule<F, Q> r : fta.getSymbolRules(symbol)) {
			// ... and check, whether the source states fit
			Iterator<Q> srcStateIter = r.getSrcStates().listIterator();
			Iterator<Set<Q>> srcStateDomainIter = combi.listIterator();
			// indicates whether the i-th source state is contained in the i-th
			// set of the list
			boolean allContained = true;
			while (srcStateIter.hasNext()) {
				Q srcState = srcStateIter.next();
				Set<Q> srcStateDomain = srcStateDomainIter.next();
				if (!srcStateDomain.contains(srcState)) {
					allContained = false;
					break;
				}
			}
			// if the rule fits, add the destination state of the rule to
			// destSet ...
			if (allContained) {
				destSet.add(r.getDestState());
				// ... and set finState true, if necessary
				if (!finState
						&& fta.getFinalStates().contains(r.getDestState()))
					finState = true;
			}
		}

		return new Pair<Set<Q>, Boolean>(destSet, finState);
	}

	/**
	 * Given a finite tree automaton A, constructs an equivalent reduced finite
	 * tree automaton. <br>
	 * A finite tree automaton is called reduced, if for each state q, there is
	 * at least one tree t, whose root symbol can be annotated with q. That
	 * means all states are reachable.<br>
	 * <br>
	 * Algorithm:<br>
	 * The reachable states are collected. Therefore at the beginning no states
	 * are marked and then all states which can be reached with the marked
	 * states are marked. The process ends if no rule can be used to mark an
	 * additional state. For the new finite tree automaton only marked states
	 * and rules (that do not contain any not marked state) are used.
	 * 
	 * @param <Q>
	 *            state type of finite tree automaton to be reduced
	 * @param <F>
	 *            symbol type of finite tree automaton to be reduced
	 * @param <R>
	 *            rule type of finite tree automaton to be reduced
	 * @param <T>
	 *            type of finite tree automaton to be reduced
	 * @param fta
	 *            finite tree automaton to be reduced
	 * @param fc
	 *            {@link FTACreator} to create the reduced finite tree automaton
	 * 
	 * @return reduced version of supplied finite tree automaton
	 */
	public static <Q extends State, F extends RankedSymbol, R extends FTARule<F, Q>, T extends FTA<F, Q, R>> T reduceBottomUp(
			FTA<F, Q, ? extends FTARule<F, Q>> fta, FTACreator<F, Q, R, T> fc) {

		LinkedList<FTARule<F,Q>> worklist = new LinkedList<FTARule<F,Q>>();

		/* group rules by source state */
		Map<Q, Collection<FTARule<F,Q>>> rulesBySrcState = new HashMap<Q, Collection<FTARule<F,Q>>>();
		for (FTARule<F,Q> rule: fta.getRules()) {

			/*
			 * add all rules starting at leaves to worklist
			 */
			if (rule.getSymbol().getArity()==0) {
				worklist.add(rule);
			}

			for (Q qsrc: rule.getSrcStates()) {
				Collection<FTARule<F,Q>> qsrcRules;
				if (rulesBySrcState.containsKey(qsrc))
					qsrcRules = rulesBySrcState.get(qsrc);
				else {
					qsrcRules = new LinkedList<FTARule<F,Q>>();
					rulesBySrcState.put(qsrc, qsrcRules);
				}
				qsrcRules.add(rule);
			}
		}

		HashSet<Q> marked = new HashSet<Q>();
		HashSet<Q> markedFinals = new HashSet<Q>();
		LinkedList<FTARule<F, Q>> markedRules = new LinkedList<FTARule<F, Q>>();
		while (!worklist.isEmpty()) {
			FTARule<F,Q> nextRule = worklist.poll();
			Q nextState = nextRule.getDestState();
			boolean allMarked = true;
			for (Q qsrc: nextRule.getSrcStates()) {
				if (!marked.contains(qsrc)) {
					allMarked = false;
					break;
				}
			}

			if (allMarked) {
				markedRules.add(nextRule);
				boolean isNew = marked.add(nextState);

				if (isNew) {
					if (fta.getFinalStates().contains(nextState))
						markedFinals.add(nextState);


					if (rulesBySrcState.containsKey(nextState))
						for (FTARule<F,Q> ruleFromNextState: rulesBySrcState.get(nextState))
							worklist.add(ruleFromNextState);
				}
			}
		}

		return fc.createFTA(fta.getAlphabet(), marked, markedFinals,markedRules);
		//		// HashSet<State> states = getStates();
		//		// marked is the set of accessible states
		//		HashSet<Q> marked = new HashSet<Q>();
		//		// markedFinals is the set of the (new) final states
		//		Set<Q> markedFinals = new HashSet<Q>();
		//		// new rules
		//		LinkedList<FTARule<F, Q>> markedRules = new LinkedList<FTARule<F, Q>>();
		//
		//		// addPossible is true, if an unmarked state can be added to marked
		//		boolean addPossible = true;
		//		// in each step we have to regard this set of rules; the matching rules
		//		// will be added tu stateRules ...
		//		HashSet<FTARule<F, Q>> rulesToExamine = new HashSet<FTARule<F, Q>>();
		//		// ... and the other ones to notMatchingRules
		//		HashSet<FTARule<F, Q>> notMatchingRules = new HashSet<FTARule<F, Q>>(
		//				fta.getRules());
		//
		//		// add reachable states as long as possible. No add is possible, if
		//		// after a step
		//		// rulesToRegard=notMatchingRules holds
		//		while (addPossible) {
		//			rulesToExamine.clear();
		//
		//			rulesToExamine.addAll(notMatchingRules);
		//			notMatchingRules.clear();
		//			// go through all rules
		//			for (FTARule<F, Q> rule : rulesToExamine) {
		//				List<Q> srcStates = rule.getSrcStates();
		//				// check whether all source states are already marked
		//				boolean srcStatesAreMarked = true;
		//				for (Q q : srcStates) {
		//					if (!(marked.contains(q))) {
		//						srcStatesAreMarked = false;
		//						break;
		//					}
		//				}
		//				// add rule, if all source states of the rule are marked
		//				if (srcStatesAreMarked) {
		//					// add the new rule
		//					markedRules.add(rule);
		//					Q dest = rule.getDestState();
		//					// mark the dest-state as reachable
		//					marked.add(dest);
		//					// if it was a final state in the given automaton, it is one
		//					// in the new automaton
		//					if (fta.getFinalStates().contains(dest))
		//						markedFinals.add(dest);
		//				}
		//				// otherwise add it to notMatchingRules
		//				else
		//					notMatchingRules.add(rule);
		//			}
		//			// if notMatchingRules = RulesToRegard, no future change is
		//			// possible,
		//			// so set addPossible to false, otherwise to true
		//			addPossible = (notMatchingRules.size() != rulesToExamine.size());
		//		}
		//		// return the reduced tree Automaton
		//		return fc.createFTA(fta.getAlphabet(), marked, markedFinals,
		//				markedRules);
	}

	/**
	 * Given a finite tree automaton A, constructs an equivalent finite tree
	 * automaton A', which is top-down reduced.<br>
	 * That means, that the resulting automaton contains only states from which
	 * a final state is reachable and only rules in which these states occur.<br>
	 * <br>
	 * The result is gained by the <em>top-down-reducing-algorithm</em>:<br>
	 * Beginning with the final states on a work list, search for a state on the
	 * work list all rules that have this state as destination state and add the
	 * rule and the corresponding source states to the resulting states of the
	 * new automaton.<br>
	 * Do this until the work list is empty.
	 * 
	 * @param <Q>
	 *            state type of the finite tree automaton to be reduced
	 * @param <F>
	 *            symbol type of the finite tree automaton to be reduced
	 * @param <R>
	 *            rule type of the finite tree automaton to be reduced
	 * @param <T>
	 *            type of the finite tree automaton to be reduced
	 * @param fta
	 *            finite tree automaton to be reduced
	 * @param fc
	 *            {@link FTACreator} to create the reduced finite tree automaton
	 * 
	 * @return equivalent finite tree automaton which only contains states from
	 *         which a final state is reachable and contains only the rules in
	 *         which merely these states occur.
	 */
	public static <Q extends State, F extends RankedSymbol, R extends FTARule<F, Q>, T extends FTA<F, Q, R>> T reduceTopDown(
			FTA<F, Q, ? extends FTARule<F, Q>> fta, FTACreator<F, Q, R, T> fc) {

		// initialize work list with all final states
		LinkedList<Q> worklist = new LinkedList<Q>();
		Set<Q> redStates = new HashSet<Q>(), redFinals = new HashSet<Q>();
		Set<FTARule<F, Q>> redRules = new HashSet<FTARule<F, Q>>();
		for (Q qf : fta.getFinalStates()) {
			worklist.add(qf);
			redStates.add(qf);
			redFinals.add(qf);
		}

		/* */
		Map<Q, Set<FTARule<F, Q>>> rulesByDestState = new HashMap<Q, Set<FTARule<F, Q>>>();
		for (FTARule<F, Q> r : fta.getRules()) {
			Q q = r.getDestState();
			Set<FTARule<F, Q>> qRules;
			if (rulesByDestState.containsKey(q))
				qRules = rulesByDestState.get(q);
			else {
				qRules = new HashSet<FTARule<F, Q>>();
				rulesByDestState.put(q, qRules);
			}
			qRules.add(r);
		}

		// for states in the work list search rules
		// which have them as destination state
		// and add the corresponding source states to the work list
		// and the rules for the reduced automaton
		while (!worklist.isEmpty()) {
			Q next = worklist.poll();
			if (rulesByDestState.containsKey(next)) {
				for (FTARule<F, Q> r : rulesByDestState.get(next)) {
					Iterator<Q> srcIter = r.getSrcStates().listIterator();
					while (srcIter.hasNext()) {
						Q q = srcIter.next();
						if (!redStates.contains(q)) {
							worklist.add(q);
							redStates.add(q);
						}
					}
					redRules.add(r);
				}
			}
		}

		return fc.createFTA(fta.getAlphabet(), redStates, redFinals, redRules);
	}

	/**
	 * Given a finite tree automaton, constructs a finite tree automaton which
	 * is both top-down and bottom-up reduced. The resulting finite tree
	 * automaton has the following properties: <br>
	 * <ul>
	 * <li>For every state q there is a tree which can be reduced to q.</li>
	 * <li>For every rule f(q1,...,qn) -> q there is a final state qf and a
	 * configuration tree t, such that f(q1,...,qn) is a subtree of t and t can
	 * be reduced to qf.</li>
	 * </ul>
	 * In conclusion, for each rule of the resulting automaton there is a tree t
	 * and a final state qf, such that t can be reduced to a configuration tree
	 * containing the left-hand side of the rule, which can be reduced to qf.
	 * 
	 * @param <Q>
	 *            state type of the finite tree automaton to be reduced
	 * @param <F>
	 *            symbol type of the finite tree automaton to be reduced
	 * @param <R>
	 *            rule type of the finite tree automaton to be reduced
	 * @param <T>
	 *            type of the finite tree automaton to be reduced
	 * @param fta
	 *            finite tree automaton to be reduced
	 * @param fc
	 *            creator for the reduced finite tree automaton and its rules
	 * 
	 * @return fully reduced version of the given finite tree automaton, that
	 *         means for every rule f(q1,...qn) - q there is a tree t, a
	 *         configuration tree tc and a final state qf such that f(q1,...qn)
	 *         is a subtree of tc, t can be reduced to tc and tc can be reduced
	 *         to qf.
	 * 
	 * @see FTAOps#reduceBottomUp
	 * @see FTAOps#reduceTopDown
	 * 
	 */
	public static <Q extends State, F extends RankedSymbol, R extends FTARule<F, Q>, T extends FTA<F, Q, R>> T reduceFull(
			FTA<F, Q, ? extends FTARule<F, Q>> fta, FTACreator<F, Q, R, T> fc) {
		return reduceBottomUp(reduceTopDown(fta, fc), fc);
	}

	/**
	 * Given a deterministic finite tree automaton, constructs an equivalent
	 * finite tree automaton with an almost minimal number of states. More
	 * precisely, the number of states of the resulting automaton is minimal, if
	 * the given automaton is complete. Otherwise, it is completed first and
	 * thus enriched by one extra state - therefore the number of states of the
	 * resulting automaton is not exactly the minimal number n, but n+1.<br>
	 * Note that this method throws an exception if the given finite tree
	 * automaton is not deterministic. <br>
	 * <em>Algorithm:</em><br>
	 * <em>1. step:</em> Create a table storing whether two states are
	 * 'equivalent'. <br>
	 * As initialization, all final states are equivalent to each other and all
	 * states, that are not final states, are equivalent to each other. <br>
	 * As long as there are any changes possible, two different states that are
	 * marked as equivalent are considered and marked as not equivalent if and
	 * only if there exists a pair of compatible rules (
	 * {@link FTAOps#compatibleRules}) for these two states such that the
	 * destination states of the rules are not marked as equivalent.<br>
	 * <em>2. step: </em> Sets of states representing exactly the equivalence
	 * classes are created and converted into a state. If the set contains a
	 * final set, the new state becomes a final state. The new rules are created
	 * out of the former rules by substituting occurring states by their
	 * equivalence classes.
	 * 
	 * @param fta
	 *            finite tree automaton to be minimized
	 * @param qbot
	 *            state to be added by completion
	 * @param fc
	 *            {@link FTACreator} for reduction and completion
	 * @param sc0
	 *            state converter used for the minimization (after the
	 *            determinization) - conversion must be injective!.
	 * @param fc0
	 *            {@link FTACreator} used for the minimization
	 * @param <Q>
	 *            state type of the given finite tree automaton
	 * @param <F>
	 *            symbol type of the given finite tree automaton
	 * @param <R>
	 *            rule type of the reduced and completed version of the given
	 *            finite tree automaton
	 * @param <T>
	 *            type of the reduced and completed version of the given finite
	 *            tree automaton
	 * @param <Q0>
	 *            state type of the resulting finite tree automaton
	 * @param <R0>
	 *            rule type of the resulting finite tree automaton
	 * @param <U>
	 *            type of the finite tree automaton to be returned
	 * 
	 * @throws IllegalArgumentException
	 *             if the given finite tree automaton is not deterministic
	 * 
	 * @return finite tree automaton with a minimal number of states which has
	 *         the same language as the given one
	 */
	public static <Q extends State, Q0 extends State, F extends RankedSymbol, R extends FTARule<F, Q>, T extends FTA<F, Q, R>, R0 extends FTARule<F, Q0>, U extends FTA<F, Q0, R0>> U minimize(
			FTA<F, Q, ? extends FTARule<F, Q>> fta, Q qbot,
					FTACreator<F, Q, R, T> fc, Converter<Set<Q>, Q0> sc0,
					FTACreator<F, Q0, R0, U> fc0) {
		if (!FTAProperties.checkDeterministic(fta))
			throw new IllegalArgumentException(
			"Cannot minimize a non-deterministic finite tree automaton! You have to determinize first!");
		T ta = reduceBottomUp(complete(fta, qbot, fc), fc);
		// precompute compatible rules for checking efficiently for equivalence
		// in the main loop
		Table<Q, Q, List<Pair<R, R>>> compatRules = new Table<Q, Q, List<Pair<R, R>>>(
				ta.getStates(), ta.getStates());
		for (Q q1 : ta.getStates())
			for (Q q2 : ta.getStates())
				compatRules.setEntry(q1, q2, FTAOps.<Q, F, R> compatibleRules(
						ta.getRules(), q1, q2));

		// we compute this so we do not have to iterate through sets all the
		// time
		Map<Q, Boolean> isFinal = new HashMap<Q, Boolean>();
		for (Q q : ta.getStates())
			if (ta.getFinalStates().contains(q))
				isFinal.put(q, true);
			else
				isFinal.put(q, false);
		// initialize table for computing equivalence between states
		SymmetricBoolTable<Q> equivalenceTable = new SymmetricBoolTable<Q>(ta
				.getStates());
		Set<Pair<Q, Q>> cells = equivalenceTable.getCells();
		Q q1, q2;
		for (Pair<Q, Q> p : cells) {
			q1 = p.getFirst();
			q2 = p.getSecond();
			if ((isFinal.get(q1) && !isFinal.get(q2))
					|| (isFinal.get(q2) && !isFinal.get(q1))) {
				equivalenceTable.setEntry(q1, q2, false);
			} else {
				equivalenceTable.setEntry(q1, q2, true);
			}
		}
		boolean done = false;

		// main loop
		// refine equivalence relation represented by table until
		// nothing is changed in one full iteration
		while (!done) {
			done = true;
			// go through all entries of table
			for (Pair<Q, Q> p : cells) {
				q1 = p.getFirst();
				q2 = p.getSecond();
				if (equivalenceTable.getEntry(q1, q2)) {
					// q1 and q2 are equivalent; now check for all states
					// resulting from compatible rules
					boolean allEquivalent = true;
					for (Pair<? extends R, ? extends R> rulePair : compatRules
							.getEntry(q1, q2)) {
						Q r1 = rulePair.getFirst().getDestState();
						Q r2 = rulePair.getSecond().getDestState();
						if (!equivalenceTable.getEntry(r1, r2)) {
							allEquivalent = false;
							break;
						}
					}
					if (!allEquivalent) {
						equivalenceTable.setEntry(q1, q2, false);
						// equivalenceTable.setEntry(q2, q1, false);
						done = false;
					}
				}
			}
		}

		// done is true if and only if we have gone through the whole table
		// without changing anything,
		// so, here we have an equivalence relation, whose number of classes
		// cannot be augmented
		// since we started with the minimal number of classes, we have now the
		// maximal number of
		// classes where we have identified different behaviour, i.e. the
		// minimal number of states.

		Map<Q, Q0> equivalenceClass = new HashMap<Q, Q0>();
		LinkedList<R0> newRules = new LinkedList<R0>();
		LinkedList<Q0> newFinals = new LinkedList<Q0>();

		// compute for each state the equivalence class
		for (Q q : ta.getStates()) {
			boolean alreadyContained = false;

			// if q is equivalent to a state for which we have already
			// computed the equivalence class, then the equivalence
			// class of q is the same
			for (Q r : equivalenceClass.keySet()) {
				if (equivalenceTable.getEntry(q, r)) {
					equivalenceClass.put(q, equivalenceClass.get(r));
					if (isFinal.get(q))
						newFinals.add(equivalenceClass.get(q));
					alreadyContained = true;
					break;
				}
			}

			// if q is not contained in an equivalence class
			// which we already know, we compute and add the equivalence class
			// of q
			if (!alreadyContained) {
				// the equivalence class of q is the set of all states
				// with "true" in the corresponding table row
				Set<Q> newEClass = equivalenceTable
				.getColumnsWithValue(q, true);
				Q0 stateNewEClass = sc0.convert(newEClass);
				equivalenceClass.put(q, stateNewEClass);
				if (isFinal.get(q))
					newFinals.add(stateNewEClass);
			}

		}

		// convert rules by substituting occurring states by their equivalence
		// classes
		for (R r : ta.getRules()) {
			List<Q0> newSrcStates = new ArrayList<Q0>();
			Q0 newDestState = equivalenceClass.get(r.getDestState());
			for (Q q0 : r.getSrcStates()) {
				newSrcStates.add(equivalenceClass.get(q0));
			}
			newRules.add(fc0.createRule(r.getSymbol(), newSrcStates,
					newDestState));
		}

		return fc0.createFTA(ta.getAlphabet(), equivalenceClass.values(),
				newFinals, newRules);
	}

	/**
	 * Computes for a given set of rules and a given pair of states all pairs of
	 * rules which are compatible with respect to two given states q1 and q2. <br>
	 * Helper method for minimize. <br>
	 * Two rules r1, r2 are called compatible with respect to q1 and q2, if the
	 * following conditions are met (abbreviate l1 := r1.getSrcStates(), l2 :=
	 * r2.getSrcStates()): <br>
	 * (i) l1.size() == l2.size() <br>
	 * (ii) there is exactly one index i with !(l1.get(i).equals(l2.get(i)))<br>
	 * (iii) for all indices i: !(l1.get(i).equals(l2.get(i))) ==>
	 * l1.get(i).equals(q1) && l2.get(i).equals(q2)
	 * 
	 * @param rules
	 *            rules filtered for compatibility with respect to the two given
	 *            states
	 * @param q1
	 *            first state
	 * @param q2
	 *            second state
	 * @param <Q>
	 *            state type of rules to examine
	 * @param <F>
	 *            symbol type of rules to examine
	 * @param <R>
	 *            type of rules to examine
	 * 
	 * @return all pairs (r1,r2) where rules.contains(r1), rules.contains(r2)
	 *         and the following conditions are met (abbreviate l1 :=
	 *         r1.getSrcStates(), l2 := r2.getSrcStates()) (i) l1.size() ==
	 *         l2.size() (ii) there is exactly one i with
	 *         !(l1.get(i).equals(l2.get(i))) (iii) for all i:
	 *         !(l1.get(i).equals(l2.get(i))) ==> l1.get(i).equals(q1) &&
	 *         l2.get(i).equals(q2)
	 * 
	 * @see #minimize(FTA, State, FTACreator, Converter, FTACreator)
	 */
	private static <Q extends State, F extends RankedSymbol, R extends FTARule<F, Q>> List<Pair<R, R>> compatibleRules(
			Collection<? extends R> rules, Q q1, Q q2) {
		List<Pair<R, R>> ret = new ArrayList<Pair<R, R>>();
		for (R r1 : rules)
			for (R r2 : rules) {
				List<Q> l1 = r1.getSrcStates();
				List<Q> l2 = r2.getSrcStates();
				if (l1.size() == l2.size() && l1.contains(q1)
						&& l2.contains(q2)) {

					int numberOfDifferences = 0;
					int lastDiffIndex = 0;
					for (int i = 0; i < l1.size(); i++) {
						if (!l1.get(i).equals(l2.get(i))) {
							numberOfDifferences++;
							lastDiffIndex = i;
						}
						if (numberOfDifferences >= 2)
							break;
					}

					if ((numberOfDifferences == 0 && q1.equals(q2))
							|| (numberOfDifferences == 1
									&& l1.get(lastDiffIndex).equals(q1) && l2
									.get(lastDiffIndex).equals(q2)))
						ret.add(new Pair<R, R>(r1, r2));
				}
			}
		return ret;
	}

	/**
	 * Given a finite tree automaton A, constructs a finite tree automaton which
	 * accepts a tree over the alphabet of A if and only if A denies it. <br>
	 * <br>
	 * Algorithm:<br>
	 * Foremost, the finite tree automaton is determinized and the result
	 * completed. Finally final states and non-final states are switched.
	 * 
	 * @param <Q>
	 *            state type of the finite tree automaton to be complemented
	 * @param <Q0>
	 *            state type of the complemented finite tree automaton
	 * @param <F>
	 *            symbol type of the finite tree automaton to be complemented
	 * @param <R0>
	 *            rule type of the complemented finite tree automaton
	 * @param <T0>
	 *            type of the complemented finite tree automaton
	 * @param fta
	 *            finite tree automaton to be complemented
	 * @param sc
	 *            state converter for determinization from a set of state to a
	 *            state! Conversion must be injective!
	 * @param fc0
	 *            creator object for the complemented automaton
	 * @return complemented finite tree automaton
	 */
	public static <Q extends State, Q0 extends State, F extends RankedSymbol, R0 extends FTARule<F, Q0>, T0 extends FTA<F, Q0, R0>> T0 complement(
			FTA<F, Q, ? extends FTARule<F, Q>> fta, Converter<Set<Q>, Q0> sc,
					FTACreator<F, Q0, R0, T0> fc0) {
		Q0 qbot = sc.convert(new HashSet<Q>());
		T0 result = complete(determinize(fta, fc0, sc), qbot, fc0);
		Collection<Q0> states = result.getStates();
		Collection<Q0> finalStates = result.getFinalStates();
		LinkedList<Q0> newFinalStates = new LinkedList<Q0>();
		for (Q0 state : states) {
			if (!finalStates.contains(state))
				newFinalStates.add(state);
		}
		return fc0.createFTA(fta.getAlphabet(), states, newFinalStates, result
				.getRules());
	}

	/**
	 * Given a finite tree automaton A, constructs a finite tree automaton which
	 * accepts a tree if and only if A denies it with respect to the union of
	 * its alphabet and some given alphabet. <br>
	 * Algorithm:<br>
	 * Foremost, the finite tree automaton is determinized and the result
	 * completed with respect to the union of its and the given alphabet.
	 * Finally final states and non-final states are switched.
	 * 
	 * @param <Q>
	 *            state type of automaton to be complemented
	 * @param <Q0>
	 *            state type of complemented automaton
	 * @param <F>
	 *            symbol type of automaton to be complemented
	 * @param <R0>
	 *            rule type of complemented automaton
	 * @param <T0>
	 *            type of complemented automaton
	 * @param fta
	 *            automaton to be complemented
	 * @param alphabet
	 *            alphabet to which the automaton is to be complemented
	 * @param sc
	 *            state converter for determinization! Conversion must be
	 *            injective!
	 * @param fc0
	 *            creator object for the complemented automaton
	 * 
	 * @return complemented finite tree automaton
	 */
	public static <Q extends State, Q0 extends State, F extends RankedSymbol, R0 extends FTARule<F, Q0>, T0 extends FTA<F, Q0, R0>> T0 complementAlphabet(
			FTA<F, Q, ? extends FTARule<F, Q>> fta, Collection<F> alphabet,
					Converter<Set<Q>, Q0> sc, FTACreator<F, Q0, R0, T0> fc0) {
		Q0 qbot = sc.convert(new HashSet<Q>());
		HashSet<F> alphabet2 = new HashSet<F>(alphabet);
		alphabet2.addAll(fta.getAlphabet());
		T0 result = completeAlphabet(determinize(fta, fc0, sc), alphabet2,
				qbot, fc0);
		Collection<Q0> states = result.getStates();
		Collection<Q0> finalStates = result.getFinalStates();
		HashSet<Q0> newFinalStates = new HashSet<Q0>();
		for (Q0 state : states) {
			if (!finalStates.contains(state))
				newFinalStates.add(state);
		}
		return fc0.createFTA(fta.getAlphabet(), states, newFinalStates, result
				.getRules());
	}

	/**
	 * Returns a finite tree automaton that recognizes exactly the union of the
	 * languages of the given finite tree automata.<br>
	 * The resulting finite tree automaton is in general non-deterministic.<br>
	 * <br>
	 * This is realized by guaranteeing that the states of the finite tree
	 * automata are disjoint. (Embed them disjointly in new states.) Then
	 * construct a new finite tree automaton with the union of states, union of
	 * final states and union of rules.
	 * 
	 * @param <Q1>
	 *            state type of the first finite tree automaton
	 * @param <F1>
	 *            symbol type of the first finite tree automaton
	 * @param <Q2>
	 *            state type of the second finite tree automaton
	 * @param <F2>
	 *            symbol type of the second finite tree automaton
	 * @param <Q3>
	 *            state type of the result finite tree automaton
	 * @param <F3>
	 *            symbol type of the result finite tree automaton
	 * @param <R>
	 *            rule type of the result finite tree automaton
	 * @param <T>
	 *            type of the result finite tree automaton
	 * @param fta1
	 *            the first finite tree automaton for the union
	 * @param fta2
	 *            the second finite tree automaton for the union
	 * @param c13
	 *            converter object which converts state set of first finite tree
	 *            automaton into states of result finite tree automaton.
	 *            Resulting states must be different from any resulting state of
	 *            the second converter object
	 * @param c23
	 *            converter object which converts state set of second finite
	 *            tree automaton into states of result finite tree automaton.
	 *            Resulting states must be different from any resulting state of
	 *            the first converter object
	 * @param smb13
	 *            converts symbols of first finite tree automaton into symbols
	 *            of result finite tree automaton
	 * @param smb23
	 *            converts symbols of second finite tree automaton into symbols
	 *            of result finite tree automaton
	 * @param fc
	 *            {@link FTACreator} for the result finite tree automaton and
	 *            its rules
	 * 
	 * @return a finite tree automaton that recognizes exactly the union of the
	 *         languages of the given finite tree tree automata
	 */
	public static <Q1 extends State, F1 extends RankedSymbol, Q2 extends State, F2 extends RankedSymbol, Q3 extends State, F3 extends RankedSymbol, R extends FTARule<F3, Q3>, T extends FTA<F3, Q3, R>> T union(
			FTA<F1, Q1, ? extends FTARule<F1, Q1>> fta1,
					FTA<F2, Q2, ? extends FTARule<F2, Q2>> fta2, Converter<Q1, Q3> c13,
							Converter<Q2, Q3> c23, Converter<F1, F3> smb13,
							Converter<F2, F3> smb23, FTACreator<F3, Q3, R, T> fc) {
		Set<F3> newAlphabet = new HashSet<F3>();
		Set<Q3> newStates = new HashSet<Q3>();
		Set<Q3> newFinals = new HashSet<Q3>();
		Set<R> newRules = new HashSet<R>();
		Map<F1, F3> symbols1 = new HashMap<F1, F3>();
		Map<F2, F3> symbols2 = new HashMap<F2, F3>();
		Map<Q1, Q3> states1 = new HashMap<Q1, Q3>();
		Map<Q2, Q3> states2 = new HashMap<Q2, Q3>();

		// first step: calculate conversion of states and symbols
		for (Q1 q1 : fta1.getStates())
			states1.put(q1, c13.convert(q1));

		for (Q2 q2 : fta2.getStates())
			states2.put(q2, c23.convert(q2));

		for (F1 f1 : fta1.getAlphabet())
			symbols1.put(f1, smb13.convert(f1));

		for (F2 f2 : fta2.getAlphabet())
			symbols2.put(f2, smb23.convert(f2));

		// second step: collect all states and final states
		newStates.addAll(states1.values());
		newStates.addAll(states2.values());

		for (Q1 qf1 : fta1.getFinalStates())
			newFinals.add(states1.get(qf1));
		for (Q2 qf2 : fta2.getFinalStates())
			newFinals.add(states2.get(qf2));

		// third step: collect all symbols
		newAlphabet.addAll(symbols1.values());
		newAlphabet.addAll(symbols2.values());

		// fourth step: translate rules...

		// ...of first automaton...
		for (FTARule<F1, Q1> r1 : fta1.getRules()) {
			F3 symbol = symbols1.get(r1.getSymbol());
			Q3 destState = c13.convert(r1.getDestState()); //states1.get(r1.getDestState());
			List<Q3> srcStates = new LinkedList<Q3>();
			for (Q1 srcState : r1.getSrcStates())
				srcStates.add(states1.get(srcState));
			newRules.add(fc.createRule(symbol, srcStates, destState));
		}

		// ...of second automaton
		for (FTARule<F2, Q2> r2 : fta2.getRules()) {
			F3 symbol = symbols2.get(r2.getSymbol());
			Q3 destState = c23.convert(r2.getDestState()); //states2.get(r2.getDestState());
			List<Q3> srcStates = new LinkedList<Q3>();
			for (Q2 srcState : r2.getSrcStates())
				srcStates.add(states2.get(srcState));
			newRules.add(fc.createRule(symbol, srcStates, destState));
		}
		
		// now we have collected all data
		return fc.createFTA(newAlphabet, newStates, newFinals, newRules);

	}

	/**
	 * Given a collection of rules, groups them by the states, which occur as
	 * source states and the position in the source state list. In particular, a
	 * map m is returned which maps every state which occurs as source state in
	 * a rule and every possible number i to all rules, in which q occurs in the
	 * source state list at position i.
	 * 
	 * @param <F>
	 *            symbol type of rules to be examined
	 * @param <Q>
	 *            state type of rules to be examined
	 * @param rules
	 *            the rules which are to be grouped
	 * @return a map m is returned which maps every state which occurs as source
	 *         state in a rule and every possible number i to all rules, in
	 *         which q occurs in the source state list at position i.
	 */
	private static <F extends RankedSymbol, 
	Q extends State> 
	Map<Q, Map<Pair<F,Integer>, Collection<FTARule<F,Q>>>> groupRulesBySrcState(Set<? extends FTARule<F,Q>> rules) {
		Map<Q, Map<Pair<F, Integer>, Collection<FTARule<F, Q>>>> ret = new HashMap<Q, Map<Pair<F,Integer>,Collection<FTARule<F,Q>>>>();
		for (FTARule<F,Q> r: rules) {
			int index = 0;
			for (Q qsrc: r.getSrcStates()) {
				Map<Pair<F,Integer>, Collection<FTARule<F,Q>>> qsrcRules;
				if (ret.containsKey(qsrc))
					qsrcRules = ret.get(qsrc);
				else {
					qsrcRules = new HashMap<Pair<F,Integer>,Collection<FTARule<F,Q>>>();
					ret.put(qsrc, qsrcRules);
				}
				Pair<F,Integer> key = new Pair<F,Integer>(r.getSymbol(), index);
				Collection<FTARule<F,Q>> qsrcKeyRules;
				if (qsrcRules.containsKey(key)) {
					qsrcKeyRules = qsrcRules.get(key);
				}
				else {
					qsrcKeyRules = new LinkedList<FTARule<F,Q>>();
					qsrcRules.put(key, qsrcKeyRules);
				}
				qsrcKeyRules.add(r);
			}
			index++;
		}

		return ret;
	}

	/**
	 * Given two finite tree automata, constructs a finite tree automaton which
	 * accepts a tree if and only if both finite tree automata accept it. The
	 * suffix "BU" stands for bottom-up reduction.<br>
	 * That means, the algorithm consists of a {@link FTAOps#intersectionWR
	 * product construction} with additional reduction, such that in the
	 * resulting automaton every state is reachable.<br>
	 * <em>In detail:</em><br>
	 * The state (q,r) is reachable if and only if there is n>=0, a rule
	 * f(q_1,...,q_n) -> q of the first automaton and a rule f(r_1,...,r_n) -> r
	 * of the second automaton such that (q_1,r_1),...,(q_n,r_n) are reachable.
	 * Reachable states and corresponding rules are added, until there is no
	 * more reachable state and thus no change in the set of new states.
	 * 
	 * @param <F>
	 *            symbol type of all three finite tree automata. Since the
	 *            result recognizes the intersection of the two operands'
	 *            languages, all three finite tree automata must have the same
	 *            symbol type.
	 * @param <Q1>
	 *            state type of the first finite tree automaton
	 * @param <Q2>
	 *            state type of the first finite tree automaton
	 * @param <Q3>
	 *            state type of the result finite tree automaton
	 * @param <R>
	 *            state type of the result finite tree automaton
	 * @param <T>
	 *            type of first finite tree automaton
	 * @param fta1
	 *            first finite tree automaton for the intersection
	 * @param fta2
	 *            second finite tree automaton for the intersection
	 * @param pc
	 *            takes pairs of states of the two finite tree automata to be
	 *            intersected and returns a state of the result state type. Must
	 *            be injective, that means, the converted versions of two
	 *            different pairs must be different
	 * @param fc
	 *            {@link FTACreator} for creating the result automaton and its
	 *            rules
	 * @return finite tree automaton which accepts a tree if and only if both
	 *         finite tree automata accept it
	 */
	public static <Q1 extends State, Q2 extends State, Q3 extends State, F extends RankedSymbol, R extends FTARule<F, Q3>, T extends FTA<F, Q3, R>> T intersectionBU(
			FTA<F, Q1, ? extends FTARule<F, Q1>> fta1,
					FTA<F, Q2, ? extends FTARule<F, Q2>> fta2,
							Converter<Pair<Q1, Q2>, Q3> pc, FTACreator<F, Q3, R, T> fc) {
		//System.out.println("precalculation on first automaton...");
		Map<Q1, Map<Pair<F,Integer>, Collection<FTARule<F,Q1>>>> rules1BySrcStates = groupRulesBySrcState(fta1.getRules());
		//System.out.println("precalculation on second automaton...");
		Map<Q2, Map<Pair<F,Integer>, Collection<FTARule<F,Q2>>>> rules2BySrcStates = groupRulesBySrcState(fta2.getRules());
		LinkedList<Pair<FTARule<F, Q1>, FTARule<F, Q2>>> worklist = new LinkedList<Pair<FTARule<F, Q1>, FTARule<F, Q2>>>();
		Set<Pair<Q1, Q2>> pairStates = new HashSet<Pair<Q1, Q2>>();
		ArrayList<Pair<FTARule<F, Q1>, FTARule<F, Q2>>> pairRules = new ArrayList<Pair<FTARule<F, Q1>, FTARule<F, Q2>>>();
		Set<Pair<Q1, Q2>> pairFinals = new HashSet<Pair<Q1, Q2>>();
		//System.out.println("initializing work list...");
		for (FTARule<F,Q1> r1: fta1.getRules())
			if (r1.getSymbol().getArity()==0) {
				for (FTARule<F,Q2> r2: fta2.getSymbolRules(r1.getSymbol())) {
					worklist.add(new Pair<FTARule<F,Q1>, FTARule<F,Q2>>(r1,r2));
				}
			}

		//System.out.println("starting work list iteration with "+worklist.size()+" elements.");
		while (!(worklist.isEmpty())) {
			Pair<FTARule<F, Q1>, FTARule<F, Q2>> next = worklist.poll();
			Iterator<Q1> states1 = next.getFirst().getSrcStates().listIterator();
			Iterator<Q2> states2 = next.getSecond().getSrcStates().listIterator();
			boolean allContained = true;
			Pair<Q1,Q2> statePair = new Pair<Q1,Q2>(null,null);
			while (states1.hasNext()) {
				statePair.setFirst(states1.next());
				statePair.setSecond(states2.next());
				if (!pairStates.contains(statePair)) {
					allContained = false;
					break;
				}
			}

			if (allContained) {
				Q1 q1 = next.getFirst().getDestState();
				Q2 q2 = next.getSecond().getDestState();
				statePair.setFirst(q1);
				statePair.setSecond(q2);
				boolean isNew = pairStates.add(statePair);
				pairRules.add(next);
				if (isNew) {
					if (fta1.getFinalStates().contains(q1)
							&& fta2.getFinalStates().contains(q2))
						pairFinals.add(statePair);

					if (rules1BySrcStates.containsKey(q1) && rules2BySrcStates.containsKey(q2)) {
						for (Pair<F,Integer> key: rules1BySrcStates.get(q1).keySet()) {
							if (rules2BySrcStates.get(q2).containsKey(key)) {
								for (FTARule<F,Q1> r1: rules1BySrcStates.get(q1).get(key))
									for (FTARule<F,Q2> r2: rules2BySrcStates.get(q2).get(key)) {
										worklist.add(new Pair<FTARule<F, Q1>, FTARule<F, Q2>>(r1,r2));
									}
							}
						}
					}
					//System.out.println("work list has grown by "+(worklist.size()-wlsize)+" items.");
				}
			}
		}

		Map<Pair<Q1, Q2>, Q3> newStates = new HashMap<Pair<Q1, Q2>, Q3>();
		LinkedList<Q3> newFinals = new LinkedList<Q3>();
		LinkedList<R> newRules = new LinkedList<R>();
		for (Pair<Q1, Q2> statePair : pairStates) {
			newStates.put(statePair, pc.convert(statePair));
			if (pairFinals.contains(statePair))
				newFinals.add(newStates.get(statePair));
		}

		for (Pair<FTARule<F, Q1>, FTARule<F, Q2>> rulePair : pairRules) {
			List<Q3> srcStates = new ArrayList<Q3>();
			Iterator<Q1> states1 = rulePair.getFirst().getSrcStates().listIterator();
			Iterator<Q2> states2 = rulePair.getSecond().getSrcStates().listIterator();
			Pair<Q1, Q2> p = new Pair<Q1, Q2>(null, null);
			while (states1.hasNext()) {
				p.setFirst(states1.next());
				p.setSecond(states2.next());
				srcStates.add(newStates.get(p));
			}
			p.setFirst(rulePair.getFirst().getDestState());
			p.setSecond(rulePair.getSecond().getDestState());
			newRules.add(fc.createRule(rulePair.getFirst().getSymbol(),srcStates, newStates.get(p)));
		}
		LinkedList<F> newAlphabet = new LinkedList<F>(fta1.getAlphabet());
		newAlphabet.addAll(fta2.getAlphabet());
		return fc.createFTA(newAlphabet, Collections.<Q3>emptyList(), newFinals, newRules);

		//		 Set<Pair<Q1,Q2>> pairStates = new HashSet<Pair<Q1,Q2>>();
		//		 Set<Pair<Q1,Q2>> pairFinals = new HashSet<Pair<Q1,Q2>>();
		//		 Set<Pair<FTARule<F,Q1>,FTARule<F,Q2>>> pairRules = new
		//		 HashSet<Pair<FTARule<F,Q1>,FTARule<F,Q2>>>();
		//		 Pair<Q1,Q2> s = new Pair<Q1,Q2>(null,null);
		//		 Q1 q;
		//		 Q2 r;
		//		 boolean done = false;
		//		 while (!done) {
		//		 done = true;
		//		 for (FTARule<F,Q1> r1: fta1.getRules())
		//		 for (FTARule<F,Q2> r2: fta2.getSymbolRules(r1.getSymbol())) {
		//		 boolean allContained = true;
		//		 Iterator<Q1> states1 = r1.getSrcStates().listIterator();
		//		 Iterator<Q2> states2 = r2.getSrcStates().listIterator();
		//		 while (states1.hasNext()) {
		//		 q = states1.next();
		//		 r = states2.next();
		//		 s.setFirst(q);
		//		 s.setSecond(r);
		//		 if (!pairStates.contains(s)) {
		//		 allContained = false;
		//		 break;
		//		 }
		//		 }
		//		 if (allContained) {
		//		 Pair<FTARule<F,Q1>,FTARule<F,Q2>> rulePair = new
		//		 Pair<FTARule<F,Q1>,FTARule<F,Q2>>(r1,r2);
		//		 Pair<Q1,Q2> p = new Pair<Q1,Q2>(r1.getDestState(),r2.getDestState());
		//		 if (!pairStates.contains(p))
		//		 done = false;
		//		 pairStates.add(p);
		//		 pairRules.add(rulePair);
		//		 if (fta1.getFinalStates().contains(r1.getDestState()) &&
		//		 (fta2.getFinalStates().contains(r2.getDestState())))
		//		 pairFinals.add(p);
		//		 }
		//		 }
		//		 }
		//				
		//		 Map<Pair<Q1,Q2>,Q3> newStates = new HashMap<Pair<Q1,Q2>,Q3>();
		//		 LinkedList<Q3> newFinals = new LinkedList<Q3>();
		//		 LinkedList<R> newRules = new LinkedList<R>();
		//		 for (Pair<Q1,Q2> statePair: pairStates) {
		//		 newStates.put(statePair, pc.convert(statePair));
		//		 if (pairFinals.contains(statePair))
		//		 newFinals.add(newStates.get(statePair));
		//		 }
		//				
		//		 for (Pair<FTARule<F,Q1>, FTARule<F,Q2>> rulePair: pairRules) {
		//		 List<Q3> srcStates = new ArrayList<Q3>();
		//		 Iterator<Q1> states1 =
		//		 rulePair.getFirst().getSrcStates().listIterator();
		//		 Iterator<Q2> states2 =
		//		 rulePair.getSecond().getSrcStates().listIterator();
		//		 Pair<Q1,Q2> p = new Pair<Q1,Q2>(null,null);
		//		 while (states1.hasNext()) {
		//		 p.setFirst(states1.next());
		//		 p.setSecond(states2.next());
		//		 srcStates.add(newStates.get(p));
		//		 }
		//		 p.setFirst(rulePair.getFirst().getDestState());
		//		 p.setSecond(rulePair.getSecond().getDestState());
		//		 newRules.add(fc.createRule(rulePair.getFirst().getSymbol(),
		//		 srcStates, newStates.get(p)));
		//		 }
		//		 LinkedList<F> newAlphabet = new LinkedList<F>(fta1.getAlphabet());
		//		 newAlphabet.addAll(fta2.getAlphabet());
		//		 return
		//		 fc.createFTA(newAlphabet,newStates.values(),newFinals,newRules);

	}

	/**
	 * Given two finite tree automata, constructs a finite tree automaton which
	 * accepts a tree if and only if both automata accept it.<br>
	 * <br>
	 * <em>Algorithm:</em><br>
	 * <em> 1. Step: Initializing </em> <br>
	 * All possible pairs of states of first and second automaton are put on a
	 * work list.<br>
	 * The rules of the first automaton are sorted by destination state.<br>
	 * The rules of the second automaton are by symbol.<br>
	 * <em> 2.Step: Process work list </em><br>
	 * For an element of the work list it is checked which rules have this as
	 * destination states.<br>
	 * If there is a rule of the first automaton with symbol f and one of the
	 * second with the same symbol, a new rule with the corresponding pair
	 * states is constructed.
	 * 
	 * @param <F>
	 *            symbol type of all three finite tree automata. Since the
	 *            result recognizes the intersection of the two operands'
	 *            languages, all three finite tree automata must have the same
	 *            symbol type.
	 * @param <Q1>
	 *            state type of the first finite tree automaton
	 * @param <Q2>
	 *            state type of the first finite tree automaton
	 * @param <Q3>
	 *            state type of the result finite tree automaton
	 * @param <R>
	 *            state type of the result finite tree automaton
	 * @param <T>
	 *            type of the first finite tree automaton
	 * @param fta1
	 *            first finite tree automaton for the intersection
	 * @param fta2
	 *            second finite tree automaton for the intersection
	 * @param pc
	 *            state converter that takes pairs of states of the two automata
	 *            to be intersected and returns a state of the result state
	 *            type. Must be injective, that means, the converted versions of
	 *            two different pairs must be different
	 * @param fc
	 *            {@link FTACreator} for creating the result automaton and its
	 *            rules
	 * @return finite tree automaton which accepts a tree if and only if both
	 *         finite tree automata accept it
	 */
	public static 
	<F extends RankedSymbol, 
	Q1 extends State, 
	Q2 extends State, 
	Q3 extends State, 
	R extends FTARule<F, Q3>, 
	T extends FTA<F, Q3, R>> 
	T intersectionTD(FTA<F, Q1, ? extends FTARule<F, Q1>> fta1,
			FTA<F, Q2, ? extends FTARule<F, Q2>> fta2,
					Converter<Pair<Q1, Q2>, Q3> pc, FTACreator<F, Q3, R, T> fc) {


		/* group the rules of the first automaton by destination state */
		Map<Q1, Collection<FTARule<F,Q1>>> rules1ByDestState = new HashMap<Q1, Collection<FTARule<F,Q1>>>();
		for (FTARule<F,Q1> r1: fta1.getRules()) {
			Q1 q = r1.getDestState();
			Collection<FTARule<F,Q1>> qRules;
			if (rules1ByDestState.containsKey(q))
				qRules = rules1ByDestState.get(q);
			else {
				qRules = new LinkedList<FTARule<F,Q1>>();
				rules1ByDestState.put(q, qRules);
			}
			qRules.add(r1);
		}

		/* group the rules of the second automaton by destination state and symbol */
		Map<Pair<F,Q2>, Collection<FTARule<F,Q2>>> rules2ByDSSymb = new HashMap<Pair<F,Q2>, Collection<FTARule<F,Q2>>>();
		for (FTARule<F,Q2> r2: fta2.getRules()) {
			Pair<F,Q2> key = new Pair<F,Q2>(r2.getSymbol(),r2.getDestState());
			Collection<FTARule<F,Q2>> keyRules;
			if (rules2ByDSSymb.containsKey(key))
				keyRules = rules2ByDSSymb.get(key);
			else {
				keyRules = new LinkedList<FTARule<F,Q2>>();
				rules2ByDSSymb.put(key, keyRules);
			}
			keyRules.add(r2);
		}

		LinkedList<Pair<FTARule<F,Q1>, FTARule<F,Q2>>> worklist = new LinkedList<Pair<FTARule<F,Q1>,FTARule<F,Q2>>>();
		HashSet<Pair<Q1,Q2>> pairStates = new HashSet<Pair<Q1,Q2>>();
		HashSet<Pair<Q1,Q2>> pairFinals = new HashSet<Pair<Q1,Q2>>();
		LinkedList<Pair<FTARule<F, Q1>, FTARule<F, Q2>>> pairRules = new LinkedList<Pair<FTARule<F,Q1>,FTARule<F,Q2>>>();



		/* initialize worklist */
		for (Q1 qf1: fta1.getFinalStates()) {
			if (rules1ByDestState.containsKey(qf1)) {
				for (FTARule<F,Q1> r1: rules1ByDestState.get(qf1)) {
					for (Q2 qf2: fta2.getFinalStates()) {
						Pair<F,Q2> key = new Pair<F,Q2>(r1.getSymbol(),qf2);
						if (rules2ByDSSymb.containsKey(key))
							for (FTARule<F,Q2> r2: rules2ByDSSymb.get(key)) {
								Pair<Q1,Q2> pairFinal = new Pair<Q1,Q2>(r1.getDestState(), r2.getDestState());
								worklist.add(new Pair<FTARule<F,Q1>, FTARule<F,Q2>>(r1,r2));
								pairStates.add(pairFinal);
								pairFinals.add(pairFinal);
							}
					}
				}
			}
		}
		/* process worklist */
		while (!worklist.isEmpty()) {
			Pair<FTARule<F,Q1>, FTARule<F,Q2>> next = worklist.poll();
			Iterator<Q1> iter1 = next.getFirst().getSrcStates().listIterator();
			Iterator<Q2> iter2 = next.getSecond().getSrcStates().listIterator();
			while (iter1.hasNext()) {
				Q1 q1 = iter1.next();
				Q2 q2 = iter2.next();
				Pair<Q1,Q2> statePair = new Pair<Q1,Q2>(q1, q2);
				Pair<F,Q2> key = new Pair<F,Q2>(null, q2);

				/* if there is a source state pair (q1,q2), which has not been reached before,
				 * add all pairs of rules f(...) -> q1 and f(...) -> q2 to worklist, i.e.
				 * all pairs of rules with same symbol and right destination states. 
				 **/
				boolean isNew = pairStates.add(statePair);
				if (isNew) {
					if (rules1ByDestState.containsKey(q1)) {
						for (FTARule<F,Q1> r1: rules1ByDestState.get(q1)) {
							key.setFirst(r1.getSymbol());
							if (rules2ByDSSymb.containsKey(key)) {
								for (FTARule<F,Q2> r2: rules2ByDSSymb.get(key)) {
									worklist.add(new Pair<FTARule<F,Q1>, FTARule<F,Q2>>(r1,r2));
								}
							}
						}
					}
				}
			}
			/*
			 * if the worklist is empty, all state and rules pairs reachable from this
			 * rule pair will have been added - so we can add this rules to the set of finished rules
			 */
			pairRules.add(next);
		}


		/* last step: calculate new automaton */
		Map<Pair<Q1, Q2>, Q3> newStates = new HashMap<Pair<Q1, Q2>, Q3>();
		LinkedList<Q3> newFinals = new LinkedList<Q3>();
		LinkedList<R> newRules = new LinkedList<R>();
		for (Pair<Q1, Q2> statePair : pairStates) {
			newStates.put(statePair, pc.convert(statePair));
			if (pairFinals.contains(statePair))
				newFinals.add(newStates.get(statePair));
		}

		for (Pair<FTARule<F, Q1>, FTARule<F, Q2>> rulePair : pairRules) {
			List<Q3> srcStates = new ArrayList<Q3>();
			Iterator<Q1> states1 = rulePair.getFirst().getSrcStates().listIterator();
			Iterator<Q2> states2 = rulePair.getSecond().getSrcStates().listIterator();
			Pair<Q1, Q2> p = new Pair<Q1, Q2>(null, null);
			while (states1.hasNext()) {
				p.setFirst(states1.next());
				p.setSecond(states2.next());
				srcStates.add(newStates.get(p));
			}
			p.setFirst(rulePair.getFirst().getDestState());
			p.setSecond(rulePair.getSecond().getDestState());
			newRules.add(fc.createRule(rulePair.getFirst().getSymbol(), srcStates, newStates.get(p)));
		}
		LinkedList<F> newAlphabet = new LinkedList<F>(fta1.getAlphabet());
		newAlphabet.addAll(fta2.getAlphabet());
		return fc.createFTA(newAlphabet, newStates.values(), newFinals, newRules);
		/**
		LinkedList<F> newAlphabet = new LinkedList<F>();
		LinkedList<Q3> newFinals = new LinkedList<Q3>();
		LinkedList<R> newRules = new LinkedList<R>();

		// save out of which states the new states have been created
		Map<Q3, Pair<Q1, Q2>> statePairs = new HashMap<Q3, Pair<Q1, Q2>>();


		LinkedList<Q3> worklist = new LinkedList<Q3>();
		List<Q3> newSrcStates = new LinkedList<Q3>();
		Q1 q1;
		Q2 q2;
		ListIterator<Q1> iter1;
		ListIterator<Q2> iter2;
		Q3 next;

		// first step: initialize work list
		// put all pairs of first and second automata states on the work list
		for (Q1 qf1 : fta1.getFinalStates())
			for (Q2 qf2 : fta2.getFinalStates()) {
				Q3 p = pc.convert(new Pair<Q1, Q2>(qf1, qf2));
				statePairs.put(p, new Pair<Q1, Q2>(qf1, qf2));
				worklist.push(p);
				newFinals.add(p);
			}

		// construct a map which maps each state of the first automaton
		// to all rules, which have this state as destination state
		Map<Q1, Set<FTARule<F, Q1>>> dstRules1 = new HashMap<Q1, Set<FTARule<F, Q1>>>();
		for (FTARule<F, Q1> r : fta1.getRules()) {
			Q1 q = r.getDestState();
			Set<FTARule<F, Q1>> qRules;
			if (dstRules1.containsKey(q))
				qRules = dstRules1.get(r.getDestState());
			else {
				qRules = new HashSet<FTARule<F, Q1>>();
				dstRules1.put(q, qRules);
			}
			qRules.add(r);
		}

		// second step: process work list
		while (!worklist.isEmpty()) {
			// take an element of the work list
			next = worklist.poll();
			q1 = statePairs.get(next).getFirst();
			q2 = statePairs.get(next).getSecond();


			// if the first state is not reachable in the first automaton
			// take next element of the work list

			// check all rules f(...)->q1 of the first automaton
			if (dstRules1.containsKey(q1))
				for (FTARule<F, Q1> r1 : dstRules1.get(q1)) {
				// search in the rules of the second automaton
				// rules like f(...)->q2
				for (FTARule<F, Q2> r2 : fta2.getSymbolRules(r1.getSymbol()))
					if (r2.getDestState().equals(q2)) {
						// look at the rule f((q1,r1),...,(qn,rn)) -> next
						// if there is a (qi,ri) which is not already processed,
						// we add it to the work list

						iter1 = r1.getSrcStates().listIterator();
						iter2 = r2.getSrcStates().listIterator();

						newSrcStates.clear();
						while (iter1.hasNext()) {
							Q1 qsrc1 = iter1.next();
							Q2 qsrc2 = iter2.next();
							Q3 p = pc.convert(new Pair<Q1, Q2>(qsrc1, qsrc2));
							newSrcStates.add(p);
							if (!statePairs.containsKey(p)) {
								worklist.add(p);
								statePairs.put(p, new Pair<Q1, Q2>(qsrc1, qsrc2));
							}
						}
						// add a new rule f(p1,...,pn) -> (p)
						// where p is created out of q1,q2 and pi in the same
						// way.
						newRules.add(fc.createRule(r1.getSymbol(), newSrcStates, next));
					}
			}
		}

		newAlphabet.addAll(fta1.getAlphabet());
		newAlphabet.addAll(fta2.getAlphabet());

		return fc.createFTA(newAlphabet, statePairs.keySet(), newFinals,newRules);*/
	}

	/**
	 * Given two finite tree automata, constructs a finite tree automaton which
	 * accepts a tree if and only if both automata accept it.<br>
	 * <br>
	 * The suffix "WR" stands for "without reduction", that means, a full
	 * product construction is carried out. Explicitly, the resulting automaton
	 * is constructed as follows:<br>
	 * <ul>
	 * <li> <em>Alphabet: </em> The union of the alphabets of the first and
	 * second automaton</li>
	 * <li> <em>Set of states:</em> Q_1 x Q_2, where Q_1 is the set of states
	 * of the first automaton and Q_2 is the set of states of the second automaton.</li>
	 * <li> <em>Set of final states:</em> F_1 x F_2, if F_1 is the set of final
	 * states of the first automaton and F_2 is the set of final states of the
	 * second automaton</li>
	 * <li> <em>Set of rules: </em> For every rule f(q_1,...,q_n) -> q of the
	 * first automaton and every rule f(r_1,...,r_n) -> r of the second
	 * automaton, there is a rule f((q_1,r_1),...,(q_n,r_n)) -> (q,r) of the
	 * resulting automaton.
	 * 
	 * @param <F>
	 *            symbol type of all three automata. Since the result recognizes
	 *            the intersection of the two operands' languages, all three
	 *            automata must have the same symbol type.
	 * @param <Q1>
	 *            state type of the first finite tree automaton
	 * @param <Q2>
	 *            state type of the first finite tree automaton
	 * @param <Q3>
	 *            state type of the result finite tree automaton
	 * @param <R>
	 *            state type of the result finite tree automaton
	 * @param <T>
	 *            type of the first finite tree automaton
	 * @param fta1
	 *            first finite tree automaton for the intersection
	 * @param fta2
	 *            second finite tree automaton for the intersection
	 * @param pc
	 *            state converter that takes pairs of states of the two automata
	 *            to be intersected and returns a state of the result state
	 *            type. Must be injective, that means, the converted versions of
	 *            two different pairs must be different
	 * @param fc
	 *            {@link FTACreator} for creating the result automaton and its
	 *            rules
	 * 
	 * @return finite tree automaton which accepts a tree if and only if both
	 *         finite tree automata accept it
	 */
	public static <F extends RankedSymbol, Q1 extends State, Q2 extends State, Q3 extends State, R extends FTARule<F, Q3>, T extends FTA<F, Q3, R>> T intersectionWR(
			FTA<F, Q1, ? extends FTARule<F, Q1>> fta1,
					FTA<F, Q2, ? extends FTARule<F, Q2>> fta2,
							Converter<Pair<Q1, Q2>, Q3> pc, FTACreator<F, Q3, R, T> fc) {
		LinkedList<F> newAlphabet = new LinkedList<F>(fta1.getAlphabet());
		newAlphabet.addAll(fta2.getAlphabet());
		HashMap<Pair<Q1,Q2>,Q3> newStates = new HashMap<Pair<Q1,Q2>, Q3>();
		LinkedList<R> newRules = new LinkedList<R>();
		HashMap<Pair<Q1,Q2>,Q3> newFinals = new HashMap<Pair<Q1,Q2>, Q3>();


		// map each pair of states to state of resulting type
		for (Q1 q1: fta1.getStates())
			for (Q2 q2: fta2.getStates()) {
				Pair<Q1,Q2> statePair = new Pair<Q1,Q2>(q1,q2);
				Q3 newState = pc.convert(statePair);
				newStates.put(statePair, newState);
				if (fta1.getFinalStates().contains(q1) && fta2.getFinalStates().contains(q2))
					newFinals.put(statePair, newState);
			}

		/*
		 * for each pair of rules f(q1,...,qn)->q of the first automaton 
		 * and f(r1,...,rn)->r of the second automaton, add a rule
		 * f((q1,r1),...,(qn,rn)) -> (q,r)
		 */
		for (FTARule<F, Q1> r1d1 : fta1.getRules()) {
			for (FTARule<F, Q2> r2d2 : fta2.getSymbolRules(r1d1.getSymbol())) {
				LinkedList<Q3> src = new LinkedList<Q3>();
				Iterator<Q1> i1 = r1d1.getSrcStates().listIterator();
				Iterator<Q2> i2 = r2d2.getSrcStates().listIterator();
				// go through the source states and 'replace' them with
				// their pairs from hash
				while (i1.hasNext()) {
					Q1 q1 = i1.next();
					Q2 q2 = i2.next();
					Q3 pair = newStates.get(new Pair<Q1,Q2>(q1,q2));
					src.add(pair);
				}
				// 'replace' the destination states with their pair 
				newRules.add(fc.createRule(r1d1.getSymbol(), src, newStates.get(new Pair<Q1, Q2>(r1d1.getDestState(), r2d2.getDestState()))));
			}
		}

		/* all data is collected */
		return fc.createFTA(newAlphabet, newStates.values(), newFinals.values(), newRules);
	}

	/**
	 * Given two finite tree automata, constructs a finite tree automaton which
	 * recognizes a tree if and only if it is recognized by the first but not by
	 * the second finite tree automaton.<br>
	 * <br>
	 * This is realized by an intersection of the first finite tree automaton
	 * with the complement of the second one.
	 * 
	 * @param <F>
	 *            type of the symbols
	 * @param <Q1>
	 *            type of the states of the first finite tree automaton
	 * @param <Q2>
	 *            type of the states of the second finite tree automaton
	 * @param <Q20>
	 *            type of the states of the complemented second finite tree
	 *            automaton
	 * @param <R20>
	 *            type of the rules of the complemented second finite tree
	 *            automaton
	 * @param <T20>
	 *            type of the complemented second finite tree automaton
	 * @param <Q3>
	 *            type of the states of the difference finite tree automaton
	 * @param <R3>
	 *            type of the rules of the difference finite tree automaton
	 * @param <T3>
	 *            type of the difference finite tree automaton
	 * @param fta1
	 *            first finite tree automaton for the basic language
	 * @param fta2
	 *            second finite tree automaton for the language which shall be
	 *            subtracted
	 * @param sc2
	 *            state converter Q2 to Q02 to complement the second finite tree
	 *            automaton
	 * @param fc20
	 *            FTACreator to create the complemented second finite tree
	 *            automaton
	 * @param pc
	 *            pair converter (Q1,Q20) to Q3 to union the first and the
	 *            complemented second finite tree automaton
	 * @param fc3
	 *            {@link FTACreator} to create the difference finite tree
	 *            automaton
	 * @return a finite tree automaton which recognizes a tree if and only if it
	 *         is recognized by the first but not by the second finite tree
	 *         automaton.
	 */
	public static <F extends RankedSymbol, Q1 extends State, Q2 extends State, Q20 extends State, R20 extends FTARule<F, Q20>, T20 extends FTA<F, Q20, R20>, Q3 extends State, R3 extends FTARule<F, Q3>, T3 extends FTA<F, Q3, R3>> T3 difference(
			FTA<F, Q1, ? extends FTARule<F, Q1>> fta1,
					FTA<F, Q2, ? extends FTARule<F, Q2>> fta2,
							Converter<Set<Q2>, Q20> sc2, FTACreator<F, Q20, R20, T20> fc20,
							Converter<Pair<Q1, Q20>, Q3> pc, FTACreator<F, Q3, R3, T3> fc3) {

		// difference
		// complementAlphabet(fta2,alphabet,sc2,fc20);

		HashSet<F> alphabet2without1 = new HashSet<F>();
		for (F f : fta2.getAlphabet())
			if (!fta1.getAlphabet().contains(f))
				alphabet2without1.add(f);

		if (!alphabet2without1.isEmpty())
			// fta2 has symbols, which fta1 does not have. So we could save
			// time, if we first filter
			// these symbols
			return intersectionBU(fta1, complementAlphabet(filter(fta2, fta1
					.getAlphabet()), fta1.getAlphabet(), sc2, fc20), pc, fc3);
		else
			// Every symbol of fta2 is a symbol of fta1, so no filtering is
			// neccessary
			return intersectionBU(fta1, complementAlphabet(fta2, fta1
					.getAlphabet(), sc2, fc20), pc, fc3);
	}

	/**
	 * Given a finite tree automaton, returns a version of it where the symbols
	 * are contained in the given alphabet. This method is used to make
	 * difference faster: <br>
	 * This is achieved by filtering the rules (and maybe associated states) of
	 * the second automaton, whose symbol is not contained in the first
	 * automaton. Then, the complement can be executed with respect to the first
	 * automaton's alphabet.
	 * 
	 * @param <Q>
	 *            state type of the finite tree automaton to be filtered
	 * @param <F>
	 *            symbol type of the finite tree automaton to be filtered
	 * @param fta
	 *            finite tree automaton to be filtered
	 * @param alphabet
	 *            symbols which shall stay in returned finite tree automaton
	 * 
	 * @return finite tree automaton which contains only rules whose symbol is
	 *         contained in the given alphabet
	 * 
	 * @see #difference(FTA, FTA, Converter, FTACreator, Converter, FTACreator)
	 */
	protected static <Q extends State, F extends RankedSymbol> FTA<F, Q, ? extends FTARule<F, Q>> filter(
			final FTA<F, Q, ? extends FTARule<F, Q>> fta, Set<F> alphabet) {
		final FTARuleSet<F, Q, FTARule<F, Q>> retRules = new SimpleFTARuleSet<F, Q, FTARule<F, Q>>();
		final HashSet<Q> retStates = new HashSet<Q>();
		final HashSet<Q> retFinals = new HashSet<Q>();
		final HashSet<F> retAlphabet = new HashSet<F>();
		for (FTARule<F, Q> r : fta.getRules())
			if (alphabet.contains(r.getSymbol())) {
				retAlphabet.add(r.getSymbol());
				retRules.add(r);
				retStates.addAll(r.getSrcStates());
				retStates.add(r.getDestState());
				for (Q qsrc : r.getSrcStates())
					if (fta.getFinalStates().contains(qsrc))
						retFinals.add(qsrc);
				if (fta.getFinalStates().contains(r.getDestState()))
					retFinals.add(r.getDestState());
			}
		return new FTA<F, Q, FTARule<F, Q>>() {

			@Override
			public Set<F> getAlphabet() {
				return retAlphabet;
			}

			@Override
			public Set<Q> getFinalStates() {
				return retFinals;
			}

			@Override
			public Set<FTARule<F, Q>> getRules() {
				return retRules;
			}

			@Override
			public Set<Q> getStates() {
				return retStates;
			}

			@Override
			public Set<FTARule<F, Q>> getSymbolRules(F f) {
				return retRules.getSymbolRules(f);
			}

		};
	}

	/**
	 * Given a tree containing some constants (symbols with arity 0) that are to
	 * be replaced and a map mapping exactly these symbols to regular tree
	 * languages represented by finite tree automata, constructs a finite tree
	 * automaton which recognizes exactly the trees which are obtained by
	 * substituting the specified constants by trees of the corresponding
	 * languages. <br>
	 * <br>
	 * <em> Algorithm:</em><br>
	 * <ol>
	 * <li>For every language the automaton states and rules are made unique and
	 * the union alphabet is builded up.</li>
	 * <li>The states and rules for the new automaton are collected.</li>
	 * <li>The automaton for the tree where the variables are replaced by the
	 * final states of the automata of the corresponding languages is
	 * constructed. ({@link FTAOps#buildAutomatonForOneTree})</li>
	 * </ol>
	 * 
	 * @param <F>
	 *            type of the symbols of the given finite tree automata and
	 *            trees
	 * @param <Q>
	 *            type of the states of the given finite tree automata
	 *            representing languages
	 * @param <Q0>
	 *            type of the states of the resulting finite tree automaton
	 * @param <R0>
	 *            type of the rules of the resulting finite tree automaton
	 * @param <T>
	 *            type of the resulting finite tree automaton
	 * @param tree
	 *            tree with variables, which shall be replaced by the given
	 *            regular languages
	 * @param languages
	 *            given regular languages, given by a map which maps each
	 *            constant (symbol with arity 0) which shall be replaced, to a
	 *            finite tree automaton.
	 * @param intStateConv
	 *            converts a pair consisting of a state and an integer into a
	 *            state - conversion must be injective and resulting states must
	 *            not be equal to states resulting from the other converters
	 * @param intConv
	 *            converts an integer into a state - conversion must be
	 *            injective and resulting states must not be equal to states
	 *            resulting from the other converters
	 * @param treeStateConv
	 *            converts variable tree into a state - conversion must be
	 *            injective and resulting states must not be equal to states
	 *            resulting from the other converters
	 * @param fc
	 *            {@link FTACreator} to create rules, the resulting finite tree
	 *            automaton and finite tree automaton with epsilon rules
	 *            constructed in an intermediate step
	 * @return finite tree automaton which recognizes exactly the trees which
	 *         are obtained by substituting each variable by a tree of the
	 *         corresponding language.
	 */
	public static <F extends RankedSymbol, Q extends State, Q0 extends State, R0 extends FTARule<F, Q0>, T extends FTA<F, Q0, R0>> T substitute(
			Tree<F> tree,
			Map<? extends F, ? extends FTA<F, Q, ? extends FTARule<F, Q>>> languages,
					Converter<? super Pair<Q, Integer>, Q0> intStateConv,
					Converter<? super Integer, Q0> intConv,
					Converter<? super Tree<F>, Q0> treeStateConv,
					FTACreator<F, Q0, R0, T> fc) {
		// check if all symbols which shall be replaced have arity 0

		for (F f : languages.keySet()) {
			if (f.getArity() != 0) {
				throw new IllegalArgumentException(
				"All symbols which shall be replaced must have arity 0.");
			}
		}

		// union of the alphabets
		Set<F> alphabet = new HashSet<F>();

		// first: for every language make the automaton states and
		// rules unique and build the union alphabet
		Map<F, FTA<F, Q0, R0>> langRenamed = new HashMap<F, FTA<F, Q0, R0>>();
		Map<Q, Q0> newnames = new HashMap<Q, Q0>();
		int i = 0;
		for (F vark : languages.keySet()) {
			FTA<F, Q, ? extends FTARule<F, Q>> l = languages.get(vark);
			alphabet.addAll(l.getAlphabet());
			for (Q state : l.getStates()) {
				newnames.put(state, intStateConv.convert(new Pair<Q, Integer>(
						state, i)));
			}
			langRenamed.put(vark, renameAutomatonStates(l, newnames, fc));
			i++;
			newnames.clear();
		}

		// second: get all rules, states and so on
		// final states are only those of the new automaton constructed for the
		// tree
		HashSet<Q0> states = new HashSet<Q0>();
		Set<R0> rules = new HashSet<R0>();
		HashSet<GenFTAEpsRule<Q0>> epsRules = new HashSet<GenFTAEpsRule<Q0>>();
		// in subst is for every language which shall be substituted a new state
		Map<F, Q0> subst = new HashMap<F, Q0>();

		i = 0;
		for (F key : langRenamed.keySet()) {
			FTA<F, Q0, R0> lta = langRenamed.get(key);
			states.addAll(lta.getStates());
			rules.addAll(lta.getRules());
			// make eps rules for final states of each language
			Q0 q = intConv.convert(i);
			states.add(q);
			for (Q0 fs : lta.getFinalStates()) {
				epsRules.add(new GenFTAEpsRule<Q0>(fs, q));
			}
			subst.put(key, q);
			i++;
		}

		// third: help-Method to construct automaton for the tree
		Q0 finalState = buildAutomatonForOneTree(tree, subst, states, rules,
				fc, treeStateConv);
		HashSet<Q0> finalStates = new HashSet<Q0>();
		finalStates.add(finalState);
		return fc.createFTA(alphabet, states, finalStates, rules, epsRules);
	}

	/**
	 * Constructs a finite tree automaton with the same behaviour as the given
	 * one but with consistently renamed states.<br>
	 * Helper method for substitute.
	 * 
	 * @param <Q>
	 *            type of the states of the given finite tree automaton
	 * @param <Q0>
	 *            type of the states of the renamed finite tree automaton
	 * @param <F>
	 *            type of the symbols of the finite tree automata
	 * @param <R0>
	 *            type of the rules of the renamed finite tree automaton
	 * @param fta
	 *            finite tree automaton which is to be renamed
	 * @param newnames
	 *            assigns each state a new state which it is replaced by
	 * @param fc
	 *            {@link FTACreator} to create the renamed finite tree automaton
	 * @return essentially the same finite tree automaton, but with states which
	 *         are renamed by the given specified map
	 * 
	 * @see #substitute(Tree, Map, Converter, Converter, Converter, FTACreator)
	 */
	private static <Q extends State, Q0 extends State, F extends RankedSymbol, R0 extends FTARule<F, Q0>> FTA<F, Q0, R0> renameAutomatonStates(
			FTA<F, Q, ? extends FTARule<F, Q>> fta, Map<Q, Q0> newnames,
					FTACreator<F, Q0, R0, ? extends FTA<F, Q0, R0>> fc) {
		/*
		 * for each rule in the old automaton, add a structurally equivalent
		 * version with consistently renamed states
		 */
		Set<R0> newRules = new HashSet<R0>();
		for (FTARule<F, Q> r : fta.getRules()) {
			Q0 newDestState = newnames.get(r.getDestState());
			List<Q0> newSrcStates = new LinkedList<Q0>();
			for (Q q : r.getSrcStates())
				newSrcStates.add(newnames.get(q));
			newRules.add(fc.createRule(r.getSymbol(), newSrcStates,
					newDestState));
		}

		/*
		 * adjust final states
		 */
		Set<Q0> newFinals = new HashSet<Q0>();
		for (Q qf : fta.getFinalStates())
			newFinals.add(newnames.get(qf));

		return fc.createFTA(fta.getAlphabet(), newnames.values(), newFinals,
				newRules);
	}

	/**
	 * Given a set of states, a set of rules, a tree in which some constants
	 * (symbols of arity 0) are to be replaced and a map that maps those
	 * constants to states, adds the rules and states necessary to recognize any
	 * tree, where the specified constants of the given tree are replaced by
	 * some trees that are recognized by given rules and states such that each
	 * of these trees is reduced to the state of the corresponding map. <br>
	 * Helper method for
	 * {@link FTAOps#substitute(Tree, Map, Converter, Converter, Converter, FTACreator)}
	 * 
	 * 
	 * @param <F>
	 *            type of the symbols of the rules and tree
	 * @param <Q>
	 *            type of the given states
	 * @param <R>
	 *            type of the given rules
	 * @param tree
	 *            tree with constants that are to be replaced,
	 * @param subst
	 *            map mapping some constants (symbols with arity 0) of the given
	 *            tree to some states that shall replace those constants
	 * @param states
	 *            set of states, where the automaton shall be added
	 * @param rules
	 *            set of rules, where the automaton shall be added
	 * @param fc
	 *            {@link FTACreator} to create rules
	 * @param treeStateConv
	 *            converts a tree into a state - conversion must be injective
	 * 
	 * @return destination state which shall be the final state of the new
	 *         automaton
	 */
	private static <F extends RankedSymbol, Q extends State, R extends FTARule<F, Q>> Q buildAutomatonForOneTree(
			Tree<F> tree, Map<F, Q> subst, Set<Q> states, Set<R> rules,
			FTACreator<F, Q, R, ? extends FTA<F, Q, R>> fc,
					Converter<? super Tree<F>, Q> treeStateConv) {
		// replace the key by a state
		if (subst.containsKey(tree.getSymbol())) {
			Q q = subst.get(tree.getSymbol());
			states.add(q);
			return q;
		} else {
			// get the rules from the subtrees and add the corresponding rule
			LinkedList<Q> srcStates = new LinkedList<Q>();
			Q q = treeStateConv.convert(tree);
			for (Tree<F> sub : tree.getSubTrees()) {
				srcStates.add(FTAOps.<F, Q, R> buildAutomatonForOneTree(sub,
						subst, states, rules, fc, treeStateConv));
			}
			// add corresponding rule
			R rule = fc.createRule(tree.getSymbol(), srcStates, q);
			rules.add(rule);
			return q;
		}
	}

	/**
	 * Computes a finite tree automaton, which accepts exactly the specified
	 * tree.<br>
	 * <br>
	 * <em> Algorithm: </em><br>
	 * Foremost the tree automata which accept the subtrees are constructed.
	 * Then all final states of the subtree-automata are collected and a
	 * corresponding new rule is constructed. The destination state of this rule
	 * will become the final state of the wished finite tree automaton.
	 * 
	 * @param <Q>
	 *            state type of the finite tree automaton to be returned
	 * @param <F>
	 *            type of symbols occurring in the resulting finite tree
	 *            automaton
	 * @param <F0>
	 *            type of symbols occurring in the tree
	 * @param <R>
	 *            rule type of the finite tree automaton to be returned
	 * @param <U>
	 *            type of the finite tree automaton to be returned
	 * @param tree
	 *            tree to be accepted by the returned finite tree automaton
	 * @param fc
	 *            {@link FTACreator} for the finite tree automaton to be
	 *            returned
	 * @param stateBuilder
	 *            can build a state from arbitrary objects - conversion must be
	 *            injective!
	 * @return finite tree automaton which recognizes a tree if and only if it
	 *         is equal to the given one
	 */
	public static <F extends RankedSymbol, Q extends State, F0 extends F, R extends FTARule<F, Q>, U extends FTA<F, Q, R>> U computeSingletonFTA(
			Tree<F0> tree, FTACreator<F, Q, R, U> fc,
			Converter<Object, Q> stateBuilder) {
		Set<F> newAlphabet = new HashSet<F>();
		Set<Q> newStates = new HashSet<Q>();
		Set<Q> newFinals = new HashSet<Q>();
		Set<R> newRules = new HashSet<R>();
		if (tree.getSubTrees().isEmpty()) {
			F0 a = tree.getSymbol();
			Q qa = stateBuilder.convert(a);
			newRules.add(fc.createRule(a, new LinkedList<Q>(), qa));
			newStates.add(qa);
			newFinals.add(qa);
			newAlphabet.add(a);
			return fc.createFTA(newAlphabet, newStates, newFinals, newRules);
		} else {

			List<Q> subFinalStates = new ArrayList<Q>();
			U subFTA;
			for (Tree<F0> s : tree.getSubTrees()) {

				// compute FTA which accepts exactly this sub tree
				subFTA = computeSingletonFTA(s, fc, stateBuilder);

				if (subFTA.getFinalStates().size() != 1) // this condition
					// should never be
					// true
					throw new IllegalArgumentException(
					"singleton fta must have exactly one final state!");

				// the (unique) final state of subFTA represents the language
				// {s}, so we remember it for the final rule
				Q subFinalState = subFTA.getFinalStates().iterator().next();
				subFinalStates.add(subFinalState);
				newRules.addAll(subFTA.getRules());
			}

			// final rule: t.getSymbol()(q_{s1},...,q_{sn}) --> q_f, where
			// q_{si} is the state representing the i-th sub tree and q_f
			// is a fresh final State
			Q qf = stateBuilder.convert(tree);
			newStates.add(qf);
			newFinals.add(qf);
			newAlphabet.add(tree.getSymbol());
			newRules.add(fc.createRule(tree.getSymbol(), subFinalStates, qf));
		}
		return fc.createFTA(newAlphabet, newStates, newFinals, newRules);
	}

	/**
	 * Constructs a finite tree automaton which accepts every tree over a given
	 * alphabet.<br>
	 * <br>
	 * This is implemented by simply taking one state and all possible rules
	 * with the symbols in the alphabet and this state.
	 * 
	 * @param <F>
	 *            type of the ranked symbols in the alphabet
	 * @param <Q>
	 *            type of the states in the finite tree automaton which will be
	 *            constructed
	 * @param <T>
	 *            type of the resulting finite tree automaton
	 * @param alphabet
	 *            alphabet for trees which are to be accepted
	 * @param qdest
	 *            only state of the finite tree automaton which will be
	 *            constructed
	 * @param fc
	 *            {@link FTACreator creator for the finite tree automaton} to
	 *            produce the rules of the new finite tree automaton and the new
	 *            tree automaton
	 * @return a finite tree automaton which accepts every tree over the given
	 *         alphabet
	 */
	public static <F extends RankedSymbol, Q extends State, T extends FTA<F, Q, ? extends FTARule<F, Q>>> T computeAlphabetFTA(
			Collection<F> alphabet, Q qdest,
			FTACreator<F, Q, ? extends FTARule<F, Q>, ? extends T> fc) {
		// create rules and only one every time accepting state
		Set<FTARule<F, Q>> rules = new HashSet<FTARule<F, Q>>();
		for (F f : alphabet) {
			int n = f.getArity();
			List<Q> src = new LinkedList<Q>();
			for (int i = 0; i < n; i++) {
				src.add(qdest);
			}
			rules.add(fc.createRule(f, src, qdest));
		}
		Set<Q> states = new HashSet<Q>();
		states.add(qdest);
		return fc.createFTA(alphabet, states, states, rules);
	}



	/**
	 * Constructs the regular tree language containing all trees of this regular tree language 
	 * which are not higher than specified.<br>
	 * <br>
	 * Algorithm:<br>
	 * Let n be the specified height. <br>
	 * For each state q of the incoming automaton and each 1<=i<=n a state (q,i) is introduced
	 * and for each rule f(q1,...,qn)->q and each 1<=j<k<=n a rule f((q1,j),...,(qn,j))->(q,k)
	 * is constructed. The final states of the new automaton are the states of the form
	 * (q,n), where q is a final state of the incoming automaton. It can easily be shown that any
	 * tree whose height does not exceed n is accepted by the resulting automaton: Just take the
	 * rules having been applied to it and add the heights of the trees to the annotating states
	 * and you get a series of rule applications of the new automaton. Conversely, if such a rule
	 * sequence is given, a corresponding rule sequence of the incoming automaton can be obtained
	 * by omitting the indices.
	 * 
	 * @param <F> symbol type of the finite tree automaton to be restricted
	 * @param <Q> state type of the finite tree automaton to be restricted
	 * @param <Q0> state type of the restricted finite tree automaton
	 * @param <T> type of the restricted finite tree automaton
	 * @param fta finite tree automaton whose language is to be restricted 
	 * @param maxHeight maximum height of the trees contained in the language to be returned
	 * @param fc {@link FTACreator} for the finite tree automaton to be returned
	 * @param stateBuilder can build a state from arbitrary objects - conversion must be injective!
	 * 
	 * @return a finite tree automaton representing the regular tree language containing 
	 * all trees of the given language which are not higher than specified
	 */
	public static <F extends RankedSymbol, Q extends State, Q0 extends State, T extends FTA<F, Q0, ? extends FTARule<F, Q0>>> 
	T restrictToMaxHeight(
			FTA<F,Q,? extends FTARule<F, Q>> fta,
					int maxHeight,
					FTACreator<F,Q0,? extends FTARule<F, Q0>,? extends T> fc,
					Converter<? super Pair<Q,Integer>,Q0> stateBuilder) {

		HashSet<Q0> newFinals = new HashSet<Q0>();
		HashSet<FTARule<F,Q0>> newRules = new HashSet<FTARule<F,Q0>>();

		List<Q0> newSrc = new LinkedList<Q0>();
		for (FTARule<F,Q> r: fta.getRules()) {
			for (int i=0; i<maxHeight; i++) {
				for (Q qsrc: r.getSrcStates())
					newSrc.add(stateBuilder.convert(new Pair<Q,Integer>(qsrc,i)));
				for (int j=i+1; j<=maxHeight; j++) {
					Q0 newDst = stateBuilder.convert(new Pair<Q,Integer>(r.getDestState(),j));
					newRules.add(fc.createRule(r.getSymbol(), newSrc, newDst)); 
					if (fta.getFinalStates().contains(r.getDestState()))
						newFinals.add(newDst);
				}
				newSrc.clear();
			}
		}
		return fc.createFTA(fta.getAlphabet(), Collections.<Q0>emptyList(), newFinals, newRules);
	}




	/**
	 * Constructs a tree which can be annotated by the given finite tree automaton
	 * with the given state and is at least as high as specified, if there is such a tree. 
	 * Otherwise, null is returned.<br>
	 * If the given state is specified as null, then a tree is constructed, which
	 * is accepted by the given finite tree automaton, i.e. which can be annotated
	 * with a final state.<br>
	 * 
	 * <emph>Algorithm:</emph><br>
	 * A map is constructed, which stores for each state a tree,
	 * which can be annotated with that state. This is done by a worklist algorithm: <br>
	 * The worklist is initialized with all rules having leaves as symbols. In each iteration, 
	 * a rule is taken from the worklist. If all its source states are found in the map, and its
	 * destination q state is not or the tree of q is not high enough, q is stored in the map 
	 * or updated, respectively. The associated tree is constructed from the symbol of the rule 
	 * and the trees of the source states. Then, the worklist is extended by all the rules, which 
	 * have q as a source state. The parameter 'depthFirst' specifies whether the worklist is 
	 * organized as a stack (depthFirst==true) or a queue. 
	 * In the first case, the new rules are pushed on the top of the worklist, and thus are 
	 * processed in the very next iterations. In the second case, they are appended and thus 
	 * examined not until the other rules on the worklist have been examined first. 
	 * This has influence on the shape of the resulting tree. 
	 * The operation is aborted, if either the specified state was stored in the map and the
	 * associated tree is high enough or if the specified state is null, a final state was stored 
	 * in the map and its associated tree is high enough. In both cases, the resulting tree is 
	 * the tree which belongs to that (final) state.
	 * @param <F> symbol type of the finite tree automaton to be examined
	 * @param <Q> state type of the finite tree automaton to be examined
	 * @param <T> tree type (implied by symbol type) of the tree to be constructed
	 * @param fta finite tree automaton of the language, for whom a witness shall be constructed
	 * @param tc {@link TreeCreator} to create the witness tree
	 * @param accState state which the returned tree can be annotated with
	 * @param minHeight minimum height of the tree to be returned
	 * @param depthFirst indicates whether the worklist is to be organized as a stack or a queue -
	 * in the first case, the resulting tree has minimal height, if the specified height is 0.
	 * @return if the given state is not null: a tree which can be annotated with that state, or
	 * null if there is no such tree <br> 
	 * If the given state is null: a tree of minimum which is accepted by the given finite tree automaton
	 * and has minimum height, or null if there is no such tree
	 */
	public static <Q extends State, F extends RankedSymbol, T extends Tree<F>> T constructTreeAcceptedInState(
			FTA<F, Q, ? extends FTARule<F, Q>> fta, TreeCreator<F, T> tc, Q accState, final int minHeight, boolean depthFirst) {

		/* map, which associates to each state in its key set tree which
		 * can be annotated by this state */
		Map<Q, T> whytree = new HashMap<Q, T>();

		/*
		 * The worklist contains all rules which could be applied next
		 */
		LinkedList<FTARule<F,Q>> worklist = new LinkedList<FTARule<F,Q>>();

		/* group rules by source state */
		Map<Q, Collection<FTARule<F,Q>>> rulesBySrcState = new HashMap<Q, Collection<FTARule<F,Q>>>();
		for (FTARule<F,Q> rule: fta.getRules()) {

			/*
			 * initialize worklist with all rules having leaves as symbols
			 */
			if (rule.getSymbol().getArity()==0) {
				worklist.add(rule);
			}

			for (Q qsrc: rule.getSrcStates()) {
				Collection<FTARule<F,Q>> qsrcRules;
				if (rulesBySrcState.containsKey(qsrc))
					qsrcRules = rulesBySrcState.get(qsrc);
				else {
					qsrcRules = new LinkedList<FTARule<F,Q>>();
					rulesBySrcState.put(qsrc, qsrcRules);
				}
				qsrcRules.add(rule);
			}
		}

		while (!worklist.isEmpty()) {
			FTARule<F,Q> next = worklist.poll();
			//System.out.println("current rule: "+next);
			Q dest = next.getDestState();
			List<T> subTrees = new LinkedList<T>();
			if (!whytree.containsKey(dest) || (whytree.containsKey(dest) && TreeOps.getHeight(whytree.get(dest))< minHeight)) {
				boolean allMarked = true;
				for (Q q: next.getSrcStates()) {
					if (!whytree.containsKey(q)) {
						allMarked = false;
						break;
					}
					else 
						subTrees.add(whytree.get(q));
				}

				/*
				 * Each source state is contained in the map and thus annotates some tree.
				 * Thus, the destination state of the current rule also annotates a tree
				 * having the rules' symbol as root and the fore-mentioned trees as subtrees.
				 */
				if (allMarked) {
					T newTree = tc.makeTree(next.getSymbol(), subTrees);
					int newHeight = TreeOps.getHeight(newTree);
					whytree.put(dest, newTree);
					/*
					 * if an appropriate state has been reached, 
					 * i.e. accState or a final state if accState==null, 
					 * then the right tree is found and can be returned
					 */
					if (newHeight>=minHeight && (dest.equals(accState) || (accState==null && fta.getFinalStates().contains(dest))))
						return newTree;
					else {
						/*
						 * if the state and tree just reached is not appropriate, try one more
						 * rule application - add all rules which could be reached in
						 * the next step, i.e. all rules which have the current state
						 * as source state 
						 */
						if (rulesBySrcState.containsKey(dest)) {
							for (FTARule<F,Q> considerNext: rulesBySrcState.get(dest))
								if (depthFirst)
									worklist.push(considerNext);
								else {
									worklist.add(considerNext);
									//System.out.println(considerNext+" added.");
								}
						}
					}
				}
			}
		}

		/* the worklist is empty and no appropriate state has been reached - thus,
		 * there is no tree as requested
		 **/
		return null;
	}

	/**
	 * Given a finite tree automaton, constructs a tree accepted by it. <br>
	 * This is done by delegating to {@link #constructTreeAcceptedInState} and specifying
	 * null as the accepting state, 0 as the minimum height and breadth-first search
	 * as search strategy. <br>
	 * Thus, a smallest tree accepted in any final state is constructed.
	 * @param <F> symbol type of the finite tree automaton to be examined
	 * @param <Q> state type of the finite tree automaton to be examined
	 * @param <T> tree type (implied by symbol type) of the tree to be constructed
	 * @param fta finite tree automaton of the language, for which a witness is to be constructed
	 * @param tc {@link TreeCreator} to create the witness tree
	 * @return a tree of minimum height accepted by the specified automaton or null if there is
	 * no accepted tree.
	 * @see #constructTreeAcceptedInState
	 */
	public static <Q extends State, F extends RankedSymbol, T extends Tree<F>> T constructTreeFrom(
			FTA<F, Q, ? extends FTARule<F, Q>> fta, TreeCreator<F, T> tc) {
		return constructTreeAcceptedInState(fta, tc, null, 0, false);
		//return MoreFTAOps.constructTreeFrom3(fta, tc);
	}


	/**
	 * Given a finite tree automaton, constructs a tree accepted by it, which has
	 * at least the specified height. <br>
	 * This is done by delegating to {@link #constructTreeAcceptedInState} and specifying
	 * null as the accepting state, and the given height as the minimum height. 
	 * Thus, the smallest tree exceeding the specified height and being accepted in any final state 
	 * is constructed.
	 * @param <F> symbol type of the finite tree automaton to be examined
	 * @param <Q> state type of the finite tree automaton to be examined
	 * @param <T> tree type (implied by symbol type) of the tree to be constructed
	 * @param fta finite tree automaton of the language, for which a witness is to be constructed
	 * @param tc {@link TreeCreator} to create the witness tree
	 * @param minHeight the height which the resulting tree will have at least
	 * @param depthFirst specifies the order in which the rules of the finite tree automaton
	 * will be iterated.
	 * @return a tree of minimum height accepted by the specified automaton or null if there is
	 * no accepted tree.
	 * @see #constructTreeAcceptedInState
	 */
	public static <Q extends State, F extends RankedSymbol, T extends Tree<F>> T constructTreeWithMinHeightFrom(
			FTA<F, Q, ? extends FTARule<F, Q>> fta, TreeCreator<F, T> tc, int minHeight, boolean depthFirst) {
		return constructTreeAcceptedInState(fta, tc, null, minHeight, depthFirst);
	}


	/**
	 * Converts a finite tree automaton into another one by converting the types
	 * of states and symbols. <br>
	 * This is done by translating the given state converter and symbol
	 * converter into maps and then translating all symbols, states and rules
	 * using these maps.
	 * 
	 * @param <Q1>
	 *            state type of the given finite tree automaton
	 * @param <Q2>
	 *            wished state type
	 * @param <F1>
	 *            symbol type of the given finite tree automaton
	 * @param <F2>
	 *            wished symbol type
	 * @param <R2>
	 *            resulting rule type using the wished state and symbol type
	 * @param <T2>
	 *            resulting finite tree automaton type using the wished state
	 *            and symbol type
	 * 
	 * @param aut
	 *            given automaton that is to be converted
	 * @param sc
	 *            Converter to convert states of the given type Q1 into states
	 *            of wished type Q2
	 * @param ac
	 *            Converter to convert symbols of given type F1 into symbols of
	 *            wished type F2
	 * @param fc
	 *            {@link FTACreator} to create rules and automaton with
	 *            converted states and symbols
	 * 
	 * @return finite tree automaton equivalent to the given one with new state
	 *         and symbol type
	 */
	public static <Q1 extends State, Q2 extends State, F1 extends RankedSymbol, F2 extends RankedSymbol, R2 extends FTARule<F2, Q2>, T2 extends FTA<F2, Q2, R2>> T2 ftaConverter(
			FTA<F1, Q1, ? extends FTARule<F1, Q1>> aut,
					Converter<? super Q1, ? extends Q2> sc, Converter<? super F1, ? extends F2> ac,
					FTACreator<F2, Q2, R2, T2> fc) {

		// initializing
		Collection<F2> newAlphabet;
		Collection<Q2> newStates;
		Set<Q2> newFinals = new HashSet<Q2>();
		Set<R2> newRules = new HashSet<R2>();

		// set the new alphabet using a map representing the alphabet converter
		Map<F1, F2> alphMap = new HashMap<F1, F2>();
		for (F1 f : aut.getAlphabet()) {
			alphMap.put(f, ac.convert(f));
		}
		newAlphabet = alphMap.values();

		// set the new states using a map representing the state converter
		// the new final states are the image of the given ones
		Map<Q1, Q2> statesMap = new HashMap<Q1, Q2>();
		for (Q1 q : aut.getStates()) {
			statesMap.put(q, sc.convert(q));
			if (aut.getFinalStates().contains(q))
				newFinals.add(statesMap.get(q));
		}
		newStates = statesMap.values();

		// set the new rules as the images of the given ones using the maps
		// defined above
		for (FTARule<F1, Q1> r : aut.getRules()) {
			List<Q2> newSrc = new LinkedList<Q2>();
			for (Q1 q : r.getSrcStates()) {
				newSrc.add(statesMap.get(q));
			}
			newRules.add(fc.createRule(alphMap.get(r.getSymbol()), newSrc,
					statesMap.get(r.getDestState())));
		}
		return fc.createFTA(newAlphabet, newStates, newFinals, newRules);
	}

	/**
	 * Annotates a given tree and all its subtrees with states they can be
	 * annotated with by a given finite tree automaton.
	 * 
	 * @param fta
	 *            finite tree automaton which is used to annotate the given tree
	 * @param <F>
	 *            symbol type of the finite tree automaton which is used to
	 *            annotate the given tree
	 * @param <Q>
	 *            state type of the finite tree automaton which is used to
	 *            annotate the given tree
	 * 
	 * @param tree
	 *            tree to be annotated
	 * @return a map which assigns each tree contained in t the set of states
	 *         which the automaton can annotate this tree with
	 */
	public static <F extends RankedSymbol, Q extends State> Map<Tree<F>, Set<Q>> annotateTreeWithStates(
			FTA<F, Q, ? extends FTARule<F, Q>> fta, Tree<F> tree) {
		Map<Tree<F>, Set<Q>> ret = new HashMap<Tree<F>, Set<Q>>();
		Stack<Tree<F>> toDo = new Stack<Tree<F>>();
		toDo.add(tree);
		while (!toDo.isEmpty()) {
			Tree<F> s = toDo.pop();
			if (!ret.containsKey(s))
				ret.put(s, FTAProperties.accessibleStates(fta, s));
			for (Tree<F> u : s.getSubTrees())
				toDo.push(u);
		}
		return ret;
	}
	
	/**
	 * Annotates a given tree and all its subtrees with all rules of a given finite tree automaton which
	 * can be applied on them. 
	 * @param fta
	 *            finite tree automaton which is used to annotate the given tree
	 * @param <F>
	 *            symbol type of the finite tree automaton which is used to
	 *            annotate the given tree
	 * @param <Q>
	 *            state type of the finite tree automaton which is used to
	 *            annotate the given tree
	 * 
	 * @param tree
	 *            tree to be annotated
	 * @return a map which assigns each tree contained in t the set of rules
	 *         which the automaton can apply to this tree 
	 **/
	public static <F extends RankedSymbol, Q extends State> Map<Tree<F>, Set<FTARule<F,Q>>> annotateTreeWithRules(
			FTA<F, Q, ? extends FTARule<F, Q>> fta, Tree<F> tree) {
		Map<Tree<F>, Set<FTARule<F,Q>>> ret = new HashMap<Tree<F>, Set<FTARule<F,Q>>>();
		Stack<Tree<F>> toDo = new Stack<Tree<F>>();
		toDo.add(tree);
		while (!toDo.isEmpty()) {
			Tree<F> s = toDo.pop();
			if (!ret.containsKey(s)) {
				ret.put(s, FTAProperties.applicableRules(fta, s));
			}
			for (Tree<F> u : s.getSubTrees())
				toDo.push(u);
		}
		return ret;
	}
	

	/**
	 * Converts the rules of the given finite tree automaton to a string
	 * representation. The final state mark ! is appended to final states in the
	 * rules. The result can be parsed back in with the FTAParser if all
	 * distinct states and symbols used in the automaton have different string
	 * representations.
	 * 
	 * @param fta
	 *            finite tree automaton to be converted to a string
	 * @param <F>
	 *            symbol type of the finite tree automaton to be converted
	 * @param <Q>
	 *            state type of the finite tree automaton to be converted
	 * 
	 * @return a string for all rules which the FTAParser can parse back
	 */
	public static <Q extends State, F extends RankedSymbol> String rulesToString(
			FTA<F, Q, ? extends FTARule<F, Q>> fta) {
		StringBuilder sb = new StringBuilder();
		for (FTARule<F, Q> rule : fta.getRules()) {
			sb.append(rule.getSymbol().toString());
			if (rule.getSrcStates().size() != 0) {
				sb.append('(');
				boolean first = true;
				for (State state : rule.getSrcStates()) {
					if (!first)
						sb.append(',');
					else
						first = false;
					sb.append(state.toString());
					if (fta.getFinalStates().contains(state))
						sb.append("!");
				}
				sb.append(")");
			}
			sb.append(" -> ");
			sb.append(rule.getDestState().toString());
			if (fta.getFinalStates().contains(rule.getDestState()))
				sb.append("!");
			sb.append('\n');
		}
		return sb.toString();
	}

}
