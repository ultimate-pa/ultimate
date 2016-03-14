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
package de.uni_muenster.cs.sev.lethal.treeautomata.common;

import de.uni_muenster.cs.sev.lethal.grammars.RTGRule;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTAEpsRule;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTARule;
import de.uni_muenster.cs.sev.lethal.utils.Converter;
import de.uni_muenster.cs.sev.lethal.utils.Pair;


/**
 * Encapsulates the creation of finite tree automata of a certain type 
 * and compatible rules.<br>
 * An FTACreator is used in various algorithms which construct new finite tree automata. By
 * supplying such an algorithm with an appropriate FTACreator, the type
 * of the resulting finite tree automaton can be controlled. 
 * Additionally, it is used to apply some transformations,
 * such as the elimination of epsilon rules.
 * 
 * @param <Q> state type of automata to be created
 * @param <F> symbol type of automata to be created
 * @param <R> rule type of automata to be created
 * @param <T> type of automata to be created
 * 
 * @author Dorothea, Irene, Martin
 */
public abstract class FTACreator<F extends RankedSymbol, Q extends State, R extends FTARule<F,Q>,T extends FTA<F,Q,R>> {


	/**
	 * Creates a new finite tree automaton out of a collection of rules and a collection of final states.
	 * This is enough to define a finite tree automaton. The created finite tree automaton satisfies the
	 * invariants specified in {@link FTA}.
	 * 
	 * @param newRules rules of the new automaton
	 * @param newFinals final states of the new automaton
	 * @return new finite tree automaton with rules and final states as specified - the remaining states
	 * and the symbols are computed out of the supplied rules and final states
	 */
	public abstract T createFTA(Collection<? extends FTARule<F,Q>> newRules, Collection<Q> newFinals);

	/**
	 * Creates a new finite tree automaton out of given alphabet, states, final states and rules.
	 * In particular, the created finite tree automaton complies with the invariants
	 * specified in {@link FTA}.
	 * 
	 * @param alphabet alphabet of the new automaton
	 * @param states states of the new automaton
	 * @param finalStates final states of the new automaton
	 * @param rules rules of the new automaton
	 * 
	 * @return new finite tree automaton with states, final states, alphabet 
	 * and rules as specified
	 * 
	 * @see FTA
	 */
	public abstract T createFTA(Collection<F> alphabet, Collection<Q> states, Collection<Q> finalStates, Collection<? extends FTARule<F,Q>> rules);

	/**
	 * Given the data of a finite tree automaton with epsilon rules, constructs an equivalent finite tree automaton
	 * without epsilon rules.
	 * 
	 * @param alphabet alphabet of the finite tree automaton with epsilon rules to be converted
	 * @param states states of the finite tree automaton with epsilon rules to be converted
	 * @param finalStates final states of the finite tree automaton with epsilon rules to be converted
	 * @param rules rules of the finite tree automaton with epsilon rules to be converted
	 * @param epsRules epsilon rules of the finite tree automaton with epsilon rules to be converted
	 * 
	 * @return new automaton without epsilon rules generating the same language
	 */
	public T createFTA(Collection<F> alphabet, Collection<Q> states, Collection<Q> finalStates, Collection<? extends FTARule<F,Q>> rules, Collection<? extends FTAEpsRule<Q>> epsRules){
		return createFTA(alphabet, states, finalStates, eliminateEpsilonRules(rules, epsRules));
	}
	
	
	/**
	 * Given rules and additional epsilon rules, eliminates the epsilon rules.<br>
	 * First, the epsilon cover of each state is calculated, that is the set of all states
	 * which can be reached by only applying epsilon rules. Then, for each rule f(q1,...qn)->q
	 * and each state r in the epsilon cover of q, a rule f(q1,...,qn)->r is added.
	 * 
	 * @param <F> symbol type used in rules
	 * @param <Q> state type used in rules and epsilon rules
	 * @param rules normal rules of the represented finite tree automaton
	 * @param epsRules epsilon rules of the represented finite tree automaton which are to be eliminated
	 * 
	 * @return a pair consisting of normal rules and final states, which represents a finite tree
	 * automaton where the supplied epsilon rules have been eliminated.
	 */
	public static 
	<F extends RankedSymbol,
	Q extends State> 
	Collection<FTARule<F,Q>> eliminateEpsilonRules(Collection<? extends FTARule<F,Q>> rules, 
			Collection<? extends FTAEpsRule<Q>> epsRules) {
		Collection<FTARule<F,Q>> newRules = new LinkedList<FTARule<F,Q>>(rules);
	
		/* map each state q to the states which can be reached from q by applying only epsilon rules */
		Map<Q,Collection<Q>> epsCover = new HashMap<Q,Collection<Q>>();
		
		/* map each state q to the states p, such that p -> q is an epsilon rule */
		Map<Q,Collection<Q>> srcStates = new HashMap<Q,Collection<Q>>();
		
		/* map each state q to the states r, such that q -> r is an epsilon rule */
		Map<Q,Collection<Q>> destStates = new HashMap<Q,Collection<Q>>();
		
		/* list of states which still have to be examined*/
		LinkedList<Q> worklist = new LinkedList<Q>();
		
		/* initialize epsCover, destStates and srcStates:
		 * for each epsilon rule (q,r) make sure that:
		 * - r \in destStates(q)
		 * - q \in srcStates(r)
		 * - q \in epsCover(q) (Note, that this is sufficient, since
		 * - the epsCover of a state s is trivial, if s is not the source state of
		 * an epsilon rule)
		 * - r is on the work list
		 */
		for (FTAEpsRule<Q> e: epsRules) {
			Q qsrc = e.getSrcState();
			Q qdest = e.getDestState();
			worklist.add(e.getSrcState());
			Collection<Q> qEpsCover;
			Collection<Q> qdestSrcStates;
			Collection<Q> qsrcDestStates;

			if (epsCover.containsKey(qsrc))
				qEpsCover = epsCover.get(qsrc);
			else {
				qEpsCover = new HashSet<Q>();
				//qEpsCover.add(qsrc);
				epsCover.put(qsrc, qEpsCover);
			}

			/* add qsrc to destStates(qdest) */
			if (srcStates.containsKey(qdest))
				qdestSrcStates = srcStates.get(qdest);
			else {
				/* a list is sufficient since the epsilon rules are represented
				 * as a set, so a rule q->r is contained at most once, so
				 * qdestSrcStates won't contain duplicates as well */
				qdestSrcStates = new LinkedList<Q>(); 
				srcStates.put(qdest, qdestSrcStates);
			}
			qdestSrcStates.add(qsrc);
			
			
			/* add qdest to srcStates(qsrc) */
			if (destStates.containsKey(qsrc))
				qsrcDestStates = destStates.get(qsrc);
			else {
				/*
				 * list is sufficient - see above, why
				 */
				qsrcDestStates = new LinkedList<Q>();
				destStates.put(qsrc, qsrcDestStates);
			}
			qsrcDestStates.add(qdest);
		}
		
		/* compute the eps-cover of the left sides of the eps rules */
		while (!worklist.isEmpty()) {
			Q q = worklist.poll();
			Collection<Q> qEpsCover = epsCover.get(q);
			boolean changed = false;
			
			/*
			 * update the eps-cover of q by adding all eps-covers of
			 * adjacent states, i.e. all elements of destStates(q)
			 */
			for (Q r: destStates.get(q)) {
				changed = changed || qEpsCover.add(r);
				if (epsCover.containsKey(r)) {
					changed = changed || qEpsCover.addAll(epsCover.get(r));
				}
			}
			
			/* if the epsilon cover of q has changed, this information needs to be
			 * propagated to the predecessors of q, i.e. srcStates(q), if there are any */
			if (changed) {
				/* the eps-Cover of q has changed, so all states p
				 * for which there is an epsilon rule p->q have to
				 * be considered again
				 */
				if (srcStates.containsKey(q))
					worklist.addAll(srcStates.get(q));
			}
		}
		
		/*
		 * group the rules by destination states, so that rules
		 * can easily be found later
		 */
		Map<Q,Collection<FTARule<F,Q>>> rulesByDestStates = new HashMap<Q,Collection<FTARule<F,Q>>>();
		for (FTARule<F,Q> r: rules) {
			Q qdest = r.getDestState();
			Collection<FTARule<F,Q>> qdestRules;
			if (rulesByDestStates.containsKey(qdest))
				qdestRules = rulesByDestStates.get(qdest);
			else {
				/* each rule occurs at most once, so a list is sufficient */
				qdestRules = new LinkedList<FTARule<F,Q>>(); 
				rulesByDestStates.put(qdest, qdestRules);
			}
			qdestRules.add(r);
		}
		
		for (Q q: epsCover.keySet()) {
			for (Q r: epsCover.get(q)) {
				if (rulesByDestStates.containsKey(q))
					for (FTARule<F,Q> qRule: rulesByDestStates.get(q)) {
						/*
						 * for each rule of the form f(q1,...,qn) -> q and
						 * each state r contained in the eps-cover of q,
						 * add a rule f(q1,...,qn) -> r
						 **/
						newRules.add(new GenFTARule<F,Q>(qRule.getSymbol(), qRule.getSrcStates(), r));
					}
			}
		}
		return newRules;
	}
	
	
	/**
	 * Given a regular tree grammar, constructs an equivalent finite tree
	 * automaton (i.e. the resulting finite tree automaton recognizes a tree if
	 * and only if it is generated by the given tree grammar).
	 * 
	 * @param <F> type of symbols occurring in the given {@link RTGRule regular tree grammar rules}
	 * @param <Q> type of states occurring in the given {@link RTGRule regular tree grammar rules}
	 * @param <Q0> type of resulting finite tree automaton
	 * @param grammarStart start symbols of the given regular tree grammar
	 * @param grammarRules rules of the given regular tree grammar
	 * @param stateBuilder converts trees into states - conversion must be injective!
	 * 
	 * @return finite tree automaton which is equivalent to the given regular tree
	 * grammar (that means the resulting finite tree automaton 
	 * recognizes a tree if and only if it is generated by the given tree grammar)
	 */
	public static <F extends RankedSymbol, 
	Q extends State,
	Q0 extends State>
	Pair<Collection<FTARule<F,Q0>>, Collection<Q0>> makeFTAFromGrammar(Collection<Q> grammarStart, Collection<? extends RTGRule<F,Q>> grammarRules, Converter<Object,Q0> stateBuilder) {
		Collection<Q0> newFinals = new LinkedList<Q0>();
		for (Q s: grammarStart)
			newFinals.add(stateBuilder.convert(s));
		Collection<FTARule<F,Q0>> newRules = new LinkedList<FTARule<F,Q0>>();
		Collection<FTAEpsRule<Q0>> newEpsRules = new LinkedList<FTAEpsRule<Q0>>();
		
		
		for (RTGRule<F,Q> rule: grammarRules) {
			Pair<Collection<FTARule<F,Q0>>,Q0> fta = computeConfigSingletonFTA(rule.getRightSide(), stateBuilder);
			newRules.addAll(fta.getFirst());
			newEpsRules.add(new GenFTAEpsRule<Q0>(fta.getSecond(), stateBuilder.convert(rule.getLeftSide())));
		}
		return new Pair<Collection<FTARule<F,Q0>>, Collection<Q0>>(eliminateEpsilonRules(newRules, newEpsRules), newFinals);
	}
	
	/**
	 * Given a configuration tree t (that is a tree consisting of ranked symbols and states),
	 * constructs a finite tree automaton which recognizes at most one tree. If t contains no
	 * states, exactly t is recognized by the constructed finite tree automaton. Otherwise,
	 * no tree is recognized by the constructed finite tree automaton alone, but by all 
	 * finite tree automata which resolve the occurring states correctly, that means that they 
	 * provide rules which transform full trees into these states.
	 * 
	 * @param <Q> type of states occurring in the given configuration tree
	 * @param <Q0> state type of resulting finite tree automaton
	 * @param <F> type of ranked symbols occurring in the given configuration tree
	 * @param t given configuration tree
	 * @param stateBuilder converts arbitrary objects into states - conversion must be injective!
	 * 
	 * @return finite tree automaton which recognizes at most one tree. If the given tree t contains no
	 * states, exactly t is recognized by the constructed finite tree automaton. Otherwise,
	 * no tree is recognized by the constructed finite tree automaton alone, but by all 
	 * finite tree automata which resolve the occurring states correctly, that means that they 
	 * provide rules which transform full trees into these states.
	 */
	private static <F extends RankedSymbol, 
	Q extends State,
	Q0 extends State>
	Pair<Collection<FTARule<F,Q0>>, Q0> computeConfigSingletonFTA(Tree<BiSymbol<F,Q>> t, 
			Converter<Object,Q0> stateBuilder) {
		Q0 qf;
		Collection<FTARule<F,Q0>> newRules = new LinkedList<FTARule<F,Q0>>();
		if (t.getSymbol().isLeafType()) {
			qf = stateBuilder.convert(t.getSymbol().asLeafSymbol());
			return new Pair<Collection<FTARule<F,Q0>>, Q0>(newRules, qf);
		}
		else {
			List<Q0> subFinalStates = new LinkedList<Q0>();
			Pair<Collection<FTARule<F,Q0>>, Q0> subFTA;
			for (Tree<BiSymbol<F,Q>> subTree: t.getSubTrees()) {
				subFTA = computeConfigSingletonFTA(subTree,stateBuilder);
				// the (unique) final state of subFTA represents the language {s}, so we remember it for the final rule
				Q0 subFinalState = subFTA.getSecond();
				subFinalStates.add(subFinalState);
				newRules.addAll(subFTA.getFirst());
			}
			// final rule: t.getSymbol()(q_{s1},...,q_{sn}) --> q_f, where q_{si} is the state representing the i-th sub tree and q_f
			// is a fresh final State
			qf = stateBuilder.convert(t);
			newRules.add(new GenFTARule<F,Q0>(t.getSymbol().asInnerSymbol(), subFinalStates, qf));
		}
		return new Pair<Collection<FTARule<F,Q0>>,Q0>(newRules,qf);
	}
	

	/**
	 * Creates a new rule out of given symbol, source states and destination states.
	 * 
	 * @see FTARule
	 * 
	 * @param f source symbol
	 * @param src source states
	 * @param dest destination states
	 * 
	 * @return rule object with characteristic data as specified
	 */
	public abstract R createRule(F f, List<Q> src, Q dest);
}
