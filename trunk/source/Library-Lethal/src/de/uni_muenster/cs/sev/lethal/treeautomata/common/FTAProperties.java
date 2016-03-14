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


import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTACreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTARule;
import de.uni_muenster.cs.sev.lethal.utils.Converter;
import de.uni_muenster.cs.sev.lethal.utils.Pair;

/**
 * A class for checking properties of a finite tree automaton, for example if it is 
 * deterministic, complete and checking properties of the regular tree languages,
 * which the automata represent.<br>
 * The methods return mostly boolean types, so this class can be used in all 
 * variants of the implementation, with or without generic type parameters.
 * 
 * @author Dorothea, Irene, Martin
 */
public class FTAProperties {


	/**
	 * Converts some object into a state in an efficient way.<br>
	 * The converting is saved in a map.
	 * 
	 * @param <T> type of objects which are to be converted into a state
	 */
	protected static class StateConverter<T> implements Converter<T,State> {

		/** Map which saves what is converted into which state. */
		private HashMap<T,State> cache = new HashMap<T,State>();

		/**
		 * @see de.uni_muenster.cs.sev.lethal.utils.Converter#convert
		 */
		@Override
		public State convert(T a) {
			if (cache.containsKey(a))
				return cache.get(a);
			else {
				State newState = new State(){};
				cache.put(a,newState);
				return newState;
			}
		}

	}



	/**
	 * Checks whether the given finite tree automaton is deterministic. <br>
	 * I.e. every left side of a rule occurs at most once.
	 * 
	 * @param <Q> type of states of the given finite tree automaton
	 * @param <F> type of symbols of the given finite tree automaton
	 * @param <R> type of rules of the given finite tree automaton
	 * @param fta finite tree automaton which shall be checked
	 * @return whether the given finite tree automaton is deterministic
	 */
	public static <F extends RankedSymbol, Q extends State, R extends FTARule<F,Q>> 
	boolean checkDeterministic(FTA<F,Q,R> fta){

		Set<List<Q>> fDefined = new HashSet<List<Q>>();

		for (F f: fta.getAlphabet()) {
			for (R rule: fta.getSymbolRules(f)) {
				if (fDefined.contains(rule.getSrcStates()))
					return false;
				else
					fDefined.add(rule.getSrcStates());
			}
			fDefined.clear();
		}

		return true;
	}

	/**
	 * Checks whether the given finite tree automaton is complete. <br>
	 * I.e. every possible left side of a rule occurs, so for each symbol
	 * of the alphabet and each combination of source states there is a rule.
	 * 
	 * @param <Q> type of states of the given finite tree automaton
	 * @param <F> type of symbols of the given finite tree automaton
	 * @param <R> type of rules of the given finite tree automaton
	 * @param fta finite tree automaton which shall be checked.
	 * @return whether the given finite tree automaton is complete
	 */
	public static <F extends RankedSymbol, Q extends State, R extends FTARule<F,Q>>
	boolean checkComplete(FTA<F,Q,R> fta) {
		// Number of states
		int countStates = fta.getStates().size();
		// consider all symbols and tupels of states
		for (F symbol : fta.getAlphabet()){
			Set<List<Q>> countDifSrc = new HashSet<List<Q>>();
			for(R rule : fta.getSymbolRules(symbol)){
				// if rule is a matching rule, set contained to true
				countDifSrc.add(rule.getSrcStates());
			}
			if (countDifSrc.size() != Math.pow(countStates,symbol.getArity())){
				return false;
			}
			// all tupels that must be part of a rule together with this symbol
			/*boolean contained = false;
			for(List<Q> states : Combinator.combine(fta.getStates(), symbol.getArity())){
				// search that rule

				}
				// if there was no matching rule, the fta is not complete
				if(!contained){
					return false;
				}
			}*/
		}    
		return true;
	}


	/**
	 * Checks whether two given finite tree automata recognise the same language.<br>
	 * That means one tree is accepted by the first tree automaton if and only if it
	 * is accepted by the second tree automaton.<br>
	 * <br>
	 * Algorithm:<br>
	 * This is realized by testing whether the language of the first automaton is a subset
	 * of the language of the second automaton and the other way round.
	 * 
	 * @param <F> type of the symbols
	 * @param <Q1> type of the states of the first finite tree automaton
	 * @param <Q2> type of the states of the second finite tree automaton
	 * of the second finite tree automaton and the complemented first finite tree automaton 
	 * @param fta1 first finite tree automaton which represents the first regular language 
	 * @param fta2 second finite tree automaton which represents the second regular language 
	 * 
	 * @return true if and only if the two tree automata recognise the same language
	 */
	public static <F extends RankedSymbol,
	Q1 extends State,
	Q2 extends State> 
	boolean sameLanguage(FTA<F,Q1,? extends FTARule<F,Q1>> fta1, 
			FTA<F,Q2,? extends FTARule<F,Q2>> fta2){
		return subsetLanguage(fta1,fta2) && subsetLanguage(fta2,fta1);
	}



	/**
	 * Checks if the language recognised by the given finite tree automaton is empty. <br>
	 * That means that no tree is accepted by the tree automaton.<br>
	 * <br>
	 * Algorithm:<br>
	 * This is simply checked by reducing the finite tree automaton.
	 * If there are no final states in the reduced automaton, than the language is empty.
	 * 
	 * @param <Q> state type of the given finite tree automaton
	 * @param <F> symbol type of the given finite tree automaton
	 * @param fta finite tree automaton which gives the language
	 * @return true if and only if the finite tree automaton does not accept any tree
	 */
	public static <F extends RankedSymbol, Q extends State>  
	boolean emptyLanguage(FTA<F,Q,? extends FTARule<F,Q>> fta){
		FTACreator<F,Q,GenFTARule<F,Q>,GenFTA<F,Q>> fc 
		= new GenFTACreator<F,Q>();
		return FTAOps.reduceBottomUp(fta,fc).getFinalStates().isEmpty();
	}


	/**
	 * Given a finite tree automaton, decides whether the language recognized by the automaton is finite.<br>
	 * <br>
	 * Algorithm:<br>
	 * First, the finite tree automaton is {@link FTAOps#reduceFull fully reduced}. Afterwards, a mapping is constructed using
	 * constructed, which assigns each state q the set of states r, from which q can be reached, that
	 * means that there is a configuration tree which contains q as leaf and can be annotated with q.<br>
	 * Finally, it is checked, whether there is a state which can be reached from itself. If such a state
	 * is found, the given finite tree automaton recognizes infinitely many trees since 
	 * <ul>
	 * <li> a configuration tree t1, which can be annotated with a final state and which has q as leaf </li>
	 * <li> a configuration tree t2, which can be annotated with q and which as q as leaf </li>
	 * </ul>
	 * can be found.
	 * Thus, by first substituting t2 for q in t1, and then repeatedly substituting t2 for q,
	 * infinitely many configuration trees can be constructed which can be annotated with
	 * a final state. 
	 * In all these configuration trees, all states can be replaced by full trees which can
	 * be reduced to them, since the finite tree automaton is also bottom-up reduced. 
	 * In consequence, the given finite tree automaton recognizes infinitely many trees.<br>
	 * <br>
	 * Conversely, if no such cycle can be found, the language is finite.
	 * <br>
	 * 
	 * @param <Q> state type of the finite tree automaton to be examined
	 * @param <F> symbol type of the finite tree automaton to be examined
	 * @param fta finite tree automaton to be examined
	 * 
	 * @return true, if the finite tree automaton recognizes finitely many trees, false otherwise
	 */
	public static <F extends RankedSymbol, Q extends State>  
	boolean finiteLanguage(FTA<F,Q,? extends FTARule<F,Q>> fta){

		//make FTACreator
		//FTACreator<Q,F,FTARule<Q,F>,T> fc
		FTACreator<F,Q,GenFTARule<F,Q>,GenFTA<F,Q>> fc 
		= new GenFTACreator<F,Q>();

		FTA<F,Q,? extends FTARule<F,Q>> redFTA = FTAOps.reduceFull(fta,fc);

		/* 
		 * For every state q, we store all states r, from which q can be reached.
		 * We say that q can be reached from a state r, if there is a configuration
		 * tree which contains q as leaf and can be annotated with r.
		 */
		Map<Q,Set<Q>> reachableStates = new HashMap<Q,Set<Q>>();
		Set<Q> workSet = new HashSet<Q>();
		Map<Q,Set<FTARule<F,Q>>> rulesByDestState = new HashMap<Q,Set<FTARule<F,Q>>>();
		for (Q q: redFTA.getStates())
			reachableStates.put(q, new HashSet<Q>());
		
		/*
		 * group rules of the reduced automaton by destination state
		 */
		for (FTARule<F,Q> rule: redFTA.getRules()) {
			Set<FTARule<F,Q>> destRules;
			if (!rulesByDestState.containsKey(rule.getDestState())) {
				destRules = new HashSet<FTARule<F,Q>>();
				rulesByDestState.put(rule.getDestState(), destRules);
			}
			else
				destRules = rulesByDestState.get(rule.getDestState());
			destRules.add(rule);
			workSet.add(rule.getDestState());
		}


		/*
		 * idea:
		 * examine rule f(q1,...qn) -> q
		 * qi can be reached directly from q and indirectly from every state r, 
		 * from which q can be reached. So, it must be assured, that 
		 * q and reachableStates.get(q) are contained in reachableStates(qi).
		 * This leads to a system of monotonic constraints, which is solvable by
		 * a worklist iteration
		 */
		while (!workSet.isEmpty()) {
			Q next = workSet.iterator().next();
			workSet.remove(next);

			/* reachNext contains all states from which next can be reached */
			Set<Q> reachNext = reachableStates.get(next);
			for (FTARule<F,Q> ruleOfNext: rulesByDestState.get(next)) {
				for (Q src: ruleOfNext.getSrcStates()) {
					boolean somethingChanged = false;
					
					/* reachSrc contains all states from which src can be reached */
					Set<Q> reachSrc = reachableStates.get(src);
					
					/* src can be reached from next */
					somethingChanged = somethingChanged || reachSrc.add(next);
					
					/* src can also be reached from every state r, from which next
					 * can be reached - just take a configuration tree, which contains
					 * next as leaf and which can be annotated with r and replace next
					 * by the current rule. This leads to a configuration tree containing
					 * src as leaf, which still can be annotated with r. Thus, src can
					 * be reached from each state r, from which next can be reached */
					somethingChanged = somethingChanged || reachSrc.addAll(reachNext);
					
					if (somethingChanged)
						
						/* 
						 * the set of states, from which src can be reached, has been enriched
						 * by at least one state s. Let q be a state, which can be reached
						 * from src in one step. Then q can also be reached from s. 
						 * So, we have to make sure, that the sets associated with each of those 
						 * states q are also enriched by s and thus add src to the worklist because
						 * then we will eventually visit these states.
						 */
						workSet.add(src);
				}
			}
		}

		for (Q q: reachableStates.keySet())
			if (reachableStates.get(q).contains(q))
				/* Since q is reachable from q, we can find a configuration
				 * tree tqc which can be reduced to q, such that q is a leaf of tqc.
				 * Sinced the automaton is top-down reduced, we can find a final state 
				 * qf and a configuration tree tc such that q is a leaf of tc. 
				 * Thus, by substituting tqc for q, we can construct infinitely many configuration
				 * trees which are, since the automaton is also bottom-up reduced,
				 * all reducible to full trees. Thus, the automaton recognizes infinitely many trees.*/
				return false;

		/* if this point is reached, no cycle could be found, so the language is finite. */
		return true;


	}

	/**
	 * Checks whether a regular tree language (given by a finite tree automaton) is
	 * a subset of another regular tree language (given by a second finite tree automaton).<br>
	 * A first language is subset of a second language, if all trees of the first language
	 * are also contained in the second language.<br>
	 * <br>
	 * Algorithm:<br>
	 * For this it is checked whether the difference from the first automaton and 
	 * the second automaton is empty. It is a simple mathematical observation, that in this case
	 * the first language is contained in the second one.
	 * 
	 * @param <F> type of the symbols
	 * @param <Q1> type of the states of the first finite tree automaton
	 * @param <Q2> type of the states of the second finite tree automaton
	 * @param fta1 first finite tree automaton 
	 * @param fta2 second finite tree automaton
	 * 
	 * @return whether the language produced by fta1 is contained in the language produced by fta2
	 */
	public static <F extends RankedSymbol,
	Q1 extends State,
	Q2 extends State> 
	boolean subsetLanguage(FTA<F,Q1,? extends FTARule<F,Q1>> fta1, 
			FTA<F,Q2,? extends FTARule<F,Q2>> fta2) {
		// make converters
		Converter<Set<Q2>,State> sc2 = new StateConverter<Set<Q2>>();
		Converter<Pair<Q1,State>,State> pc3 = new StateConverter<Pair<Q1,State>>();
		// make standard creator
		FTACreator<F,State,GenFTARule<F,State>,GenFTA<F,State>> fc 
		= new GenFTACreator<F,State>();

		return FTAOps.difference(fta1,fta2,sc2,fc,pc3,fc).getFinalStates().isEmpty();
	}

	/**
	 * Decides whether a given finite tree automaton can reduce a given tree to a final state. <br>
	 * <br>
	 * Algorithm: <br>
	 * First all states which can be reached by the automaton can annotate the root symbol
	 * of the tree with are computed and it is checked whether they contain a final state. 
	 * To find the states the helper function {@link #accessibleStates} is used.
	 * 
	 * @param <Q> state type of finite tree automaton
	 * @param <F> symbol type of finite tree automaton
	 * @param fta finite tree automaton for which the tree problem is to be decided
	 * @param tree tree for which the tree problem shall be decided
	 * @return true if the given finite tree automaton can reduce the given tree to a final state, 
	 * i.e. if the automaton accepts the tree, false otherwise
	 * 
	 * @see FTAProperties#accessibleStates(FTA, Tree) 
	 * 
	 */
	public static <F extends RankedSymbol, Q extends State> 
	boolean decide(FTA<F,Q,? extends FTARule<F,Q>> fta, Tree<? extends F> tree) {
		Set<Q> accStates = FTAProperties.accessibleStates(fta,tree);
		for (Q q: accStates)
			if (fta.getFinalStates().contains(q))
				return true;
		return false;
	}

	/**
	 * Computes the set of states which a finite tree automaton A can reduce a given tree 
	 * consisting of ranked symbols to.<br>
	 * Helper function for {@link FTAProperties#decide}.<br>
	 * <br>
	 * Algorithm:<br>
	 * The function works recursively on the tree. First the method calculates the accessible states
	 * of the subtrees, then calculates the corresponding accessible states which are accessible
	 * with the rules fitting to the root symbol of the tree.
	 * 
	 * @param <Q> state type of the given finite tree automaton
	 * @param <F> symbol type of the given finite tree automaton
	 * @param fta finite tree automaton to be applied to tree
	 * @param tree tree to be analysed
	 * @return the set of states which the given finite tree automaton can reduce the given tree to
	 * @see FTAProperties#decide(FTA, Tree)
	 */
	public static <F extends RankedSymbol, Q extends State> 
	Set<Q> accessibleStates(FTA<F,Q,? extends FTARule<F,Q>> fta, Tree<? extends F> tree) {
		Set<Q> ret = new HashSet<Q>();
		List<Set<Q>> subStateSets = new LinkedList<Set<Q>>();
		for (Tree<? extends F> s: tree.getSubTrees())
			subStateSets.add(accessibleStates(fta,s));

		for (FTARule<F,Q> r: fta.getSymbolRules(tree.getSymbol())) {
			Iterator<Set<Q>> accSet = subStateSets.listIterator();
			Iterator<Q> srcState = r.getSrcStates().listIterator();
			boolean ruleApplicable=true;
			while (accSet.hasNext()) {
				if (!accSet.next().contains(srcState.next())) {
					ruleApplicable=false;
					break;
				}
			}
			if (ruleApplicable)
				ret.add(r.getDestState());
		}
		return ret;
	}
	
	/**
	 * Computes the set of rules which a finite tree automaton A can apply to a given tree 
	 * consisting of ranked symbols<br>
	 * <br>
	 * Algorithm:<br>
	 * The function works recursively on the tree. First the method calculates the accessible states
	 * of the subtrees, then calculates the corresponding rules fitting to the root symbol of the tree.
	 * 
	 * @param <Q> state type of the given finite tree automaton
	 * @param <F> symbol type of the given finite tree automaton
	 * @param fta finite tree automaton to be applied to tree
	 * @param tree tree to be analysed
	 * @return the set of rules which the given finite tree automaton can apply to the given tree
	 */
	public static <F extends RankedSymbol, Q extends State> 
	Set<FTARule<F,Q>> applicableRules(FTA<F,Q,? extends FTARule<F,Q>> fta, Tree<? extends F> tree) {
		Set<FTARule<F,Q>> ret = new HashSet<FTARule<F,Q>>();
		List<Set<Q>> subStateSets = new LinkedList<Set<Q>>();
		for (Tree<? extends F> s: tree.getSubTrees())
			subStateSets.add(accessibleStates(fta,s));

		for (FTARule<F,Q> r: fta.getSymbolRules(tree.getSymbol())) {
			Iterator<Set<Q>> accSet = subStateSets.listIterator();
			Iterator<Q> srcState = r.getSrcStates().listIterator();
			boolean ruleApplicable=true;
			while (accSet.hasNext()) {
				if (!accSet.next().contains(srcState.next())) {
					ruleApplicable=false;
					break;
				}
			}
			if (ruleApplicable)
				ret.add(r);
		}
		return ret;
	}

	/**
	 * Computes the set of states which a finite tree automaton A can reduce a given 
	 * tree consisting of states and ranked symbols to.<br>
	 * <br>
	 * Algorithm:<br>
	 * The function works recursively on the tree. 
	 * If the root symbol is a state, the reachable states contains only this state.
	 * If the root symbol is a ranked symbol, the method first calculates the accessible states
	 * of the subtrees, then calculates the corresponding accessible states which are accessible
	 * with the rules fitting to the root symbol of the tree. 
	 * 
	 * @param <Q> state type of the given finite tree automaton
	 * @param <F> symbol type of the given finite tree automaton
	 * @param fta finite tree automaton to be applied to the given tree
	 * @param tree tree to be analysed
	 * 
	 * @return the set of states which the given finite tree automaton can reduce the given tree to
	 */
	public static <F extends RankedSymbol, Q extends State> 
	Set<Q> accessibleStatesFromConfigTree(FTA<F,Q,? extends FTARule<F,Q>> fta, Tree<BiSymbol<F,Q>> tree) {
		// set if reachable states
		Set<Q> ret = new HashSet<Q>();

		// if the root of t is a state, this state is reachable (and the only reachable one) 
		if (tree.getSymbol().isLeafType()){
			ret.add(tree.getSymbol().asLeafSymbol());
			return ret;
		} else {
			// states that can be reached at the subtrees of t 
			List<Set<Q>> subStateSets = new LinkedList<Set<Q>>();
			for (Tree<BiSymbol<F,Q>> s: tree.getSubTrees())
				subStateSets.add(accessibleStatesFromConfigTree(fta,s));

			// consider all rules r = f(q1,..,qn)->q having f = root of t and 
			// qi \in states that can be reached in the i-th subtree 
			for (FTARule<F,Q> r: fta.getRules()) {
				// 'f = root of t' 
				if (tree.getSymbol().asInnerSymbol().equals(r.getSymbol())) {
					// 'qi \in states that ...'
					Iterator<Set<Q>> accSet = subStateSets.listIterator();
					Iterator<Q> srcState = r.getSrcStates().listIterator();
					boolean ruleApplicable = true;
					while (accSet.hasNext()) {
						// if qi is not contained for some i, the rule cannot be applied
						if (!accSet.next().contains(srcState.next())) {
							ruleApplicable = false;
							break;
						}
					}
					// if the rule is applicable, the destination state is a reachable state 
					if (ruleApplicable)
						ret.add(r.getDestState());
				}
			}
			return ret;
		}
	}

}
