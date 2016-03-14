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
package de.uni_muenster.cs.sev.lethal.treetransducer;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.Variable;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.tree.common.TreeOps;
import de.uni_muenster.cs.sev.lethal.tree.common.VarTreeOps;
import de.uni_muenster.cs.sev.lethal.tree.standard.StdTreeCreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.AbstractModFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAEpsRule;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAOps;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTARule;
import de.uni_muenster.cs.sev.lethal.utils.Combinator;
import de.uni_muenster.cs.sev.lethal.utils.Pair;


/**
 * Class to represent tree tranducers.<br>
 * Tree transducers extend the functionality of finite tree automata. Like those, 
 * a tree transducer represents a language and can decide, whether a given tree
 * is contained in this language. Furthermore a tree transducer creates a new tree 
 * out of the given one and can therefore be used for some calculations on trees
 * or for changing trees into others. The functioning of this transforming is 
 * a bit similar to the one of a homomorphism.<br>
 * With these rules in a run of the tree automaton, recursively subtrees like f(q1,...,qn) 
 * are annotated by q, until no rule can be applied or until only one state remains. 
 * If the remaining state is in the final states, 
 * we say that the finite tree automaton accepts or recognizes the tree.
 * Simultaneously, a new tree is created out of the trees containig variables 
 * of the right side of the rules. 
 * 
 * @param <F> type of symbols of the start alphabet (left side of the rules)
 * @param <G> type of symbols of the destination alphabet (right side of the rules)
 * @param <Q> type of used states
 * 
 * @see FTA
 * @see TTRuleSet
 * 
 * @author Dorothea, Irene, Martin
 */
public class GenTT<F extends RankedSymbol, G extends RankedSymbol, Q extends State> 
implements FTA<F,TTState<Q,G>,TTRule<F,G,Q>>{

	/**
	 * States of the tree transducer. 
	 */
	protected Set<TTState<Q,G>> states;

	/**
	 * Final states for accepting trees and end. <br>
	 * Final states are a subset of states and they mark all states,
	 * on which a tree is accepted, when a run on a tree lands there.
	 */
	protected Set<TTState<Q,G>> finalStates;

	/**
	 * The start alphabet is a set of ranked symbols. The tree 
	 * transducer can run on all trees over this alphabet. <br>
	 * The left side of a rule which is not an epsilon rule
	 * always contains a symbol of the start alphabet.
	 */
	protected Set<F> startAlphabet;

	/**
	 * The destination alphabet is the alphabet of trees which
	 * are produced by applying the tree transducer.  <br>
	 * The variable trees on the right side of a transducer rule always
	 * consist of ranked symbols of the destination alphabet and of variables.
	 */
	protected Set<G> destAlphabet;

	/** 
	 * Here the rules are saved in an efficient form. <br>
	 * Normal rules have the form f(q1...qn)->(q,u), epsilon rules have the 
	 * form q1->(q,v), where q1,...qn,q are states, f is a ranked symbol
	 * of the start alphabet, u is a variable tree containing variables
	 * with numbers between 0 and n-1 and ranked symbols of the destination 
	 * alphabet and v is a variable tree containing only one variable
	 * with number 0 and ranked symbols of the destination alphabet.<br>
	 * Rules are used to apply a tree transducer on a tree, they build the base
	 * of the tree transducer.
	 * */
	protected TTRuleSet<F,G,Q> rules;

	/**
	 * Constructs a new tree transducer with given final states, 
	 * start alphabet, destination alphabet and rules given as TTRuleSet.
	 * The states are calculated from the rules.
	 * 
	 * @param finalStat final states
	 * @param startAlph start alphabet
	 * @param destAlph destination alphabet
	 * @param rul rules
	 * @param epsRul epsilon rules
	 */
	public GenTT(Collection<Q> finalStat, Collection<F> startAlph, Collection<G> destAlph, 
			Collection<? extends FTARule<F,TTState<Q,G>>> rul, Collection<? extends FTAEpsRule<TTState<Q,G>>> epsRul) {
		if (epsRul == null)    throw new IllegalArgumentException("GenTT(): epsRul must not be null.");
		if (rul == null)       throw new IllegalArgumentException("GenTT(): rul must not be null.");
		if (finalStat == null) throw new IllegalArgumentException("GenTT(): finalStat must not be null.");
		if (startAlph == null) throw new IllegalArgumentException("GenTT(): startAlph must not be null.");
		if (destAlph == null)  throw new IllegalArgumentException("GenTT(): destAlph must not be null.");
		
		finalStates = new HashSet<TTState<Q,G>>();
		for (Q q: finalStat){
			finalStates.add(new TTState<Q,G>(q));
		}
		startAlphabet = new HashSet<F>(startAlph);
		destAlphabet = new HashSet<G>(destAlph);
		rules = new TTRuleSet<F,G,Q>(rul,epsRul);
		states = rules.getAllContainedStates();
		//preserve invariants
		preserveInvariants();
	}
	
	
	/**
	 * Constructs a new tree transducer with given final states, 
	 * start alphabet, destination alphabet and rules given as TTRuleSet.
	 * The states are calculated from the rules.
	 * 
	 * @param finalStat final states
	 * @param startAlph start alphabet
	 * @param destAlph destination alphabet
	 * @param rul rules
	 */
	public GenTT(Collection<Q> finalStat, Collection<F> startAlph, Collection<G> destAlph, 
			Collection<? extends FTARule<F,TTState<Q,G>>> rul) {
		finalStates = new HashSet<TTState<Q,G>>();
		for (Q q: finalStat){
			finalStates.add(new TTState<Q,G>(q));
		}
		startAlphabet = new HashSet<F>(startAlph);
		destAlphabet = new HashSet<G>(destAlph);
		rules = new TTRuleSet<F,G,Q>(rul);
		states = rules.getAllContainedStates();
		//preserve invariants
		preserveInvariants();
	}


	/**
	 * Constructs a new tree transducer with given final states and rules. <br>
	 * The states and alphabets are calculated from the rules.
	 * 
	 * @param finalStat final states
	 * @param rul rules
	 * @param epsRul epsilon rules
	 */
	public GenTT(Collection<Q> finalStat, Collection<? extends FTARule<F,TTState<Q,G>>> rul, Collection<? extends FTAEpsRule<TTState<Q,G>>> epsRul) {
		finalStates = new HashSet<TTState<Q,G>>();
		for (Q q: finalStat){
			finalStates.add(new TTState<Q,G>(q));
		}
		startAlphabet = new HashSet<F>();
		destAlphabet = new HashSet<G>();
		rules = new TTRuleSet<F,G,Q>(rul,epsRul);
		//translate rules
		/*for (FTARule<F,TTState<Q,G>> rule: FTACreator.eliminateEpsilonRules(rul, epsRul)){
			rules.addRule(rule.getSymbol(),rule.getSrcStates(),rule.getDestState());
		}*/
		finalStates.addAll(finalStates);
		states = rules.getAllContainedStates();

		//preserve invariants
		preserveInvariants();
	}
	
	/**
	 * Constructs a new tree transducer with given final states and rules. <br>
	 * The states and alphabets are calculated from the rules.
	 * 
	 * @param newFinals final states
	 * @param newRules rules
	 */
	public GenTT(Collection<Q> newFinals,
			Collection<? extends FTARule<F, TTState<Q, G>>> newRules) {
		finalStates = new HashSet<TTState<Q,G>>();
		for (Q q: newFinals){
			finalStates.add(new TTState<Q,G>(q));
		}
		startAlphabet = new HashSet<F>();
		destAlphabet = new HashSet<G>();
		rules = new TTRuleSet<F,G,Q>(newRules);
		finalStates.addAll(finalStates);
		states = rules.getAllContainedStates();

		//preserve invariants
		preserveInvariants();
	}

	/**
	 * Preserves the invariants: final states are always states, all symbols occurring in the
	 * rules are contained in the start or the destination alphabet, respectively, 
	 * and all states in the rules are contained in the states.
	 */
	protected void preserveInvariants(){
		states.addAll(finalStates);
		states.addAll(rules.getAllContainedStates());
		startAlphabet.addAll(rules.getStartSymbols());
		destAlphabet.addAll(rules.getDestinationSymbols());
	}

	/**
	 * Checks whether the tree transducer accepts a given tree. <br>
	 * It works equivalent to the corresponding procedure at automatons, 
	 * it uses the doARun function.
	 * 
	 * @param tree tree to check whether the tree transducer will accept it
	 * @return whether a tree is accepted by the tree transducer
	 */
	public boolean decide(Tree<F> tree){
		return !doARun(tree).isEmpty();
	}

	/**
	 * Checks which trees are gained by transducing an given input tree.<br> 
	 * The method works recursively on the given tree, it is similar to the method
	 * in the class {@link FTAOps}. Additionally trees are constructed 
	 * by applying the tree transducer rules. 
	 * 
	 * @param tree input tree that is to be transduced
	 * @return the transduced trees where the tree transducer accepts the tree
	 */
	public Set<Tree<G>> doARun(Tree<F> tree){
		if (!startAlphabet.containsAll(TreeOps.getAllContainedSymbols(tree))){
			//throw new IllegalArgumentException("tree must have the same alphabet as the start alphabet of this tree transducer");
			return new HashSet<Tree<G>>(); 
		}
		Set<Tree<G>> ret = new HashSet<Tree<G>>();

		//compute accessible states
		Set<Pair<Q,Tree<G>>> accStates = accessibleStates(tree);
		//check if there is a final state
		for (Pair<Q,Tree<G>> pair: accStates){
			if (this.getFinalStates().contains(new TTState<Q,G>(pair.getFirst()))){
				ret.add(pair.getSecond());
			}
		}
		
		return ret;
	}


	/**
	 * Given a set of pairs of State and InputTree, collects all inputTrees 
	 * that are the second parameter of a pair where the first parameter is equal to 
	 * the given state q.
	 * 
	 * @param set set of pairs of state and input tree
	 * @param state the state which is to be the first parameter of collected pairs 
	 * @return all trees t where (q,t) is in set
	 */ 
	private Set<Tree<G>> contained(Set<Pair<Q,Tree<G>>> set, Q state){
		Set<Tree<G>> ret = new HashSet<Tree<G>>();
		for (Pair<Q,Tree<G>> pair: set){
			if (pair.getFirst().equals(state)){
				ret.add(pair.getSecond());
			}
		}
		return ret;
	}

	/**
	 * Method which is used for the decide-method to get all states 
	 * which can be reached with a given tree. It does not matter whether
	 * it is a final state or not. <br>
	 * Algorithm:<br>
	 * The method works recursively on the tree, first it is applied to all subtrees.
	 * Having collected the accessible states for the subtrees, all rules are collected
	 * which can be applied. Then the transduced tree is computed from the right side of the rule
	 * and state and tree are stored in a set which is, at last, returned. 
	 * 
	 * @param t tree, input for the tree automaton, should be an input tree
	 * @return the set of reachable states and reached trees of destination alphabet
	 */
	public Set<Pair<Q,Tree<G>>> accessibleStates(Tree<F> t) {
		List<Set<Pair<Q,Tree<G>>>> subStates = new LinkedList<Set<Pair<Q,Tree<G>>>>();
		Set<Pair<Q,Tree<G>>> ret = new HashSet<Pair<Q,Tree<G>>>();

		// get states and trees of the subtrees
		for (Tree<F> sub: t.getSubTrees()){
			subStates.add(this.accessibleStates(sub));
		}

		F f = t.getSymbol();
		int n = f.getArity();	
		// checks whether there are some fitting states for the rules, breaks otherwise
		boolean someFittingRules = true;

		// for every rule look if there must be added something (or something more)
		for (List<TTState<Q,G>> ruleStates: this.rules.getSymbolRules(f).keySet()){
			// for all accessible states
			Collection<TTState<Q,G>> destStates = rules.getDestStates(f, ruleStates);
			for (TTState<Q,G> q: destStates){
				// get the variable trees to insert the sub tree things
				Tree<BiSymbol<G,Variable>> varTree = q.getVarTree();
				// build subtrees things
				LinkedList<Set<Tree<G>>> treesToInsert = new LinkedList<Set<Tree<G>>>();

				for (int i = 0; i<n; i++){
					// accessible Input {t_ji, j runs}
					Set<Tree<G>> allTreesWithStatei = contained(subStates.get(i),ruleStates.get(i).getState());

					//break if there is nothing
					if (allTreesWithStatei.isEmpty()){
						someFittingRules = false;
						break; 
					}
					treesToInsert.add(allTreesWithStatei);
				}

				if (!someFittingRules){
					someFittingRules = true;
					break;
				} else {
					for (List<Tree<G>> replaceTrees: Combinator.cartesianProduct(treesToInsert)){
						// build tree for output
						Tree<G> functionTree = VarTreeOps.replaceVariables(varTree,replaceTrees, new StdTreeCreator<G>());
						ret.add(new Pair<Q,Tree<G>>(q.getState(),functionTree));
					}
				}
			}
		}
		return ret;
	}

	/**
	 * Returns the states of the tree transducer.
	 * 
	 * @return the states
	 */
	@Override
	public Set<TTState<Q,G>> getStates() {
		return states;
	}

	/**
	 * Returns the final states of the tree transducer,
	 * that are the states where the tree transducer accepts.
	 * 
	 * @return the finalStates
	 */
	public Set<TTState<Q,G>> getFinalStates() {
		return finalStates;
	}

	/**
	 * Returns the start alphabet of the tree transducer, i.e. the symbols 
	 * of the left side of the rules.
	 * 
	 * @return the startAlphabet
	 */
	public Set<F> getStartAlphabet() {
		return startAlphabet;
	}

	/**
	 * Returns the destination alphabet of the tree transducer, i.e. the symbols
	 * of the right side of the rules in variable trees.
	 * 
	 * @return the destAlphabet
	 */
	public Set<G> getDestAlphabet() {
		return destAlphabet;
	}

	/**
	 * Returns the set of rules of the tree transducer.
	 * 
	 * @return the rules
	 */
	public Set<? extends TTRule<F, G, Q>> getRules() {
		return this.rules.getRulesAsSet();
	}


	/**
	 * Checks whether the tree transducer is linear, i.e. in each rule every variable occurs just once. 
	 * Therefore a corresponding method in {@link VarTreeOps} is used.
	 * 
	 * @return true if and only if the tree transducer is linear, 
	 * i.e. in each rule every variable occurs just once. 
	 */
	public boolean isLinear(){
		//all variable trees must be linear
		for (Tree<BiSymbol<G,Variable>> var: rules.getAllVariableTrees()){
			if (!VarTreeOps.isLinear(var))
				return false;
		}
		return true;
	}


	/**
	 * A part of the functionality of a tree transducer is the same as the one of a finite tree automaton.
	 * Thus such a corresponding the finite tree automaton can be obtained from the transducer by 
	 * transforming the rules (just the first parameter of each right side is needed).
	 * 
	 * @return the finite tree automaton which is inside the tree transducer
	 */
	public AbstractModFTA<F,Q, ? extends FTARule<F,Q>> getFTAPart(){
		List<GenFTARule<F,Q>> newrules = new LinkedList<GenFTARule<F,Q>>();
		for (TTRule<F,G,Q> rule: rules.getRulesAsList()){
			newrules.add(new GenFTARule<F,Q>(rule.getSymbol(),rule.getSrcStatesAsQ(),rule.getDestStateAsQ()));
		}
		List<Q> finals = new LinkedList<Q>();
		for (TTState<Q,G> qf: finalStates){
			finals.add(qf.getState());
		}
		GenFTA<F,Q> epsfta = new GenFTA<F,Q>(newrules, finals);
		epsfta.addSymbols(this.startAlphabet);
		return epsfta;
	}

	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString(){
		return "TreeTransducer \n With start alphabet: " + startAlphabet
		+ "\n With destination alphabet: " + destAlphabet
		+ "\n With final states: " + finalStates
		+ "\n With rules: \n" + rules;
	}

	
	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA#getAlphabet()
	 */
	@Override
	public Set<F> getAlphabet() {
		return startAlphabet;
	}

	
	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA#getSymbolRules(de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol)
	 */
	@Override
	public Set<? extends TTRule<F, G, Q>> getSymbolRules(F f) {
		return rules.getSymbolRulesAsTTRules(f);
	}
	

}
