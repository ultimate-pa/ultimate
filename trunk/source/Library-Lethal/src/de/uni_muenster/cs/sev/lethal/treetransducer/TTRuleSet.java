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
package de.uni_muenster.cs.sev.lethal.treetransducer;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.Variable;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.tree.common.TreeCreator;
import de.uni_muenster.cs.sev.lethal.tree.common.TreeOps;
import de.uni_muenster.cs.sev.lethal.tree.common.VarTreeOps;
import de.uni_muenster.cs.sev.lethal.tree.standard.StdTreeCreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAEpsRule;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;

/**
 * This class encapsulates the rule set of an {@link EasyTT} and
 * stores it in an efficient way for applying a tree transducer to a tree.
 * There are different ways to create the rule set. <br>
 * The idea of applying rules is described in {@link EasyTT},
 * but the use of TTRuleSet is always the same: 
 * Foremost the set is searched for the rules with the right symbol, 
 * then for the list of states that is to be in the left side of the rule. 
 * Then the right side of the rule - i.e. a state and a tree containing variables - 
 * can be worked with. This is realized by using maps.
 * 
 * @param <F> type of symbols of the start alphabet (left side of the rules)
 * @param <G> type of symbols of the destination alphabet (right side of the rules)
 * @param <Q> type of used states
 * 
 * @see EasyTT
 * @see TTRule
 * @see TTEpsRule
 * 
 * @author Dorothea, Irene, Martin
 */
public class TTRuleSet<F extends RankedSymbol, G extends RankedSymbol, Q extends State> {

	/**
	 * Rules of a tree transducer. <br>
	 * Such a rule has the form  f(q_1,...,q_n)->q(u), 
	 * where u is a tree containing symbols of the destination alphabet 
	 * and variables x_1,...x_n 
	 */
	private Map<F,HashMap<List<TTState<Q,G>>,Set<TTState<Q,G>>>> rules;


	/**
	 * Constructs a new TTRuleSet using the inner efficient structure of the TTRuleSet with HashMap.
	 * As it is not easy to build up, there are alternatives.<br>
	 * This constructor is only to use for the copy-method, it makes a deep copy.
	 * 
	 * @param rules rules of the form f(q_1,...,q_n)->q(u), where u is a tree 
	 * containing ranked symbols of the destination alphabet and variables x_1,...x_n
	 */
	private TTRuleSet(Map<F,HashMap<List<TTState<Q,G>>,Set<TTState<Q,G>>>> rules){
		this.rules = new HashMap<F,HashMap<List<TTState<Q,G>>,Set<TTState<Q,G>>>>();
		for (F f: rules.keySet()){
			HashMap<List<TTState<Q,G>>,Set<TTState<Q,G>>> newmap = new HashMap<List<TTState<Q,G>>,Set<TTState<Q,G>>>();
			for (List<TTState<Q,G>> src: rules.get(f).keySet()){
				Set<TTState<Q,G>> newset = new HashSet<TTState<Q,G>>(rules.get(f).get(src));
				newmap.put(new LinkedList<TTState<Q,G>>(src), newset);
			}
			this.rules.put(f, newmap);
		}
	}


	/**
	 * Constructor using TTRules but no epsilon rules. 
	 * The rules are transformed in the efficient structure.
	 * 
	 * @param rules rules of the tree transducer as a collection of TTRules
	 */
	public TTRuleSet(Collection<? extends FTARule<F,TTState<Q,G>>> rules){
		setRules(rules); 
	}


	/**
	 * Constructor using {@link TTRule TTRules} and {@link TTEpsRule TTEpsRules}. 
	 * The rules are transformed in the efficient structure, the epsilon rules 
	 * are eliminated.
	 * 
	 * @param rul collection of tree transducer rules
	 * @param epsRul collection of tree transducer epsilon rules, which are going to be eliminated
	 */
	public TTRuleSet(Collection<? extends FTARule<F,TTState<Q,G>>> rul,
			Collection<? extends FTAEpsRule<TTState<Q,G>>> epsRul){
		// eliminate epsilon rules
		Collection<FTARule<F,TTState<Q,G>>> nrules = eliminateEpsilonRules(rul, epsRul);
		
		setRules(nrules);
	}
	
	
	

	/**
	 * Given rules, final states and additional epsilon rules, eliminates the epsilon rules.<br>
	 * First, the epsilon cover of each state is calculated, that is the set of all states
	 * which can be reached by only applying epsilon rules. Then, for each rule f(q1,...qn)->q
	 * and each state r in the epsilon cover of q, a rule f(q1,...,qn)->r is added.
	 * 
	 * @param rules normal rules of the represented finite tree automaton
	 * @param epsRules epsilon rules of the represented finite tree automaton which are to be eliminated
	 * 
	 * @return a pair consisting of normal rules and final states, which represents a finite tree
	 * automaton where the supplied epsilon rules have been eliminated.
	 */
	protected Collection<FTARule<F,TTState<Q,G>>> eliminateEpsilonRules(Collection<? extends FTARule<F,TTState<Q,G>>> rules, 
			Collection<? extends FTAEpsRule<TTState<Q,G>>> epsRules) {
		Collection<FTARule<F,TTState<Q,G>>> newRules = new LinkedList<FTARule<F,TTState<Q,G>>>(rules);
	
		/* map each state q to the states which can be reached from q by applying only epsilon rules */
		Map<TTState<Q,G>,Collection<TTState<Q,G>>> epsCover = new HashMap<TTState<Q,G>,Collection<TTState<Q,G>>>();
		
		/* map each state q to the states p, such that p -> q is an epsilon rule */
		Map<TTState<Q,G>,Collection<TTState<Q,G>>> srcStates = new HashMap<TTState<Q,G>,Collection<TTState<Q,G>>>();
		
		/* map each state q to the states r, such that q -> r is an epsilon rule */
		Map<TTState<Q,G>,Collection<TTState<Q,G>>> destStates = new HashMap<TTState<Q,G>,Collection<TTState<Q,G>>>();
		
		/* list of states which still have to be examined*/
		LinkedList<TTState<Q,G>> worklist = new LinkedList<TTState<Q,G>>();
		
		TreeCreator<BiSymbol<G,Variable>,Tree<BiSymbol<G,Variable>>> tc = new StdTreeCreator<BiSymbol<G,Variable>>();
		
		/* initialize epsCover, destStates and srcStates:
		 * for each epsilon rule (q,r) make sure that:
		 * - r \in destStates(q)
		 * - q \in srcStates(r)
		 * - q \in epsCover(q) (Note, that this is sufficient, since
		 * - the epsCover of a state s is trivial, if s is not the source state of
		 * an epsilon rule)
		 * - r is on the work list
		 */
		for (FTAEpsRule<TTState<Q,G>> e: epsRules) {
			TTState<Q,G> qsrc = e.getSrcState();
			TTState<Q,G> qdest = e.getDestState();
			worklist.add(e.getSrcState());
			Collection<TTState<Q,G>> qEpsCover;
			Collection<TTState<Q,G>> qdestSrcStates;
			Collection<TTState<Q,G>> qsrcDestStates;

			if (epsCover.containsKey(qsrc))
				qEpsCover = epsCover.get(qsrc);
			else {
				qEpsCover = new HashSet<TTState<Q,G>>();
			//	qEpsCover.add(qsrc);
				epsCover.put(qsrc, qEpsCover);
			}

			/* add qsrc to destStates(qdest) */
			if (srcStates.containsKey(qdest))
				qdestSrcStates = srcStates.get(qdest);
			else {
				/* a list is sufficient since the epsilon rules are represented
				 * as a set, so a rule q->r is contained at most once, so
				 * qdestSrcStates won't contain duplicates as well */
				qdestSrcStates = new LinkedList<TTState<Q,G>>(); 
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
				qsrcDestStates = new LinkedList<TTState<Q,G>>();
				destStates.put(qsrc, qsrcDestStates);
			}
			qsrcDestStates.add(qdest);
		}
		
		//System.out.println("epsCover: " + epsCover);
		//System.out.println("destStates: " + destStates);
		//System.out.println("srcStates: " + srcStates);
		
		/* compute the eps-cover of the left sides of the eps rules */
		while (!worklist.isEmpty()) {
			TTState<Q,G> q = worklist.poll();
			Collection<TTState<Q,G>> qEpsCover = epsCover.get(q);
			boolean changed = false;
			
			/*
			 * update the eps-cover of q by adding all eps-covers of
			 * adjacent states, i.e. all elements of destStates(q)
			 */
			for (TTState<Q,G> r: destStates.get(q)) {
				
				changed = changed || qEpsCover.add(r);
				
				if (epsCover.containsKey(r)) {
					for (TTState<Q,G> s: epsCover.get(r)){
						//System.out.println(s);
						if (qEpsCover.add(new TTState<Q,G>(s.getState(),
								VarTreeOps.replaceOneVariable(s.getVarTree(), r.getVarTree(), tc)))){
							changed = false;
						}
					}
					// changed = changed || qEpsCover.addAll(epsCover.get(r));
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
	//	System.out.println("epsCover " +epsCover);
		
		/*
		 * group the rules by destination states, so that rules
		 * can easily be found later
		 */
		Map<TTState<Q,G>,Collection<FTARule<F,TTState<Q,G>>>> rulesByDestStates = 
			new HashMap<TTState<Q,G>,Collection<FTARule<F,TTState<Q,G>>>>();
		for (FTARule<F,TTState<Q,G>> r: rules) {
			TTState<Q,G> qdest = r.getDestState();
			Collection<FTARule<F,TTState<Q,G>>> qdestRules;
			if (rulesByDestStates.containsKey(qdest))
				qdestRules = rulesByDestStates.get(qdest);
			else {
				/* each rule occurs at most once, so a list is sufficient */
				qdestRules = new LinkedList<FTARule<F,TTState<Q,G>>>(); 
				rulesByDestStates.put(qdest, qdestRules);
			}
			qdestRules.add(r);
		}
		
		for (TTState<Q,G> q: epsCover.keySet()) {
			for (TTState<Q,G> r: epsCover.get(q)) {
				if (rulesByDestStates.containsKey(q))
					for (FTARule<F,TTState<Q,G>> qRule: rulesByDestStates.get(q)) {
						/*
						 * for each rule of the form f(q1,...,qn) -> q and
						 * each state r contained in the eps-cover of q,
						 * add a rule f(q1,...,qn) -> r
						 */
						newRules.add(new TTRule<F,G,Q>(qRule.getSymbol(), qRule.getSrcStates(), 
								new TTState<Q,G>(r.getState(),
								VarTreeOps.replaceOneVariable(r.getVarTree(),qRule.getDestState().getVarTree(),tc))));
					}
			}


		}
		//System.out.println(newRules);
		return newRules;
	}
	

	/**
	 * Transforms the rules in the efficient form we choosed and saves it.<br> 
	 * The rules are given as triples like (f, (q1,...,qn), q) for the 
	 * rule f(q1,...qn) -> q. <br>
	 * This is realized simply by transforming rule by rule.
	 * 
	 * @param ruleset rules as f(q1,...qn) -> (q,u), saved as set of triples (f, (q1,...,qn), (q,u))
	 */
	private void setRules(Collection<? extends FTARule<F,TTState<Q,G>>> ruleset){
		rules = new HashMap<F,HashMap<List<TTState<Q,G>>,Set<TTState<Q,G>>>>();
		for (FTARule<F,TTState<Q,G>> trip: ruleset){
			if (trip.getDestState().getVarTree() == null){
				throw new IllegalArgumentException("Destination states must contain a variable tree");
			}
			if (rules.containsKey(trip.getSymbol())){
				// if states already in list add a new entry in the collection
				if (rules.get(trip.getSymbol()).containsKey(trip.getSrcStates())){
					for (TTState<Q,G> s: rules.get(trip.getSymbol()).get(trip.getSrcStates())){
						if (s.equals(trip.getDestState()) && !(trip.getDestState().getVarTree().equals(s.getVarTree()))){
							throw new IllegalArgumentException("There are two rules like f(q1,...qn)->(q,u) and f(q1,...qn)->(q,v)"
									+"with u != v. This is impossible. Replace the rules by: f(q1,...qn)->(q,u)," +
							" f(q1,...qn)->(p,v) and p -> (q,var).");
						}
					}
					rules.get(trip.getSymbol()).get(trip.getSrcStates()).add(trip.getDestState());
				} else {
					// add a new entry in the second map
					HashSet<TTState<Q,G>> set = new HashSet<TTState<Q,G>>();
					set.add(trip.getDestState());
					rules.get(trip.getSymbol()).put(trip.getSrcStates(), set);
				}
			} else {
				// insert in the first map a new entry
				HashMap<List<TTState<Q,G>>,Set<TTState<Q,G>>> map = new HashMap<List<TTState<Q,G>>,Set<TTState<Q,G>>>();
				HashSet<TTState<Q,G>> set = new HashSet<TTState<Q,G>>();
				set.add(trip.getDestState());
				map.put(trip.getSrcStates(), set);
				rules.put(trip.getSymbol(), map);
			}
		}
		//epsRules = new HashMap<TTState<Q,G>,Set<TTState<Q,G>>>();
	}


	/**
	 * Gives the rules as list of {@link TTRule tree transducer rules}
	 * for rules like f(q1,..qn)->(q,u).
	 * 
	 * @return rules as list of tree transducer rules
	 */
	public List<TTRule<F,G,Q>> getRulesAsList(){
		List<TTRule<F,G,Q>> ret = new LinkedList<TTRule<F,G,Q>>();
		for (F f: this.rules.keySet()){
			for (List<TTState<Q,G>> src: this.rules.get(f).keySet()){
				for (TTState<Q,G> dest: this.rules.get(f).get(src)){
					ret.add(new TTRule<F,G,Q>(f,src,dest));
				}
			}
		}
		return ret;
	}


	/**
	 * Returns all contained start symbols.
	 * 
	 * @return contained start symbols
	 */
	public Set<F> getStartSymbols(){
		return rules.keySet();
	}

	/**
	 * Returns all contained destination symbols.
	 * 
	 * @return contained destination symbols
	 */
	public Set<G> getDestinationSymbols(){
		Collection<Tree<BiSymbol<G,Variable>>> col = getAllVariableTrees();

		Set<BiSymbol<G,Variable>> set = new HashSet<BiSymbol<G,Variable>>();
		for (Tree<BiSymbol<G,Variable>> t: col){
			set.addAll(TreeOps.getAllContainedSymbols(t));	
		}
		Set<G> ret = new HashSet<G>();	
		for (BiSymbol<G,Variable> s:set){
			if (s.isInnerType()){
				ret.add(s.asInnerSymbol());
			}
		}
		return ret;
	}


	/**
	 * Returns a copy of the TTRuleSet for manipulate.
	 * 
	 * @return a copy of this rule set
	 */
	public TTRuleSet<F,G,Q> getCopy(){
		return new TTRuleSet<F,G,Q>(rules);
	}


	/**
	 * Collects all rules having the given symbol f and returns a map that 
	 * maps the list of source states to the corresponsing destination state,
	 * where all states are given as tree transducer states.<br>
	 * This method is efficient because of the choosen structure. 
	 * 
	 * @param f function symbol we search in rules
	 * @return rest of the rules, you need to put in a list of states
	 */
	public HashMap<List<TTState<Q,G>>,Set<TTState<Q,G>>> getSymbolRules(F f){
		if (this.rules.containsKey(f))
			return this.rules.get(f);
		else return new HashMap<List<TTState<Q,G>>,Set<TTState<Q,G>>>();
	}

	/**
	 * Returns all rules using the given symbol f as set of 
	 * {@link TTRule tree transducer rules}.<br>
	 * This method is efficient because of the choosen structure. 
	 * 
	 * @param f function symbol we search in rules
	 * @return rest of the rules, you need to put in a list of states
	 */
	public Set<TTRule<F,G,Q>> getSymbolRulesAsTTRules(F f){
		Set<TTRule<F,G,Q>> ret = new HashSet<TTRule<F,G,Q>>();
		if (this.rules.containsKey(f)){
			for (List<TTState<Q,G>> src: this.rules.get(f).keySet()){
				for (TTState<Q,G> dest: this.rules.get(f).get(src)){
					ret.add(new TTRule<F,G,Q>(f,src,dest));
				}
			}
		}
		return ret;
	}

	/**
	 * Given the values of the left side of a rule, 
	 * returns all corresponding right sides.<br>
	 * This method is efficient because of the choosen structure. 
	 * 
	 * @param f ranked symbol
	 * @param ruleStates source states for a rule
	 * @return destination states and variableTrees of right side of the rules 
	 * having the given symbol and source states as left side.
	 */
	public Set<TTState<Q,G>> getDestStates(F f, List<TTState<Q,G>> ruleStates) {
		if (this.getSymbolRules(f).containsKey(ruleStates))
			return this.getSymbolRules(f).get(ruleStates);
		else return new HashSet<TTState<Q,G>>();
	}


	/**
	 * Returns the states on the right side, i.e. the destination state 
	 * of a rule with the given left side. 
	 * It can be more than one state, since the tree transducer 
	 * rules are in general non-deterministic. <br>
	 * This method is efficient because of the choosen structure. 
	 * 
	 * @param f ranked symbol
	 * @param ruleStates source states for a rule
	 * @return all states you can achieve with this rule (without VariableTrees)
	 */
	/*	public Set<TTState<Q,G>> getDestinationStates(F f, List<TTState<Q,G>> ruleStates) {
		Set<TTState<Q,G>> destination = this.getDestination(f,ruleStates);
		Set<Tree<BiSymbol<G,Variable>>> ret = new HashSet<Tree<BiSymbol<G,Variable>>>();
		for (TTState<Q,G> pair: destination){
			if (pair.getFirst().equals(q))
				ret.add(pair.getSecond());
		}
		return ret;*/
	/*Collection<Pair<Q,Tree<BiSymbol<G,Variable>>>> destination = this.getDestination(f,ruleStates);
		Set<Q> ret = new HashSet<Q>();
		for (Pair<Q,Tree<BiSymbol<G,Variable>>> pair: destination){
			ret.add(pair.getFirst());
		}
		return ret;*/
	/*	} */


	/**
	 * Calculates which VariableTrees can be achieved by applying a rule
	 * with the given symbol, the given source states and a given destination rule.
	 * Since the rules are non deterministic, there can be more than one rules with this definition.
	 * 
	 * @param f function symbol
	 * @param ruleStates source states for a rule
	 * @param q state for destination
	 * 
	 * @return all VariableTrees which can be achieved by the rule
	 */
	/*	public Set<Tree<BiSymbol<G,Variable>>> getDestinationTreesForState(F f, List<Q> ruleStates, Q q) {
		Collection<Pair<Q,Tree<BiSymbol<G,Variable>>>> destination = this.getDestination(f,ruleStates);
		Set<Tree<BiSymbol<G,Variable>>> ret = new HashSet<Tree<BiSymbol<G,Variable>>>();
		for (Pair<Q,Tree<BiSymbol<G,Variable>>> pair: destination){
			if (pair.getFirst().equals(q))
				ret.add(pair.getSecond());
		}
		return ret;
	}*/

	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString(){
		String ret = "";
		for (F f: rules.keySet()){
			for (List<TTState<Q,G>>  src: rules.get(f).keySet()){
				for (TTState<Q,G> dest: rules.get(f).get(src)){
					ret += f.toString() + src.toString() + "->" + dest.toString() + "\n";
				}
			}
		}
		/*	ret += "\n epsilon rules:";
		for (State q: epsRules.keySet()){
			ret += "\n"+  q + "->" + epsRules.get(q);
		}*/
		return ret;
	}


	/**
	 * Returns all states and corresponding variable trees you can achieve by 
	 * applying epsilon rules on a given start state.<br>
	 * It is used in {@link GenTT}.
	 * 
	 * @param q start state
	 * @return all states and corresponding variable trees you can achieve by applying epsilon rules
	 */
	/*	public Set<TTState<Q,G>> getEpsCover(TTState<Q,G> q){
		return calcEpsCover(q,new HashSet<TTState<Q,G>>());
	}


	private Set<TTState<Q,G>> calcEpsCover(TTState<Q,G> q, Set<TTState<Q,G>> alreadyCalc ){
		if (epsRules.containsKey(q)){
			//epsCover.add(q);
			for (TTState<Q,G> s: epsRules.get(q)){
				if (!alreadyCalc.contains(s)){
					alreadyCalc.add(s);
					alreadyCalc.addAll(calcEpsCover(s,alreadyCalc));
				}
			}
		}
		return alreadyCalc;
	}*/


	/**
	 * Calculates all variable trees which occur in the rules.
	 * 
	 * @return all variables trees which are in the rules
	 */
	public Collection<Tree<BiSymbol<G,Variable>>> getAllVariableTrees() {
		Set<Tree<BiSymbol<G,Variable>>> ret = new HashSet<Tree<BiSymbol<G,Variable>>>();
		for (F f: this.rules.keySet()){
			for (List<TTState<Q,G>> src: rules.get(f).keySet()){
				for (TTState<Q,G> p: rules.get(f).get(src)){
					if (p.getVarTree() != null)
						ret.add(p.getVarTree());
					else throw new IllegalArgumentException("Something wrong with the rules of the tree transducer");
				}
			}
		}
		/*for (TTState<Q,G> q: this.epsRules.keySet()){
			for (TTState<Q,G> dest: epsRules.get(q)){
				ret.add(dest.getVarTree());
			}
		}*/
		return ret;
	}


	/**
	 * Returns all states that occur in the rules.
	 * 
	 * @return all states that occur in the rules
	 */
	public Set<TTState<Q,G>> getAllContainedStates() {
		Set<TTState<Q,G>> ret = new HashSet<TTState<Q,G>>();
		for (F f: this.rules.keySet()){
			for (List<TTState<Q,G>> src: rules.get(f).keySet()){
				for (TTState<Q,G> q: src){
					ret.add(q);
				}
				for (TTState<Q,G> p: rules.get(f).get(src)){
					ret.add(p);
				}
			}
		}
		/*	for (TTState<Q,G> q: this.epsRules.keySet()){
			ret.add(q);
			for (TTState<Q,G> dest: epsRules.get(q)){
				ret.add(dest);
			}
		}*/
		return ret;
	}


	/**
	 * Returns all epsilon rules as a list of {@link TTEpsRule tree transducer epsilon rules}.
	 * 
	 * @return all epsilon rules as a list of {@link TTEpsRule tree transducer epsilon rules}.
	 */
	/*	public List<TTEpsRule<G,Q>> getEpsRulesAsList() {
		LinkedList<TTEpsRule<G,Q>> ret = new LinkedList<TTEpsRule<G,Q>>();
		for (TTState<Q,G> q: epsRules.keySet()){
			for (TTState<Q,G> p: epsRules.get(q)){
				ret.add(new TTEpsRule<G,Q>(q,p));
			}
		}
		return ret;
	}*/

	/**
	 * Returns all rules as a set of {@link TTEpsRule tree transducer epsilon rules}.
	 * 
	 * @return all rules as a set of {@link TTEpsRule tree transducer epsilon rules}.
	 */
	public Set<? extends TTRule<F,G,Q>> getRulesAsSet() {
		Set<TTRule<F,G,Q>> ret = new HashSet<TTRule<F,G,Q>>();
		for (F f: rules.keySet()){
			for (List<TTState<Q,G>> src: rules.get(f).keySet()){
				for (TTState<Q,G> p: rules.get(f).get(src)){
					ret.add(new TTRule<F,G,Q>(f,src,p));
				}
			}
		}
		return ret;
	}

	/**
	 * Adds a rule to the rules set. <br>
	 * The method is used in the constructor of {@link GenTT}.
	 * 
	 * @param symbol symbol of the new rules
	 * @param src source states of the new rule
	 * @param dest destination state (and tree) of the new rule
	 */
	void addRule(F symbol, List<TTState<Q,G>> src, TTState<Q,G> dest){
		if (rules.containsKey(symbol)){
			if (rules.get(symbol).containsKey(src)){
				for (TTState<Q,G> s: rules.get(symbol).get(src)){
					if (dest.getVarTree() != null && s.equals(dest) && !(dest.getVarTree().equals(s.getVarTree()))){
						throw new IllegalArgumentException("There are two rules like f(q1,...qn)->(q,u) and f(q1,...qn)->(q,v)"
								+"with u != v. This is impossible. Replace the rules by: f(q1,...qn)->(q,u)," +
						" f(q1,...qn)->(p,v) and p -> (q,var).");
					}
				}
				rules.get(symbol).get(src).add(dest);
			} else {
				Set<TTState<Q,G>> set = new HashSet<TTState<Q,G>>();
				set.add(dest);
				rules.get(symbol).put(src, set);
			}

		} else {
			HashMap<List<TTState<Q,G>>,Set<TTState<Q,G>>> map = new HashMap<List<TTState<Q,G>>,Set<TTState<Q,G>>>();
			Set<TTState<Q,G>> set = new HashSet<TTState<Q,G>>();
			set.add(dest);
			map.put(src, set);
			rules.put(symbol,map);
		}
	}


	/*	public boolean containsRule(TTRule<F,G,Q> rule){
		return this.getRulesAsList().contains(rule);
	}
	 */
}
