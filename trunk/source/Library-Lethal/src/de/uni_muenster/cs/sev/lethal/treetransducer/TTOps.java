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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_muenster.cs.sev.lethal.states.NamedState;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.Variable;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTACreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAOps;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTACreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTAEpsRule;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTARule;
import de.uni_muenster.cs.sev.lethal.utils.Converter;
import de.uni_muenster.cs.sev.lethal.utils.IdentityConverter;
import de.uni_muenster.cs.sev.lethal.utils.Pair;
import de.uni_muenster.cs.sev.lethal.utils.Triple;

/**
 * @author i_thes01
 *
 */
public class TTOps {
	

	
	/**
	 * Returns a tree transducer that recognizes exactly the union of the languages 
	 * of the given tree transducers.<br>
	 * The resulting tree transducer is in general non-deterministic and its state type
	 * is State.<br>
	 * <br>
	 * This is realized by guaranteeing that the states of the tree transducers are disjoint.
	 * (Embed them disjointly in new states.) Then construct a new finite tree automaton with 
	 * the union of states, union of final states and union of rules. 
	 * 
	 * @param <F> symbol type of the start alphabet of both tree transducers
	 * @param <G> symbol type of the destination alphabet of both tree transducers
	 * @param <Q1> state type of first tree transducer
	 * @param <Q2> state type pf second tree transducer

	 * @param tt1 the first tree transducer for the union
	 * @param tt2 the second tree transducer for the union
	 * 
	 * @return a tree transducer that recognizes exactly the union of the 
	 * languages of the given finite tree tree automata
	 */
	public static <F extends RankedSymbol, G extends RankedSymbol, Q1 extends State, Q2 extends State>
	GenTT<F,G,State> union(GenTT<F,G,Q1> tt1,GenTT<F,G,Q2> tt2){
		Converter<TTState<Q1,G>,TTState<State,G>> conv1 = new Converter<TTState<Q1,G>,TTState<State,G>>(){
			@Override
			public TTState<State, G> convert(TTState<Q1, G> a) {
				State stat = new NamedState<Pair<Q1,Boolean>>(new Pair<Q1,Boolean>(a.getState(),true));
				return new TTState<State,G>(stat,a.getVarTree());
			}	
		};
		Converter<TTState<Q2,G>,TTState<State,G>> conv2 = new Converter<TTState<Q2,G>,TTState<State,G>>(){
			@Override
			public TTState<State, G> convert(TTState<Q2, G> a) {
				State stat = new NamedState<Pair<Q2,Boolean>>(new Pair<Q2,Boolean>(a.getState(),false));
				return new TTState<State,G>(stat,a.getVarTree());
			}	
		};
		IdentityConverter<F> fc =  new IdentityConverter<F>();
		TTCreator<F,G,State> creator = new TTCreator<F,G,State>();
		/*for (TTState<Q1,G> state: tt1.getStates()){
			System.out.println(state + " converted " + conv1.convert(state));
		}*/
		
		return FTAOps.union(tt1,tt2,conv1,conv2,fc,fc,creator);
	}
	
	
	
	
	
	/**
	 * Computes a finite tree automaton which recognizes the language gained by applying a given
	 * tree transducer on all trees the given finite tree automaton accepts. <br>
	 * Note that the tree transducer must be linear and 
	 * that only the symbols of the finite tree automata are considered, which are also symbols
	 * of the tree transducer.
	 * <br>
	 * Algorithm:<br>
	 * for all TTRules f(q0,..,qn)->(q,u(x_0,...x_{n-1}))<br>
	 *   for all FTA-Rules f(p1,...,pn)->p<br>
	 *     add Rules to gain:<br>
	 *     u(x_0 <-(q0,p0), ... x_n <- (q_{n-1},p_{n-1})) -> (q,p)<br>
	 *     Therefore for each variable v_i, add an epsilon rule v_i->(q_i,p_i),<br>
	 *     if you have the destination states of the subtrees, s_i <br>
	 *     add a rule g(s_0, ..., s_{m-1}) --> s_g, produced of regarded rules and tree <br>
	 *     ad last add rule s_f -> (q,p).
	 * 
	 * @param <F> type of ranked symbols in the finite tree automaton and the start alphabet of the tree transducer
	 * @param <G> type of symbols in the destination alphabet
	 * @param <Q> type of states in the tree transducer
	 * @param <Q1> type of states in the given finite tree automaton
	 * @param <Q2> type of states in the resulting finite tree automaton
	 * @param <R1> type of rules in the given finite tree automaton
	 * @param <R2> type of rules in the resulting finite tree automaton
	 * @param <T> type of the resulting finite tree automaton
	 * @param tt given tree transducer, which is applied
	 * @param fta given finite tree automaton, the tree transducer is applied to
	 * @param sc Converter which converts pairs of states of fta and tt in states
	 * of the resulting finite tree automaton. The image must be disjoint with the image of tsc.
	 * @param tsc Converter which converts rules of fta and tt and variable trees into states
	 * of the resulting finite tree automaton. The image must be disjoint with the image of sc.
	 * @param creator finite tree automaton creator, which creates rules and automaton for the result.
	 * It is also used to eliminate epsilon rules.
	 * @return finite tree automaton which recognizes the language gained by applying the
	 * tree transducer on all trees the given finite tree automaton accepts.
	 */
	public static <F extends RankedSymbol,
	G extends RankedSymbol,
	Q extends State,
	Q1 extends State,
	Q2 extends State,
	R1 extends FTARule<F,Q1>,
	R2 extends FTARule<G,Q2>,
	T extends FTA<G,Q2,R2>>
	T runOnAutomaton(GenTT<F,G,Q> tt, 
			FTA<F,Q1,R1> fta, 
			Converter<Pair<Q,Q1>,Q2> sc, 
			Converter<Triple<TTRule<F,G,Q>,R1,Tree<BiSymbol<G,Variable>>>,Q2> tsc,
			FTACreator<G,Q2,R2,T> creator){
		if (!tt.isLinear())
			throw new IllegalArgumentException("The tree transducer must be linear.");
		
		Set<Q2> finals = new HashSet<Q2>();
		Set<R2> rules = new HashSet<R2>();
		Set<GenFTAEpsRule<Q2>> epsrules = new HashSet<GenFTAEpsRule<Q2>>();
		
		// consider all symbols which are in tt and fta, sort for arity.
		Map<Integer,ArrayList<F>> alphabet = new HashMap<Integer,ArrayList<F>>();
		for (F f: tt.getAlphabet()){
			if (fta.getAlphabet().contains(f)){
				if (alphabet.containsKey(f.getArity()))
					alphabet.get(f.getArity()).add(f);
				else  {
					ArrayList<F> set = new ArrayList<F>();
					set.add(f);
					alphabet.put(new Integer(f.getArity()),set);
				}
			}
		}
		// consider all symbols
		for (int arity: alphabet.keySet()){
			for (F symbol: alphabet.get(arity)){
				// consider all rules
				for (TTRule<F,G,Q> ttrule: tt.getSymbolRules(symbol)){
					for (R1 ftarule: fta.getSymbolRules(symbol)){
						Tree<BiSymbol<G,Variable>> varTree = ttrule.getDestTree();
						List<Q> ttSrcStates = ttrule.getSrcStatesAsQ();
						List<Q1> ftaSrcStates = ftarule.getSrcStates();
						List<Q2> newSrcStates = new LinkedList<Q2>();
						for (int i=0; i<arity; i++){
							newSrcStates.add(sc.convert(new Pair<Q,Q1>(
									ttSrcStates.get(i),ftaSrcStates.get(i))));
						}
						Q2 destState = sc.convert(new Pair<Q,Q1>(
								ttrule.getDestStateAsQ(),ftarule.getDestState()));
						if (tt.getFinalStates().contains(ttrule.getDestState()) || 
								fta.getFinalStates().contains(ftarule.getDestState())){
							finals.add(destState);
						}
						// produce rules for recognizing the variable tree, replace the variables in the right way
						Q2 state = produceTreeRules(ftarule,ttrule,varTree,rules,epsrules,newSrcStates,tsc,creator);
						// add one additional epsilon rule
						epsrules.add(new GenFTAEpsRule<Q2>(state,destState));
					}
				}
			}
		}
		// create corresponding finite tree automaton
		return creator.createFTA(tt.getDestAlphabet(), Collections.<Q2>emptySet(), finals, rules, epsrules);	
	}
	
	/*Helper Method for runOnAutomaton*/
	private static <F extends RankedSymbol,
	G extends RankedSymbol,
	Q extends State,
	Q1 extends State,
	Q2 extends State,
	R1 extends FTARule<F,Q1>,
	R2 extends FTARule<G,Q2>,
	T extends FTA<G,Q2,R2>> 
	Q2 produceTreeRules(R1 ftarule, TTRule<F,G,Q> ttrule, Tree<BiSymbol<G,Variable>> varTree, 
			Set<R2> rules, Set<GenFTAEpsRule<Q2>> epsrules,
			List<Q2> src,
			Converter<Triple<TTRule<F,G,Q>,R1,Tree<BiSymbol<G,Variable>>>,Q2> tsc,
			FTACreator<G,Q2,R2,T> creator){
		if (varTree.getSymbol().isLeafType()){
			// new epsilon rule from the corresponding srcStateslist
			int number = varTree.getSymbol().asLeafSymbol().getComponentNumber();
			Q2 desteps = tsc.convert(new Triple<TTRule<F,G,Q>,R1,Tree<BiSymbol<G,Variable>>>(ttrule,ftarule,varTree));
			epsrules.add(new GenFTAEpsRule<Q2>(src.get(number),desteps));
			return desteps;
		} else {
			// new rule with deststates of subtrees and deststate from the converter
			LinkedList<Q2> newsrc = new LinkedList<Q2>();
			for (Tree<BiSymbol<G,Variable>> sub: varTree.getSubTrees()){
				Q2 q = produceTreeRules(ftarule,ttrule,sub,rules,epsrules,src,tsc,creator);
				newsrc.add(q);
			}
			Q2 dest = tsc.convert(new Triple<TTRule<F,G,Q>,R1,Tree<BiSymbol<G,Variable>>>(ttrule,ftarule,varTree));
			rules.add(creator.createRule(varTree.getSymbol().asInnerSymbol(), newsrc, dest));
			return dest;
		}
		
	}
	
	/**
	 * Computes a finite tree automaton which recognizes the language gained by applying a given
	 * tree transducer on all trees the given finite tree automaton accepts. <br>
	 * The variant for generic finite tree automaton without converters and creators. The states of the 
	 * resulting finite tree automaton are in fact some NamedStates with very complicated names.
	 * 
	 * @param <F> type of ranked symbols in the finite tree automaton and the start alphabet of the tree transducer
	 * @param <G> type of symbols in the destination alphabet
	 * @param <Q> type of states in the tree transducer
	 * @param <Q1> type of states in the given finite tree automaton
	 * @param tt given tree transducer, which is applied
	 * @param fta given finite tree automaton, the tree transducer is applied to
	 * @return finite tree automaton which recognizes the language gained by applying the
	 * tree transducer on all trees the given finite tree automaton accepts. 
	 */
	public static <F extends RankedSymbol, G extends RankedSymbol, Q extends State, Q1 extends State>
	GenFTA<G,State> runOnAutomaton(GenTT<F,G,Q> tt, GenFTA<F,Q1> fta){
		Converter<Pair<Q,Q1>,State> sc = new Converter<Pair<Q,Q1>,State>(){
			@Override
			public State convert(Pair<Q, Q1> a) {
				return new NamedState<Object>(a);
			}
		};
		Converter<Triple<TTRule<F,G,Q>,GenFTARule<F,Q1>,Tree<BiSymbol<G,Variable>>>,State> tsc = 
			new Converter<Triple<TTRule<F,G,Q>,GenFTARule<F,Q1>,Tree<BiSymbol<G,Variable>>>,State>(){
				@Override
				public State convert(
						Triple<TTRule<F, G, Q>, GenFTARule<F, Q1>, Tree<BiSymbol<G, Variable>>> a) {
					return new NamedState<Object>(a);
				}
			
		};
		return runOnAutomaton(tt,fta,sc,tsc,new GenFTACreator<G,State>());
	}
	
	
	/**
	 * Converts a fitting generic tree transducer to an easy one. <br>
	 * This is useful for converting the results of the algorithms.
	 * 
	 * @param tt generic tree transducer of type RankedSymbol,RankedSymbol and State
	 * @return the same as easy tree transducer
	 */
	public static EasyTT convertToEasyTT(GenTT<RankedSymbol,RankedSymbol,State> tt){
		ArrayList<State> states = new ArrayList<State>();
		for (TTState<State,RankedSymbol> q: tt.getFinalStates()){
			states.add(q.getState());
		}
	/*	ArrayList<RankedSymbol> alph1 = new ArrayList<RankedSymbol>();
		for (RankedSymbol f: tt.getAlphabet()){
			alph1.add(f);
		}
		ArrayList<RankedSymbol> alph2 = new ArrayList<RankedSymbol>();
		for (RankedSymbol f: tt.getDestAlphabet()){
			alph2.add(f);
		}
		ArrayList<EasyTTRule> rules = new ArrayList<EasyTTRule>();
		for (TTRule<? extends RankedSymbol,? extends RankedSymbol,State> r: tt.getRules()){
			rules.add(new EasyTTRule((RankedSymbol)r.getSymbol(),r.getSrcStates(),r.getDestState()));
		}*/
		return new EasyTT(states,tt.getAlphabet(),tt.getDestAlphabet(),tt.getRules());
	}

}
