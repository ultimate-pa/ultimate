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
package de.uni_muenster.cs.sev.lethal.hom;

import de.uni_muenster.cs.sev.lethal.factories.StateFactory;
import de.uni_muenster.cs.sev.lethal.factories.TreeFactory;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_muenster.cs.sev.lethal.states.NamedState;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.Variable;
import de.uni_muenster.cs.sev.lethal.symbol.standard.NamedVariable;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.tree.common.TreeCreator;
import de.uni_muenster.cs.sev.lethal.tree.common.VarTreeOps;
import de.uni_muenster.cs.sev.lethal.tree.standard.StdTreeCreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.AbstractModFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTACreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTARule;
import de.uni_muenster.cs.sev.lethal.utils.Converter;
import de.uni_muenster.cs.sev.lethal.utils.Pair;


/**
 * Represents a homomorphism between two alphabets using generic types.
 * 
 * @see Hom
 * @see HomOps
 * 
 * @param <F> type of symbols in source alphabet of the homomorphism
 * @param <G> type of symbols in destination alphabet of the homomorphism
 * 
 * @author Dorothea, Irene, Martin
 */
public class GenHom<F extends RankedSymbol, G extends RankedSymbol> extends AbstractHom<F,G,Variable>{


	/**
	 * Creates an empty homomorphism.
	 */
	public GenHom() {
		super();
	}

	/**
	 * Creates a homomorphism out of a given map that specifies the homomorphism.
	 * 
	 * @param h map which specifies the homomorphism 
	 */
	public GenHom(Map<F,Tree<? extends BiSymbol<G,Variable>>> h) {
		super(h);
	}


	/**
	 * Creates a homomorphism out of a map which maps each symbol of the source alphabet 
	 * to a tree and another map that specifies which constants in the trees are to be
	 * be replaced by which homomorphism variables (using the number of the homomorphism
	 * variable). <br> 
	 * 
	 * The keys of the map must be symbols with arity 0. 
	 * 
	 * @param toInts map which maps some occurring constants (symbols with arity 0) 
	 * to Integers which are needed to define the homomorphism
	 * @param hmap Map which specifies the homomorphism except the ordering of the variables
	 */
	public GenHom(Map<G,Integer> toInts, Map<F,Tree<G>> hmap) {
		super();
		if (toInts == null) throw new IllegalArgumentException("GenHom(): toInts must not be null.");
		if (hmap == null) throw new IllegalArgumentException("GenHom(): hmap  must not be null.");
		
		Map<G,Variable> varMap = new HashMap<G,Variable>();

		for (G v: toInts.keySet()){
			varMap.put(v, new NamedVariable<String>(v.toString(), toInts.get(v)));
		}

		TreeCreator<BiSymbol<G, Variable>,Tree<BiSymbol<G,Variable>>> tc 
		= new TreeCreator<BiSymbol<G,Variable>,Tree<BiSymbol<G,Variable>>>() {

			@Override
			public Tree<BiSymbol<G,Variable>> makeTree(BiSymbol<G,Variable> leaf) {
				return TreeFactory.getTreeFactory().makeTreeFromSymbol(leaf);
			}
			@Override
			public Tree<BiSymbol<G,Variable>> makeTree(BiSymbol<G,Variable> root,
					List<Tree<BiSymbol<G,Variable>>> subtrees) {
				return TreeFactory.getTreeFactory().makeTreeFromSymbol(root,subtrees);
			}

		};

		for (F symbol: hmap.keySet()){

			Tree<BiSymbol<G,Variable>> w 
			= VarTreeOps.<G,Variable,Tree<BiSymbol<G,Variable>>>
			makeTreeToBiTree(hmap.get(symbol),varMap,tc);

			hom.put(symbol,w); 
		}
	} 



	/* section: applying a homomorphism on a tree */

	/**
	 * Applies the homomorphism to a given tree. <br>
	 * This is done by applying {@link HomOps#apply}. 
	 * 
	 * @param startTree the tree on which the homomorphism shall be applied
	 * @return the tree of the destination alphabet which is gained by applying the homomorphism on the 
	 * given tree
	 */
	public Tree<G> apply(Tree<F> startTree) {	
		return HomOps.apply(this, startTree, new StdTreeCreator<G>());
	}


	/* section: applying a homomorphism in a tree automaton */

	/**
	 * Given a tree automaton, this method creates the tree automaton that generates the language, 
	 * which is gained by applying the homomorphism on each tree of the language of the given automaton. <br>
	 * This method can only be applied, if the homomorphism is linear! <br>
	 * This is done by applying {@link HomOps#applyOnAutomaton}. 
	 * 
	 * 
	 * @param <Q> state type of the given finite tree automaton
	 * @param <R> rule type of the given finite tree automaton
	 * @param ta finite tree automaton which gives the language, on which the homomorphism is to be applied
	 * @return new tree automaton which describes all trees gained by applying the homomorphism 
	 * on all trees given by the given finite tree automaton
	 * 
	 */
	public <Q extends State, R extends FTARule<F,Q>> GenFTA<G,NamedState<? extends Object>> applyOnAutomaton(AbstractModFTA<F,Q,R> ta){

		Converter<Q,NamedState<? extends Object>> c = new Converter<Q,NamedState<? extends Object>>() {
			@Override
			public NamedState<? extends Object> convert(Q a) {
				return StateFactory.getStateFactory().makeState(a);
			}
		};

		Converter<Pair<R,List<Integer>>,NamedState<? extends Object>> c2 = new Converter<Pair<R,List<Integer>>,NamedState<? extends Object>>() {
			@Override
			public NamedState<? extends Object> convert(Pair<R, List<Integer>> a) {
				return StateFactory.getStateFactory().makeState(a);
			}
		};		

		return HomOps.<F,G,Variable,Q,
		NamedState<? extends Object>,
		R,
		GenFTARule<G,NamedState<? extends Object>>,
		GenFTA<G,NamedState<? extends Object>>>
		applyOnAutomaton(this, ta, c, c2, new GenFTACreator<G,NamedState<? extends Object>>());

	}



	/* section: applying an inverse homomorphism */

	/**
	 * Given a finite tree automaton, this method returns a finite tree automaton
	 * whose language is mapped by the homomorphism to the language of the given automaton. <br>
	 * This is done by applying {@link HomOps#applyInverseOnAutomaton}. 
	 * 
	 * @param <Q> type of states of the input automaton
	 * @param ta finite tree automaton that represents the language which shall be regarded as  
	 * the image of the homomorphism. 
	 * @return finite tree automaton whose language is mapped by the homomorphism 
	 * to the language of the given automaton
	 */
	public <Q extends State> GenFTA<F,NamedState<? extends Object>> applyInverseOnAutomaton(AbstractModFTA<G,Q,? extends FTARule<G,Q>> ta){
		NamedState<? extends Object> s = StateFactory.getStateFactory().makeState();

		Converter<Q,NamedState<? extends Object>> c = new Converter<Q,NamedState<? extends Object>>() {
			@Override
			public NamedState<? extends Object> convert(Q a) {
				return StateFactory.getStateFactory().makeState(a);
			}
		};


		TreeCreator<BiSymbol<G,Q>,Tree<BiSymbol<G,Q>>> tc
		= new TreeCreator<BiSymbol<G,Q>,Tree<BiSymbol<G,Q>>>(){

			@Override
			public Tree<BiSymbol<G, Q>> makeTree(
					BiSymbol<G, Q> symbol,
					List<Tree<BiSymbol<G, Q>>> subTrees) {
				return TreeFactory.getTreeFactory().makeTreeFromSymbol(symbol,subTrees);
			}

			@Override
			public Tree<BiSymbol<G, Q>> makeTree(
					BiSymbol<G, Q> symbol) {
				return TreeFactory.getTreeFactory().makeTreeFromSymbol(symbol);
			}


		};

		return HomOps.<F,G, 
		Variable,
		Tree<G>,
		Q,						
		Tree<BiSymbol<G,Q>>, 
		NamedState<? extends Object>,
		GenFTARule<F,NamedState<? extends Object>>, 
		GenFTA<F,NamedState<? extends Object>>>
		applyInverseOnAutomaton(this, ta, s, c, new StdTreeCreator<G>(), 
				new GenFTACreator<F,NamedState<? extends Object>>(), tc);
	}


	/* section: properties of homomorphisms*/

	/**
	 * Returns whether the homomorphism is linear. <br>
	 * A homomorphism is called linear if in each tree each variable occurs at most once.<br>
	 * This is done by applying {@link HomOps#isLinear}.
	 * 
	 * @return true if and only if the homomorphism is linear, 
	 * i.e. in each tree each variable occurs at most once
	 */
	public boolean isLinear(){
		return HomOps.isLinear(this);
	}


	/**
	 * Returns whether the homomorphism is epsilon free. <br>
	 * A homomorphism is called epsilon free if no symbol is mapped just to a variable.<br>
	 * This is done by applying {@link HomOps#isEpsilonFree}.
	 * 
	 * @return true if and only if the homomorphism is epsilon free, 
	 * i.e. no symbol is mapped just to a variable
	 */
	public boolean isEpsilonFree(){
		return HomOps.isEpsilonFree(this);
	}


	/**
	 * Returns whether the homomorphism is symbol to symbol.<br>
	 * A homomorphism is called symbol to symbol if for each symbol the height of the 
	 * image of this symbol is 1. <br> 
	 * Note: A symbolToSymbol-Homomorphism can change the label of the input symbol, 
	 * possibly erase some subtrees and modify the order of the 
	 * This is done by applying {@link HomOps#isSymbolToSymbol}.
	 * 
	 * @return true if and only if the homomorphism is symbol to symbol, 
	 * i.e. for each symbol the height of the image of this symbol is 1.
	 */
	public boolean isSymbolToSymbol(){
		return HomOps.isSymbolToSymbol(this);
	}


	/**
	 * Returns whether the homomorphism is complete. <br>
	 * A homomorphism is called complete if for each symbol with arity n, 
	 * the image of f contains all variables from 0 to n-1. <br>
	 * This is done by applying {@link HomOps#isComplete}.
	 * 
	 * @return true if and only if the homomorphism is complete, 
	 * i.e. for each symbol with arity n the image of f contains all variables from 0 to n-1.
	 */
	public boolean isComplete(){
		return HomOps.isComplete(this);
	}


	/**
	 * Returns whether this homomorphism is delabeling. <br>
	 * A homomorphism is called delabeling if it is complete, linear and symbol to symbol. <br>  
	 * Note: A delabeling homomorphism only changes the label of the input symbol and
	 * possibly the order of the subtrees.<br>
	 * This is done by applying {@link HomOps#isDelabeling}.
	 * 
	 * @return true if and only if the homomorphism is delableing,
	 * i.e. it is complete, linear and symbol to symbol.
	 * 
	 */
	public boolean isDelabeling(){
		return HomOps.isDelabeling(this);
	}


	/**
	 * Returns whether a homomorphism is alphabetic. <br>
	 * A homomorphism is called alphabetic if for each symbol f the image of f is of the form
	 * g(x_0, ...x_{n-1}) where g is a symbol of the destination alphabet.<br>
	 * This is done by applying {@link HomOps#isAlphabetic}.
	 * 
	 * @return true if and only if the homomorphism is alphabetic,
	 * i.e. for each symbol f the image of f is of the form g(x_0, ...x_{n-1}) 
	 * where g is a symbol of the destination alphabet
	 */
	public boolean isAlphabetic(){
		return HomOps.isAlphabetic(this);
	}


	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString(){
		String res = "Homomorphismn: \n";
		for (F symbol: hom.keySet()){
			res += symbol.toString() + " -> " + hom.get(symbol).toString() + "\n";
		}
		return res;
	}


}
