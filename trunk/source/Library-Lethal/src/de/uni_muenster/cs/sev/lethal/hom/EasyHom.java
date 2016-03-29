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

import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.Variable;
import de.uni_muenster.cs.sev.lethal.symbol.standard.InnerSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.standard.NamedVariable;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.tree.common.TreeCreator;
import de.uni_muenster.cs.sev.lethal.tree.common.VarTreeOps;
import de.uni_muenster.cs.sev.lethal.tree.standard.StdTreeCreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTACreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.easy.EasyFTARule;
import de.uni_muenster.cs.sev.lethal.utils.CachedConverter;
import de.uni_muenster.cs.sev.lethal.utils.Converter;
import de.uni_muenster.cs.sev.lethal.utils.Pair;


/**
 * Represents a homomorphism between two alphabets without generic types. 
 * 
 * @see Hom
 * @see HomOps
 * 
 * @author Dorothea, Irene, Martin
 */
public class EasyHom extends GenHom<RankedSymbol,RankedSymbol>{


	/**
	 * Creates an empty homomorphism.
	 */
	public EasyHom() {
		super();
	}

	
	/**
	 * Creates a homomorphism out of a given map that specifies the homomorphism.
	 * 
	 * @param h map which specifies the homomorphism 
	 */
	public EasyHom(Map<RankedSymbol,Tree<? extends BiSymbol<RankedSymbol,Variable>>> h) {
		super(h);
	}

	
	/**
	 * Creates a homomorphism out of a given map that specifies the homomorphism and
	 * continues it with the identity on the given alphabet.
	 * 
	 * @param hmap map which specifies the homomorphism 
	 * @param alphabet what shall be added source alphabet of the homomorphism
	 */
	public EasyHom(Map<RankedSymbol,Tree<? extends BiSymbol<RankedSymbol,Variable>>> hmap, Collection<RankedSymbol> alphabet) {
		super(hmap);
		if (alphabet == null) throw new IllegalArgumentException("EasyHom(): alphabet must not be null.");
		if (hmap == null) throw new IllegalArgumentException("EasyHom(): hmap must not be null.");
		continueOn(alphabet);
	}


	/**
	 * Creates a homomorphism out of a map which maps each symbol of the source alphabet 
	 * to a tree and another map which states, which constants in the trees shall
	 * be replaced by which homomorphism variables (using the number of the homomorphism
	 * variable). <br> 
	 * 
	 * The keys of the map must be symbols with arity 0. 
	 * 
	 * @param toInts map which maps some occurring constants (symbols with arity 0) 
	 * to Integers which are needed to define the homomorphism
	 * @param hmap Map which specifies the homomorphism except the ordering of the variables
	 * 
	 */
	public EasyHom(Map<RankedSymbol,Integer> toInts, Map<RankedSymbol,Tree<RankedSymbol>> hmap) {
		if (toInts == null) throw new IllegalArgumentException("EasyHom(): toInts must not be null.");
		if (hmap == null)  throw new IllegalArgumentException("EasyHom(): hmap must not be null.");
		
		generateHom(toInts,hmap);
	} 

	
	/**
	 * Creates a homomorphism out of a map which maps each symbol of the source alphabet 
	 * to a tree and another map that specifies which constants in the trees are to be
	 * be replaced by which homomorphism variables (using the number of the homomorphism
	 * variable) and continues the homomorphism with the identity on the given alphabet.<br>
	 * 
	 * The keys of the map must be symbols with arity 0. 
	 * 
	 * @param toInts map which maps some occurring constants (symbols with arity 0) 
	 * to Integers which are needed to define the homomorphism
	 * @param h Map which specifies the homomorphism except the ordering of the variables
	 * @param alphabet what shall be added source alphabet of the homomorphism
	 */
	public EasyHom(Map<RankedSymbol,Integer> toInts, Map<RankedSymbol,Tree<RankedSymbol>> h, Collection<RankedSymbol> alphabet) {
		generateHom(toInts,h);
		continueOn(alphabet);
	} 


	/**
	 * Continues the homomorphism with the identity on the given alphabet.
	 * 
	 * @param alphabet what shall be added source alphabet of the homomorphism
	 */
	private void continueOn(Collection<RankedSymbol> alphabet) {
		for (RankedSymbol f: alphabet){
			if (!hom.containsKey(f)){
				hom.put(f, TreeFactory.getTreeFactory().makeTreeFromSymbol(
						new InnerSymbol<RankedSymbol,Variable>(f)));
			}
		}
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
	 * @param h Map which specifies the homomorphism except the ordering of the variables
	 */
	private void generateHom(Map<RankedSymbol,Integer> toInts, Map<RankedSymbol,Tree<RankedSymbol>> h){
		Map<RankedSymbol,Variable> varMap = new HashMap<RankedSymbol,Variable>();

		for (RankedSymbol v: toInts.keySet()){
			varMap.put(v, new NamedVariable<String>(v.toString(), toInts.get(v)));
		}

		TreeCreator<BiSymbol<RankedSymbol, Variable>,Tree<BiSymbol<RankedSymbol,Variable>>> tc 
		= new TreeCreator<BiSymbol<RankedSymbol,Variable>,Tree<BiSymbol<RankedSymbol,Variable>>>() {

			@Override
			public Tree<BiSymbol<RankedSymbol,Variable>> makeTree(BiSymbol<RankedSymbol,Variable> leaf) {
				return TreeFactory.getTreeFactory().makeTreeFromSymbol(leaf);
			}
			@Override
			public Tree<BiSymbol<RankedSymbol,Variable>> makeTree(BiSymbol<RankedSymbol,Variable> root,
					List<Tree<BiSymbol<RankedSymbol,Variable>>> subtrees) {
				return TreeFactory.getTreeFactory().makeTreeFromSymbol(root,subtrees);
			}

		};

		hom = new HashMap<RankedSymbol,Tree<? extends BiSymbol<RankedSymbol,Variable>>>();
		for (RankedSymbol symbol: h.keySet()){

			Tree<BiSymbol<RankedSymbol,Variable>> w 
			= VarTreeOps.<RankedSymbol,Variable,Tree<BiSymbol<RankedSymbol,Variable>>>
			makeTreeToBiTree(h.get(symbol),varMap,tc);

			hom.put(symbol,w); 
		}
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.hom.Hom#containsSrcSymbol(de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol)
	 */
	@Override
	public boolean containsSrcSymbol(RankedSymbol symbol) {
		return hom.containsKey(symbol);
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.hom.Hom#getSrcAlphabet()
	 */
	@Override
	public Collection<RankedSymbol> getSrcAlphabet() {
		return hom.keySet();
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.hom.Hom#imageOf(de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol)
	 */
	@Override
	public Tree<? extends BiSymbol<RankedSymbol,Variable>> imageOf(RankedSymbol f) {
		return hom.get(f);
	}



	/* section: applying a homomorphism in a tree automaton */

	/**
	 * Given a tree automaton, this method makes the tree automaton that generates the language, 
	 * which is gained by applying the homomorphism on each tree of the language of the given automaton. <br>
	 * This method can only be applied, if the homomorphism is linear! <br>
	 * This is done by applying {@link HomOps#applyOnAutomaton}. 
	 *  
	 * @param ta finite tree automaton which gives the language, on which the homomorphism is to be applied
	 * @return new tree automaton which describes all trees gained by applying the homomorphism 
	 * on all trees given by the given finite tree automaton
	 */
	public EasyFTA applyOnAutomaton(EasyFTA ta) {
		Converter<State,State> c = new Converter<State,State>() {
			@Override
			public State convert(State a) {
				return a;
			}
		};

		Converter<Pair<EasyFTARule,List<Integer>>,State> c20 = new CachedConverter<Pair<EasyFTARule,List<Integer>>, State>() {

			@Override
			public State uniqueConvert(Pair<EasyFTARule, List<Integer>> a) {
				return StateFactory.getStateFactory().makeState();
			}
			
		};
		
//		Converter<Pair<EasyFTARule,List<Integer>>,State> c2 = new Converter<Pair<EasyFTARule,List<Integer>>,State>() {
//			@Override
//			public State convert(Pair<EasyFTARule, List<Integer>> a) {
//				return StateFactory.getStateFactory().makeState(a);
//			}
//		};

		return HomOps.applyOnAutomaton(this, ta, c, c20, new EasyFTACreator());
	}

	/* section: applying an inverse homomorphism */

	/**
	 * Given a finite tree automaton, this method returns a finite tree automaton
	 * whose language is mapped by the homomorphism to the language of the given automaton. <br>
	 * This is done by applying {@link HomOps#applyInverseOnAutomaton}. 
	 * 
	 * @param ta finite tree automaton that represents the language which shall be regarded as  
	 * the image of the homomorphism. 
	 * @return finite tree automaton whose language is mapped by the homomorphism 
	 * to the language of the given automaton
	 */
	public EasyFTA applyInverseOnAutomaton(EasyFTA ta){
		State s = StateFactory.getStateFactory().makeState();
		Converter<State,State> c = new Converter<State,State>() {
			@Override
			public State convert(State a) {
				return a;
			}
		};

		TreeCreator<BiSymbol<RankedSymbol,State>,Tree<BiSymbol<RankedSymbol,State>>> tc
		= new TreeCreator<BiSymbol<RankedSymbol,State>,Tree<BiSymbol<RankedSymbol,State>>>(){

			@Override
			public Tree<BiSymbol<RankedSymbol,State>> makeTree(
					BiSymbol<RankedSymbol,State> symbol,
					List<Tree<BiSymbol<RankedSymbol,State>>> subTrees) {
				return TreeFactory.getTreeFactory().makeTreeFromSymbol(symbol,subTrees);
			}

			@Override
			public Tree<BiSymbol<RankedSymbol,State>> makeTree(
					BiSymbol<RankedSymbol,State> symbol) {
				return TreeFactory.getTreeFactory().makeTreeFromSymbol(symbol);
			}


		};
		return HomOps.applyInverseOnAutomaton(this, ta, s, c, new StdTreeCreator<RankedSymbol>(), new EasyFTACreator(), tc);
	}

}
