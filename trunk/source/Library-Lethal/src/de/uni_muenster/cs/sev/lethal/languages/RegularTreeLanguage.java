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
package de.uni_muenster.cs.sev.lethal.languages;

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_muenster.cs.sev.lethal.grammars.RTGRule;
import de.uni_muenster.cs.sev.lethal.hom.Hom;
import de.uni_muenster.cs.sev.lethal.hom.HomOps;
import de.uni_muenster.cs.sev.lethal.states.NumberedState;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.Variable;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.tree.standard.StdTreeCreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTACreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAOps;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAProperties;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTACreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTAOps;
import de.uni_muenster.cs.sev.lethal.utils.Converter;
import de.uni_muenster.cs.sev.lethal.utils.IdentityConverter;
import de.uni_muenster.cs.sev.lethal.utils.Pair;

/**
 * Represents a regular tree language. For internal description a finite tree automaton is used, laying
 * stress on its structure, more than on the names of the states etc.<br>
 * As a consequence, the returned finite tree automaton is only a renamed version of
 * the finite tree automaton out of which a tree language was constructed - and these names are as
 * simple as possible. 
 * 
 * @param <F> type of symbols occurring in trees, which this class can deal with
 * @author Dorothea, Irene, Martin
 */
public class RegularTreeLanguage<F extends RankedSymbol> implements Iterable<Tree<F>> {

	/**
	 * Factory for numbered states - states are identified with objects of type T and
	 * numbered consecutively. To make the conversion injective, the mapping between
	 * identification object and state is stored - if an object is supplied,
	 * out of which a state was already produced, it simply is restored from a cache.
	 * 
	 * @param <T> type of objects to identify newly created states
	 */
	protected static class NumberedStateConstructor<T> implements Converter<T,NumberedState> {

		/**
		 * Stores the mapping between identification object and state.
		 */
		private HashMap<T,NumberedState> cache = new HashMap<T,NumberedState>();

		/**
		 * Stores how many distinct objects have already been identified with new states.
		 */
		private int count=0;
		
		/**
		 * @see de.uni_muenster.cs.sev.lethal.utils.Converter#convert(java.lang.Object)
		 */
		@Override
		public NumberedState convert(T a) {
			if (cache.containsKey(a))
				return cache.get(a);
			else {
				NumberedState newState = new NumberedState(count) {
					@Override
					public String toString() {
						return "q"+super.toString();
					}
				};
				cache.put(a,newState);
				count++;
				return newState;
			}
		}

		/**
		 * Returns all states which have been created.
		 * @return all states which have been created
		 */
		Collection<NumberedState> getStates() {
			return cache.values();
		}

		void reset() {
			cache.clear();
			count=0;
		}
	}


	
	/**
	 * Finite tree automaton which characterizes this regular tree language. <br>
	 * Invariant: States are always numbered continuously from 0 to n-1, where
	 * n is their total number.
	 */
	private GenFTA<F,NumberedState> underlyingFTA;

	
	/**
	 * Creates a new regular tree language out of an arbitrary finite tree automaton.
	 * 
	 * @param <Q> state type of the given finite tree automaton
	 * @param fta finite tree automaton which describes the language to be created
	 */
	public <Q extends State> RegularTreeLanguage(FTA<F,Q, ? extends FTARule<F,Q>> fta) {
		if (fta == null) throw new IllegalArgumentException("RegularTreeLanguage(): fta must not be null.");
		underlyingFTA = translateFTA(FTAOps.reduceFull(translateFTA(fta),new GenFTACreator<F,NumberedState>()));
	}

	
	/**
	 * Creates a new regular tree language out of the components of a regular tree grammar.
	 * 
	 * @param <Q> type of non-terminals occurring in the given regular tree grammar
	 * @param grammarStart start symbols of grammar to be converted into a finite tree automaton
	 * @param grammarRules rules of grammar to be converted into a finite tree automaton
	 * @see FTACreator#makeFTAFromGrammar
	 */
	public <Q extends State> RegularTreeLanguage(Collection<Q> grammarStart, Collection<? extends RTGRule<F,Q>> grammarRules) {
		if (grammarStart == null) throw new IllegalArgumentException("RegularTreeLanguage(): grammarStart must not be null.");
		if (grammarRules == null) throw new IllegalArgumentException("RegularTreeLanguage(): grammarRules must not be null.");
		Pair<Collection<FTARule<F, NumberedState>>, Collection<NumberedState>> convFTA = FTACreator.makeFTAFromGrammar(grammarStart, grammarRules, new NumberedStateConstructor<Object>());
		underlyingFTA = new GenFTA<F,NumberedState>(convFTA.getFirst(), convFTA.getSecond());
	}

	
	/**
	 * Creates a new regular tree language which consists of all trees over the given alphabet.
	 * 
	 * @param alphabet alphabet generating the regular tree language of all trees, which is to be created
	 */
	public RegularTreeLanguage(Collection<F> alphabet) {
		underlyingFTA = FTAOps.computeAlphabetFTA(alphabet, new NumberedState(0), new GenFTACreator<F,NumberedState>());
	}

	
	/**
	 * Creates an empty regular tree language.
	 */
	protected RegularTreeLanguage() {
		underlyingFTA = new GenFTA<F,NumberedState>();
	}

	
	/**
	 * Creates a new regular tree language out of a given one by copying its description.
	 * 
	 * @param lang regular tree language to be copied
	 * @return copied regular tree language
	 */
	public RegularTreeLanguage<F> copy(RegularTreeLanguage<F> lang) {
		return new RegularTreeLanguage<F>(lang.underlyingFTA);
	}


	/**
	 * Translates a given finite tree automaton to an internal representation, where the states are
	 * numbered consecutively somehow, but consistently.
	 * 
	 * @param <Q> state type of the finite tree automaton to be translated
	 * @param fta finite tree automaton to be translated
	 * @return internal representation, where the states are
	 * numbered consecutively somehow, but consistently.
	 */
	protected <Q extends State> GenFTA<F,NumberedState> translateFTA(FTA<F,Q,? extends FTARule<F,Q>> fta) {
		NumberedStateConstructor<Q> sc = new NumberedStateConstructor<Q>();
		IdentityConverter<F> ac = new IdentityConverter<F>();
		GenFTACreator<F,NumberedState> fc = new GenFTACreator<F, NumberedState>();
		return FTAOps.ftaConverter(fta, sc, ac, fc);
	}


	/**
	 * Adds a whole regular tree language to this language.
	 * @param lang language to be added
	 */
	public void addTrees(RegularTreeLanguage<F> lang) {
		IdentityConverter<F> identConv = new IdentityConverter<F>();
		Converter<NumberedState,NumberedState> c13 = new Converter<NumberedState,NumberedState>() {

			@Override
			public NumberedState convert(NumberedState a) {
				return a;
			}
		};

		Converter<NumberedState,NumberedState> c23 = new Converter<NumberedState,NumberedState>() {
			final int offset = underlyingFTA.getStates().size();
			@Override
			public NumberedState convert(NumberedState a) {
				return new NumberedState(a.getIndex()+offset);
			}

		};

		underlyingFTA = FTAOps.union(underlyingFTA, lang.underlyingFTA, c13, c23, identConv, identConv, new GenFTACreator<F,NumberedState>());
	}

	
	/**
	 * Adds a tree to this language.
	 * 
	 * @param t tree to be added
	 */
	public void addTree(Tree<F> t) {
		GenFTA<F,NumberedState> A_t = FTAOps.computeSingletonFTA(t, new GenFTACreator<F,NumberedState>(),new NumberedStateConstructor<Object>());
		RegularTreeLanguage<F> L_t = new RegularTreeLanguage<F>();
		L_t.underlyingFTA = A_t;
		addTrees(L_t);
	}

	
	/**
	 * Intersects this language with a given regular tree language.
	 * 
	 * @param lang language to be intersected with this regular tree language
	 */
	public void retainAllTrees(RegularTreeLanguage<F> lang) {
		NumberedStateConstructor<Pair<NumberedState,NumberedState>> pc = new NumberedStateConstructor<Pair<NumberedState,NumberedState>>();
		GenFTACreator<F,NumberedState> fc = new GenFTACreator<F,NumberedState>();
		underlyingFTA = translateFTA(FTAOps.reduceBottomUp(FTAOps.intersectionBU(underlyingFTA, lang.underlyingFTA, pc, fc),fc));
	}

	
	/**
	 * Returns the complement of this regular tree language.
	 * @return a regular tree language over the same alphabet which contains a tree 
	 * if and only if it is not contained in this language
	 */
	public RegularTreeLanguage<F> complement() {
		GenFTACreator<F,NumberedState> fc = new GenFTACreator<F,NumberedState>();
		NumberedStateConstructor<Set<NumberedState>> setToState = new NumberedStateConstructor<Set<NumberedState>>();
		GenFTA<F,NumberedState> compFTA = FTAOps.complement(underlyingFTA, setToState, fc);
		return new RegularTreeLanguage<F>(FTAOps.reduceFull(compFTA, fc));
	}

	
	/**
	 * Removes a whole regular tree language from this language.
	 * @param lang language to be removed
	 */
	public void removeTrees(RegularTreeLanguage<F> lang) {
		GenFTACreator<F,NumberedState> fc = new GenFTACreator<F,NumberedState>();
		NumberedStateConstructor<Set<NumberedState>> setToState = new NumberedStateConstructor<Set<NumberedState>>();
		NumberedStateConstructor<Pair<NumberedState,NumberedState>> pairToState = new NumberedStateConstructor<Pair<NumberedState,NumberedState>>();
		GenFTA<F,NumberedState> newFTA = FTAOps.difference(underlyingFTA, lang.underlyingFTA, setToState, fc, pairToState, fc);
		GenFTA<F,NumberedState> newFTARed = FTAOps.reduceFull(newFTA, fc);
		underlyingFTA = newFTARed;
	}


	/**
	 * Removes a tree from this language, if it is contained.
	 * @param t tree to be removed
	 */
	public void removeTree(Tree<F> t) {
		if (contains(t)) {
			GenFTACreator<F,NumberedState> fc = new GenFTACreator<F,NumberedState>();
			NumberedStateConstructor<Object> treeToState = new NumberedStateConstructor<Object>();
			GenFTA<F,NumberedState> A_t = FTAOps.computeSingletonFTA(t, fc, treeToState);
			RegularTreeLanguage<F> L_t = new RegularTreeLanguage<F>();
			L_t.underlyingFTA = A_t;
			removeTrees(L_t);
		}
	}


	/**
	 * Constructs the regular tree language containing all trees of this regular tree language 
	 * which do not exceed the specified height.
	 * 
	 * @param maxHeight maximum height of the trees contained in the language to be returned
	 * @return the regular tree language containing all trees of this regular tree language 
	 * which are not higher than specified
	 */
	public RegularTreeLanguage<F> restrictToMaxHeight(int maxHeight) {
		return new RegularTreeLanguage<F>(FTAOps.restrictToMaxHeight(underlyingFTA, 
				maxHeight,
				new GenFTACreator<F,NumberedState>(), 
				new NumberedStateConstructor<Pair<NumberedState,Integer>>()));
		
	}


	/**
	 * Returns a tree contained in this language, if this language is not empty. Otherwise,
	 * null is returned
	 * @return a tree contained in this language, if this language is not empty, null otherwise
	 **/
	public Tree<F> constructWitness() {
		return GenFTAOps.constructTreeFrom(underlyingFTA);
	}


	/**
	 * Decides whether a given tree is contained in this regular tree language
	 * @param t tree to be checked
	 * @return true if the given tree is contained in this regular tree language,
	 * false otherwise
	 */
	public boolean contains(Tree<F> t) {
		return FTAProperties.decide(underlyingFTA, t);
	}

	
	/**
	 * Returns whether this language is empty.
	 * @return true if this language is empty, false otherwise
	 */
	public boolean isEmpty() {
		return FTAProperties.emptyLanguage(underlyingFTA);
	}

	
	/**
	 * Returns whether this language is finite.
	 * @return true if this language is finite, false otherwise
	 */
	public boolean isFinite() {
		return FTAProperties.finiteLanguage(underlyingFTA);
	}

	
	/**
	 * Checks whether this regular tree language is the same as the given one.
	 * @param lang regular tree language to be compared with this regular tree language
	 * @return true, if this regular tree language is the same as the given one,
	 * false otherwise
	 */
	public boolean sameAs(RegularTreeLanguage<F> lang) {
		return FTAProperties.sameLanguage(getFTA(), lang.getFTA());
	}

	
	/**
	 * Checks whether this regular tree language is a subset of the given one.
	 * @param lang regular tree language to be compared with this regular tree language
	 * @return true, if this regular tree language is a subset of the given one,
	 * false otherwise
	 */
	public boolean subsetOf(RegularTreeLanguage<F> lang) {
		return FTAProperties.subsetLanguage(getFTA(), lang.getFTA());
	}

	
	/**
	 * Returns the regular tree language obtained by substituting several regular tree languages into
	 * a given tree.
	 * @param <F> symbol type of the incoming tree and languages
	 * @param <G> type of leaves to be substituted
	 * @param tree tree in which the given languages are to be substituted
	 * @param languages regular tree languages to be substituted into the given tree
	 * @return the regular tree language obtained by substituting several regular tree languages into
	 * a given tree.
	 * @see FTAOps#substitute
	 */
	public static <F extends RankedSymbol, G extends F> RegularTreeLanguage<F> substitute(Tree<F> tree, Map<G,RegularTreeLanguage<F>> languages) {
		Map<G, GenFTA<F,NumberedState>> ftaLang = new HashMap<G, GenFTA<F,NumberedState>>();
		for (G g: languages.keySet())
			ftaLang.put(g,languages.get(g).underlyingFTA);
		GenFTACreator<F,NumberedState> fc = new GenFTACreator<F,NumberedState>();
		NumberedStateConstructor<Object> sb = new NumberedStateConstructor<Object>();
		GenFTA<F,NumberedState> retFTA = FTAOps.substitute(tree, ftaLang, sb, sb, sb, fc);
		RegularTreeLanguage<F> ret = new RegularTreeLanguage<F>();
		ret.underlyingFTA = retFTA;
		return ret;
	}

	
	/**
	 * Applies a linear tree homomorphism to this regular tree language. The result is
	 * the image of this regular tree language under the given homomorphism.
	 * @param <G> type of destination alphabet of the given homomorphism
	 * @param h homomorphism to be applied
	 * @return the image of the given regular tree language under the given homomorphism
	 * @see HomOps#applyOnAutomaton(Hom, FTA, Converter, Converter, de.uni_muenster.cs.sev.lethal.treeautomata.common.FTACreator)
	 */
	public  
	<G extends RankedSymbol> 
	RegularTreeLanguage<G> applyHom(Hom<F,G,? extends Variable> h) {
		NumberedStateConstructor<Object> sb = new NumberedStateConstructor<Object>();
		return new RegularTreeLanguage<G>(HomOps.applyOnAutomaton(h, getFTA(), sb, sb, new GenFTACreator<G,NumberedState>()));
	}

	
	/**
	 * Given a tree homomorphism h, computes the preimage of
	 * this regular tree language under h, i.e. all trees t with h(t) in L.
	 * @param <E> type of source alphabet of the given homomorphism
	 * @param h homomorphism under which the preimage is to be computed
	 * @return the preimage of this regular tree language under the given homomorphism
	 */
	public
	<E extends RankedSymbol>
	RegularTreeLanguage<E> applyHomInv(Hom<E,F,? extends Variable> h) {
		NumberedState s = new NumberedState(getFTA().getStates().size());
		Converter<NumberedState,NumberedState> c = new IdentityConverter<NumberedState>();
		StdTreeCreator<F> tc = new StdTreeCreator<F>();
		GenFTACreator<E,NumberedState> fc = new GenFTACreator<E,NumberedState>();
		StdTreeCreator<BiSymbol<F,NumberedState>> btc = new StdTreeCreator<BiSymbol<F,NumberedState>>();
		return new RegularTreeLanguage<E>(HomOps.applyInverseOnAutomaton(h, underlyingFTA, s, c, tc, fc, btc));
	}


	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "Underlying fta has "+underlyingFTA.getStates().size()+" states and "+underlyingFTA.getRules().size()+ " rules.";
	}


	/**
	 * Returns the underlying finite tree automaton.
	 * @return the finite tree automaton which describes this language
	 */
	public GenFTA<F,? extends State> getFTA() {
		return underlyingFTA;
	}

	
	/**
	 * @see java.lang.Iterable#iterator()
	 */
	@Override
	public Iterator<Tree<F>> iterator() {
		return new Iterator<Tree<F>>() {
			final RegularTreeLanguage<F> L = copy(RegularTreeLanguage.this);
			@Override
			public boolean hasNext() {
				return !L.isEmpty();
			}

			@Override
			public Tree<F> next() {
				Tree<F> next = L.constructWitness();
				L.removeTree(next);
				return next;
			}

			@Override
			public void remove() {
				throw new UnsupportedOperationException("Deletion of elements not allowed!");
			}

		};
	}
}
