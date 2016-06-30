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
package de.uni_muenster.cs.sev.lethal.treeautomata.easy;


import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_muenster.cs.sev.lethal.factories.StateFactory;
import de.uni_muenster.cs.sev.lethal.states.NamedState;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.Symbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.tree.standard.StdTreeCreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTACreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAOps;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;
import de.uni_muenster.cs.sev.lethal.utils.Converter;
import de.uni_muenster.cs.sev.lethal.utils.IdentityConverter;
import de.uni_muenster.cs.sev.lethal.utils.Pair;


/**
 * The standard implementation for operations on finite tree automata without generic types.
 * 
 * @see FTAOps
 * 
 * @author Dorothea, Irene, Martin
 */
public class EasyFTAOps {


	/**
	 * Constructs a state out of any object, using a StateFactory.<br>
	 * It is used for the standard implementation of operations on tree automata
	 * to convert an object into a new state. 
	 * 
	 * @param <T> type of object to be converted
	 * @see Converter
	 * @see StateFactory
	 * @see EasyFTAOps
	 */
	protected static class StdStateBuilder<T> implements Converter<T,State> {

		/**
		 * Converts any object into a state.
		 * 
		 * @see de.uni_muenster.cs.sev.lethal.utils.Converter#convert(java.lang.Object)
		 * @see StateFactory#makeState(Object)
		 */
		@Override
		public NamedState<Object> convert(Object a) {
			return StateFactory.getStateFactory().makeState(a);
		}

	}


	/**
	 * Used to have the right converter in the substitute method. 
	 * Solution for the problem that if StdVarTree extends BiTree<I,L>,
	 * Converter<StdVarTree,State> needs not to extend Converter<BiTree<I,L>,State>.
	 * So the Converter<StdVarTree,State> implements this interface and can be used
	 * as Converter<BiTree<I,L>,State>.
	 * 
	 * @param <I> type of a symbol, for example ranked symbol
	 * @param <L> type of the other symbol, for example variable symbol
	 */
	protected interface BiTreeToStateConverter<I extends Symbol, L extends Symbol> extends Converter<Tree<BiSymbol<I,? extends L>>,State> { }



	/**
	 * Given a finite tree automaton, constructs an equivalent complete finite tree automaton.
	 * 
	 * @param fta finite tree automaton to be completed
	 * @return complete finite tree automaton equivalent to the given finite tree automaton
	 * 
	 * @see FTAOps#complete
	 */
	public static EasyFTA complete(FTA<RankedSymbol,State,? extends FTARule<RankedSymbol,State>> fta){
		State qbot = StateFactory.getStateFactory().makeState();
		EasyFTACreator fc = new EasyFTACreator();
		return FTAOps.complete(fta,qbot,fc);

	}


	/**
	 * Given a finite tree automaton A, constructs a tree automaton which accepts a tree if and only if
	 * A denies it with respect to the union of its alphabet and some given alphabet. <br>
	 * 
	 * @param fta finite tree automaton to be completed
	 * @param alphabet alphabet with respect to which the automaton shall be completed
	 * 
	 * @return complete finite tree automaton equivalent to the given finite tree automaton w.r.t. the given alphabet 
	 * 
	 * @see FTAOps#completeAlphabet(FTA, Collection, State, FTACreator)
	 */
	public static EasyFTA 	completeAlphabet(FTA<RankedSymbol,State,? extends FTARule<RankedSymbol,State>> fta, 
			Collection<RankedSymbol> alphabet) {
		State qbot = StateFactory.getStateFactory().makeState();
		EasyFTACreator fc = new EasyFTACreator();
		return FTAOps.completeAlphabet(fta, alphabet, qbot, fc);
	}


	/**
	 * Given a given finite tree automaton A, computes an equivalent deterministic 
	 * finite tree automaton.
	 * 
	 * @param fta automaton to be determinized
	 * 
	 * @return deterministic finite tree automaton equivalent to the given one
	 * 
	 * @see FTAOps#determinize
	 */
	public static EasyFTA determinize(FTA<RankedSymbol,State,? extends FTARule<RankedSymbol,State>> fta) {
		EasyFTACreator fc = new EasyFTACreator();
		StdStateBuilder<Set<State>> sc = new StdStateBuilder<Set<State>>(); 
		return FTAOps.determinize(fta, fc, sc);
	}


	/**
	 * Given a finite tree automaton A, constructs an equivalent reduced finite tree automaton.
	 * 
	 * @param fta finite tree automaton to be reduced
	 * @return reduced version of supplied finite tree automaton
	 * 
	 * @see FTAOps#reduceBottomUp
	 */
	public static EasyFTA reduceBottomUp(FTA<RankedSymbol,State,? extends FTARule<RankedSymbol,State>> fta) {
		EasyFTACreator fc = new EasyFTACreator();
		return FTAOps.reduceBottomUp(fta, fc);
	}


	/**
	 * Given a finite tree automaton A, constructs an equivalent finite tree automaton A', 
	 * which is top-down reduced.
	 * 
	 * @param fta finite tree automaton to be reduced 
	 * @return equivalent finite tree automaton which only contains states from which a 
	 * final state is reachable and contains only the rules in which merely these states occur.
	 * 
	 * @see FTAOps#reduceTopDown
	 */
	public static EasyFTA reduceTopDown(FTA<RankedSymbol,State,? extends FTARule<RankedSymbol,State>> fta) {
		EasyFTACreator fc = new EasyFTACreator();
		return FTAOps.reduceTopDown(fta, fc);
	}


	/**
	 * Given a finite tree automaton, constructs a finite tree automaton which is both top-down and
	 * bottom-up reduced. 
	 * 
	 * @param fta finite tree automaton to be reduced 
	 * @return fully reduced version of the given finite tree automaton, that means for every rule f(q1,...qn) - q there is a
	 * tree t, a configuration tree tc and a final state qf such that f(q1,...qn) is a subtree of tc, t can
	 * be reduced to tc and tc can be reduced to qf.
	 * 
	 * @see FTAOps#reduceFull
	 */
	public static EasyFTA reduceFull(FTA<RankedSymbol,State,? extends FTARule<RankedSymbol,State>> fta) {
		EasyFTACreator fc = new EasyFTACreator();
		return FTAOps.reduceFull(fta, fc);
	}


	/**
	 * Given a deterministic finite tree automaton, constructs an equivalent finite tree automaton 
	 * with an almost minimal number of states. 
	 * 
	 * @param fta  finite tree automaton to be minimized
	 * @return finite tree automaton with a minimal number of states which has the same
	 * language as the given one
	 * 
	 * @see FTAOps#minimize
	 */
	public static EasyFTA minimize(FTA<RankedSymbol,State,? extends FTARule<RankedSymbol,State>> fta) {
		StdStateBuilder<Set<State>> sc = new StdStateBuilder<Set<State>>(); 
		EasyFTACreator fc = new EasyFTACreator();
		State qbot = StateFactory.getStateFactory().makeState();
		while (fta.getStates().contains(qbot))
			qbot = StateFactory.getStateFactory().makeState();
		return FTAOps.minimize(fta, qbot, fc, sc, fc);
	}


	/**
	 * Given a finite tree automaton A, constructs a finite tree automaton 
	 * which accepts a tree over the alphabet of A if and only if A denies it.
	 * 
	 * @param fta finite tree automaton to be complemented
	 * @return complemented finite tree automaton
	 * 
	 * @see FTAOps#complement
	 */
	public static EasyFTA complement (FTA<RankedSymbol,State,? extends FTARule<RankedSymbol,State>> fta) {
		EasyFTACreator fc = new EasyFTACreator();
		StdStateBuilder<Set<State>> sc = new StdStateBuilder<Set<State>>(); 
		return FTAOps.complement(fta, sc, fc);
	}

	
	/**
	 * Given a finite tree automaton A, constructs a finite tree automaton which accepts a tree if and only if
	 * A denies it with respect to the union of its alphabet and some given alphabet.
	 * 
	 * @param fta automaton to be complemented
	 * @param alphabet alphabet to which the automaton is to be complemented
	 * 
	 * @return complemented finite tree automaton
	 * 
	 * @see FTAOps#complementAlphabet
	 */
	public static EasyFTA complementAlphabet (FTA<RankedSymbol,State, ? extends FTARule<RankedSymbol,State>> fta, Collection<RankedSymbol> alphabet) {
		
		EasyFTACreator fc = new EasyFTACreator();
		StdStateBuilder<Set<State>> sc = new StdStateBuilder<Set<State>>();
		return FTAOps.complementAlphabet(fta, alphabet, sc, fc);
	}


	/**
	 * Returns a finite tree automaton that recognizes exactly the union of the languages of the given finite 
	 * tree automata.<br>
	 * The resulting finite tree automaton is in general non-deterministic.<br>
	 * <br>
	 * This is realized by guaranteeing that the states of the finite tree automata are disjoint.
	 * (Embed them disjointly in new states.) Then construct a new finite tree automaton with 
	 * the union of states, union of final states and union of rules. 
	 * 
	 * @param fta1 the first finite tree automaton for the union
	 * @param fta2 the second finite tree automaton for the union
	 * 
	 * @return a finite tree automaton that recognizes exactly the union of the 
	 * languages of the given finite tree tree automata
	 * 
	 * @see FTAOps#union
	 */
	public static EasyFTA union (FTA<RankedSymbol,State,? extends FTARule<RankedSymbol,State>> fta1, 
			FTA<RankedSymbol,State,? extends FTARule<RankedSymbol,State>> fta2) {
		Converter<State,State> stateconv1 = new Converter<State,State>() {

			@Override
			public State convert(State a) {
				Pair<State,Integer> newname = new Pair<State,Integer>(a,1);
				return StateFactory.getStateFactory().makeState(newname);
			}

		};

		Converter<State,State> stateconv2 = new Converter<State,State>() {

			@Override
			public State convert(State a) {
				Pair<State,Integer> newname = new Pair<State,Integer>(a,2);
				return StateFactory.getStateFactory().makeState(newname);
			}

		};
		IdentityConverter<RankedSymbol> symbconv = new IdentityConverter<RankedSymbol>();
		EasyFTACreator fc = new EasyFTACreator();
		return FTAOps.union(fta1, fta2, stateconv1, stateconv2, symbconv, symbconv, fc);
	}


	/**
	 * Given two finite tree automata, constructs a finite tree automaton which accepts a tree 
	 * if and only if both automata accept it. The suffix "BU" stands for bottom-up reduction.<br>
	 * That means, the algorithm consists of a {@link FTAOps#intersectionWR product construction} with additional reduction, such
	 * that in the resulting automaton every state is reachable. 
	 * 
	 * @param fta1 first automaton
	 * @param fta2 second automaton
	 * @return an automaton which accepts a tree if and only if both A1 and A2 accept it.
	 * @see FTAOps#intersectionBU
	 */
	public static EasyFTA intersectionBU(FTA<RankedSymbol,State,? extends FTARule<RankedSymbol,State>> fta1, 
			FTA<RankedSymbol,State,? extends FTARule<RankedSymbol,State>> fta2) {
		EasyFTACreator fc = new EasyFTACreator();
		StdStateBuilder<Pair<State,State>> pc = new StdStateBuilder<Pair<State,State>>();
		return FTAOps.intersectionBU(fta1, fta2, pc, fc);
	}


	/**
	 * Given two finite tree automata, constructs a finite tree automaton which accepts a tree 
	 * if and only if both automata accept it. The resulting tree automaton is top down reduced.
	 * 
	 * @param fta1 first finite tree automaton for the intersection
	 * @param fta2 second finite tree automaton for the intersection
	 * @return finite tree automaton which accepts a tree if and only if both finite tree automata accept it
	 * @see FTAOps#intersectionTD
	 */
	public static EasyFTA intersectionTD(FTA<RankedSymbol,State,? extends FTARule<RankedSymbol,State>> fta1, 
			FTA<RankedSymbol,State,? extends FTARule<RankedSymbol,State>> fta2) {
		EasyFTACreator fc = new EasyFTACreator();
		StdStateBuilder<Pair<State,State>> pc = new StdStateBuilder<Pair<State,State>>();
		return FTAOps.intersectionTD(fta1, fta2, pc, fc);
	}

	
	/**
	 * Given two finite tree automata, constructs a finite tree automaton which accepts a tree 
	 * if and only if both automata accept it.
	 * @param fta1 first finite tree automaton for the intersection
	 * @param fta2 second finite tree automaton for the intersection
	 * 
	 * @return finite tree automaton which accepts a tree if and only if both finite tree automata accept it
	 * 
	 * @see FTAOps#intersectionWR
	 */
	public static EasyFTA intersectionWR(FTA<RankedSymbol,State,? extends FTARule<RankedSymbol,State>> fta1, 
			FTA<RankedSymbol,State,? extends FTARule<RankedSymbol,State>> fta2) {
		EasyFTACreator fc = new EasyFTACreator();
		StdStateBuilder<Pair<State,State>> pc = new StdStateBuilder<Pair<State,State>>();
		return FTAOps.intersectionWR(fta1, fta2, pc, fc);
	}


	/**
	 *  Given two finite tree automata, constructs a finite tree automaton which 
	 * recognizes a tree if and only if it is recognized by the first but not by the second
	 * finite tree automaton.
	 * 
	 * @param fta1 first finite tree automaton for the basic language 
	 * @param fta2 second finite tree automaton for the language which shall be subtracted
	 * 
	 * @return a finite tree automaton which recognizes a tree
	 * if and only if it is recognized by the first but not by the second finite tree automaton. 
	 * 
	 * @see FTAOps#difference
	 */
	public static EasyFTA difference(FTA<RankedSymbol,State,? extends FTARule<RankedSymbol,State>> fta1, FTA<RankedSymbol,State,? extends FTARule<RankedSymbol,State>> fta2) {
		EasyFTACreator fc = new EasyFTACreator();
		StdStateBuilder<Pair<State,State>> pc = new StdStateBuilder<Pair<State,State>>();
		StdStateBuilder<Set<State>> sc = new StdStateBuilder<Set<State>>();
		return FTAOps.difference(fta1, fta2, sc, fc, pc, fc);
	}


	/**
	 * Given a tree containing some constants (symbols with arity 0) that are to be replaced 
	 * and a map mapping exactly these symbols to regular tree languages represented by finite 
	 * tree automata, constructs a finite tree automaton which recognizes exactly
	 * the trees which are obtained by substituting the specified constants by trees of the
	 * corresponding languages.
	 * 
	 * @param tree tree with variables, which shall be replaced by the given regular languages
	 * @param languages given regular languages, given by a map which maps each constant
	 * (symbol with arity 0) which shall be replaced, to a finite tree automaton.
	 * 
	 * @return finite tree automaton which recognizes exactly
	 * the trees which are obtained by substituting each variable by a tree of the
	 * corresponding language.
	 * 
	 * @see FTAOps#substitute(Tree, Map, Converter, Converter, Converter, FTACreator)
	 *
	 */
	public static EasyFTA substitute(Tree<RankedSymbol> tree, Map<? extends RankedSymbol,? extends FTA<RankedSymbol,State,? extends FTARule<RankedSymbol,State>>> languages) {

		/* converts a pair consisting of a state and an integer into a state - 
		 * conversion must be injective and resulting states
		 * must not be equal to states resulting from the other converters
		 */
		Converter<Pair<State,Integer>,State> intStateConv = new Converter<Pair<State,Integer>,State>() {
			@Override
			public State convert(Pair<State,Integer> a) {
				return StateFactory.getStateFactory().makeState(a);
			}
		};

		/* converts an integer into a state - conversion must be injective 
		 * and resulting states
		 * must not be equal to states resulting from the other converters*/
		Converter<Integer,State> intConv = new Converter<Integer,State>() {
			@Override
			public State convert(Integer i) {
				return StateFactory.getStateFactory().makeState(i);
			}
		};

		/*
		 * treeStateConv converts variable tree into a state - conversion must be injective 
		 * and resulting states must not be equal to states resulting from the other converters
		 */
		Converter<Tree<RankedSymbol>,State> treeStateConv = new Converter<Tree<RankedSymbol>,State>() {
			@Override
			public State convert(Tree<RankedSymbol> v) {
				return StateFactory.getStateFactory().makeState(v);
			}
		};


		//EpsFTACreator<State,RankedSymbol,EasyFTARule,StdFTAEpsRule,EasyFTA,EasyEpsFTA> fc 
		EasyFTACreator fc = new EasyFTACreator();

		//apply generic method
		return  FTAOps.substitute(
				tree,languages,intStateConv,intConv,treeStateConv,fc);

	}	


	/**
	 * Computes a finite tree automaton, which accepts exactly the specified tree.
	 * 
	 * @param <F> type of symbols occurring in the resulting finite tree automaton
	 * @param tree tree to be accepted by the returned finite tree automaton
	 * 
	 * @return finite tree automaton which recognizes a tree if and only if it is equal to the given one
	 * 
	 * @see FTAOps#computeSingletonFTA
	 */
	public static <F extends RankedSymbol> EasyFTA computeSingletonFTA(Tree<F> tree) {
		EasyFTACreator fc = new EasyFTACreator();
		StdStateBuilder<Object> sb = new StdStateBuilder<Object>();
		return FTAOps.computeSingletonFTA(tree, fc, sb);
	}


	/**
	 * Constructs a finite tree automaton which accepts every tree over a given alphabet.
	 * 
	 * @param alphabet alphabet for trees which are to be accepted
	 * tree automaton and the new tree automaton
	 * @return a finite tree automaton which accepts every tree over the given alphabet
	 * 
	 * @see FTAOps#computeAlphabetFTA(Collection, State, FTACreator)
	 */
	public static EasyFTA computeAlphabetFTA(Collection<RankedSymbol> alphabet){
		State qnew = StateFactory.getStateFactory().makeState();
		return FTAOps.computeAlphabetFTA(alphabet,qnew,new EasyFTACreator());
	}


	/**
	 * Constructs the regular tree language containing all trees of this regular tree language 
	 * which are not higher than specified.
	 * 
	 * @param fta finite tree automaton whose language is to be restricted 
	 * @param maxHeight maximum height of the trees contained in the language to be returned
	 * 
	 * @return a finite tree automaton representing the regular tree language containing 
	 * all trees of the given language which are not higher than specified
	 */
	public static 	EasyFTA restrictToMaxHeight(
			EasyFTA fta, 
			int maxHeight) {
		EasyFTACreator fc = new EasyFTACreator();
		StdStateBuilder<Pair<State,Integer>> sb = new StdStateBuilder<Pair<State,Integer>>();
		return FTAOps.restrictToMaxHeight(fta, maxHeight, fc, sb);
	}
	
	
	/**
	 * Constructs a witness for the non-emptiness of a regular tree language.
	 * 
	 * @param fta finite tree automaton of the language, for whom a witness shall be constructed
	 * @return a witness for the non-emptiness of the language of the given finite tree automaton, i.e.
	 * a tree such that automaton accepts it, or null if the language is empty
	 * 
	 * @see FTAOps#constructTreeFrom
	 */
	public static Tree<RankedSymbol> constructTreeFrom(FTA<RankedSymbol,State,? extends FTARule<RankedSymbol,State>> fta) {
		StdTreeCreator<RankedSymbol> itc = new StdTreeCreator<RankedSymbol>();
		return FTAOps.constructTreeFrom(fta, itc);
	}
	
	 /** Constructs a tree which can be annotated by the given finite tree automaton
	 * with the given state and is at least as high as specified, if there is such a tree. 
	 * Otherwise, null is returned.<br>
	 * If the given state is specified as null, then a tree is constructed, which
	 * is accepted by the given finite tree automaton, i.e. which can be annotated
	 * with a final state.<br>
	 * @param fta finite tree automaton of the language, for whom a witness shall be constructed
	 * @param accState state which the returned tree can be annotated with
	 * @param minHeight minimum height of the tree to be returned
	 * @param depthFirst indicates whether the worklist is to be organized as a stack or a queue -
	 * in the first case, the resulting tree has minimal height, if the specified height is 0.
	 * @return if the given state is not null: a tree which can be annotated with that state, or
	 * null if there is no such tree <br> 
	 * If the given state is null: a tree of minimum which is accepted by the given finite tree automaton
	 * and has minimum height, or null if there is no such tree
	 */
	public static Tree<RankedSymbol> constructTreeAcceptedInState(FTA<RankedSymbol,State,? extends FTARule<RankedSymbol,State>> fta, State accState, int minHeight, boolean depthFirst) { 
		return FTAOps.constructTreeAcceptedInState(fta, new StdTreeCreator<RankedSymbol>(), accState, minHeight, depthFirst);
	}
	
	/**
	 * Given a finite tree automaton, constructs a tree accepted by it, which has
	 * at least the specified height. <br>
	 * @param fta finite tree automaton of the language, for which a witness is to be constructed
	 * @param minHeight the height which the resulting tree will have at least
	 * @param depthFirst specifies the order in which the rules of the finite tree automaton
	 * will be iterated.
	 * @return a tree of minimum height accepted by the specified automaton or null if there is
	 * no accepted tree.
	 * @see FTAOps#constructTreeWithMinHeightFrom
	 */
	public static Tree<RankedSymbol> constructTreeWithMinHeightFrom(
			FTA<RankedSymbol, State, ? extends FTARule<RankedSymbol, State>> fta, int minHeight, boolean depthFirst) {
		return FTAOps.constructTreeAcceptedInState(fta, new StdTreeCreator<RankedSymbol>(), null, minHeight, depthFirst);
	}

}
