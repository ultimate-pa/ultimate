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
package de.uni_muenster.cs.sev.lethal.treeautomata.generic;


import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_muenster.cs.sev.lethal.factories.StateFactory;
import de.uni_muenster.cs.sev.lethal.states.BiState;
import de.uni_muenster.cs.sev.lethal.states.NamedState;
import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
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
 * The standard implementation for operations on finite tree automata using generic types.
 * 
 * 
 * @see FTAOps
 * 
 * @author Dorothea, Martin, Irene
 */
public class GenFTAOps {

	/**
	 * Builds a state out of an arbitrary object. The object is taken as name of the new state and
	 * identifies it.
	 * 
	 * @param <T> type of the object to identify the new state
	 * 
	 * @see NamedState 
	 */
	protected static class StdStateBuilder<T> implements Converter<T,NamedState<T>> {
		/**
		 * @see de.uni_muenster.cs.sev.lethal.utils.Converter#convert(java.lang.Object)
		 */
		@Override
		public NamedState<T> convert(T a) {
			return StateFactory.getStateFactory().makeState(a);
		}

	}



	/**
	 * Implementation of BiState. Specification is realized by having references to two possible
	 * state kinds. Exactly one of them is null, the other is used as the represented state.
	 * 
	 * @param <Q1> type of first state kind
	 * @param <Q2> type of second state kind
	 * 
	 * @see BiState
	 */
	protected static final class StdBiState<Q1 extends State,Q2 extends State> implements BiState<Q1,Q2> {

		/**
		 * Reference to the first possible kind of represented states.
		 */
		private Q1 q1;

		/**
		 * Reference to the second possible kind of represented states.
		 */
		private Q2 q2;


		/**
		 * Constructs a new BiState out of two states. Exactly one of the supplied states must be
		 * null, the other one acts as the represented state.
		 * 
		 * @param q1 first state - not null if it is to be represented
		 * @param q2 second state - not null if it is to be represented
		 */
		public StdBiState(Q1 q1, Q2 q2) {
			if ((q1==null && q2==null) || (q1!=null && q2!=null))
				throw new IllegalArgumentException("Exactly one of the two supplied states must be null!");
			this.q1 = q1;
			this.q2 = q2;
		}


		/**
		 * Returns whether this state represents the first state given in the constructor.
		 * @return true if the first state given was not null, false otherwise
		 */
		public boolean isFirstKind() {
			return q1!=null;
		}


		/**
		 * Returns whether this state represents the second state given in the constructor.
		 * @return true if the second state given was not null, false otherwise
		 */
		public boolean isSecondKind() {
			return q1!=null;
		}


		/**
		 * Returns the first state given in the constructor.
		 * @return the first state given in the constructor
		 */
		public Q1 asFirstKind() {
			return q1;
		}


		/**
		 * Returns the second state given in the constructor.
		 * @return the second state given in the constructor
		 */
		public Q2 asSecondKind() {
			return q2;
		}


		/**
		 * @see java.lang.Object#hashCode()
		 */
		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((this.q1 == null) ? 0 : this.q1.hashCode());
			result = prime * result + ((this.q2 == null) ? 0 : this.q2.hashCode());
			return result;
		}


		/**
		 * @see java.lang.Object#equals(java.lang.Object)
		 */
		@Override
		@SuppressWarnings("unchecked")
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			StdBiState other = (StdBiState) obj;
			if (this.q1 == null) {
				if (other.q1 != null)
					return false;
			} else if (!this.q1.equals(other.q1))
				return false;
			if (this.q2 == null) {
				if (other.q2 != null)
					return false;
			} else if (!this.q2.equals(other.q2))
				return false;
			return true;
		}

		/**
		 * @see java.lang.Object#toString()
		 */
		@Override
		public String toString(){
			return "("+q1+","+q2+")";
		}
	}




	/**
	 * Given a finite tree automaton, constructs an equivalent complete finite tree automaton.
	 * 
	 * @param <Q> state type of the finite tree automaton to be completed
	 * @param <F> symbol type of the finite tree automaton to be completed
	 * @param fta finite tree automaton to be completed
	 * @param qbot fresh state for rules to be added
	 * 
	 * @return complete finite tree automaton equivalent to the given finite tree automaton
	 * 
	 * @see FTAOps#complete(FTA, State, de.uni_muenster.cs.sev.lethal.treeautomata.common.FTACreator)
	 */
	public static <F extends RankedSymbol, Q extends State> GenFTA<F,Q> complete(FTA<F,Q,? extends FTARule<F,Q>> fta, Q qbot) {
		return FTAOps.complete(fta,qbot,new GenFTACreator<F,Q>());
	}


	/**
	 * Given a finite tree automaton A, constructs a tree automaton which accepts a tree if and only if
	 * A denies it with respect to the union of its alphabet and some given alphabet. <br>
	 * 
	 * @param <Q> state type of finite tree automaton to be completed
	 * @param <F> symbol type of finite tree automaton to be completed
	 * @param fta finite tree automaton to be completed
	 * @param alphabet alphabet with respect to which the automaton shall be completed
	 * @param qbot fresh state for rules to be added
	 * 
	 * @return complete finite tree automaton equivalent to the given finite tree automaton w.r.t. the given alphabet 
	 * 
	 * @see FTAOps#completeAlphabet(FTA, Collection, State, FTACreator)
	 */
	public static <F extends RankedSymbol, Q extends State> GenFTA<F,Q> 
	completeAlphabet (FTA<F,Q, ? extends FTARule<F,Q>> fta, Q qbot, Collection<F> alphabet) {
		return FTAOps.completeAlphabet(fta, alphabet, qbot, new GenFTACreator<F,Q>());
	}


	/**
	 * Given a given finite tree automaton A, computes an equivalent deterministic 
	 * finite tree automaton.
	 * 
	 * @param <Q> state type of the finite tree automaton to be determinized
	 * @param <F> symbol type of the finite tree automaton to be determinized
	 * @param fta automaton to be determinized
	 * 
	 * @return deterministic finite tree automaton equivalent to the given one
	 * 
	 * @see FTAOps#determinize
	 */
	public static <F extends RankedSymbol,Q extends State> GenFTA<F,NamedState<Set<Q>>> determinize(FTA<F,Q,? extends FTARule<F,Q>> fta) {
		return FTAOps.determinize(fta, new GenFTACreator<F,NamedState<Set<Q>>>(), new StdStateBuilder<Set<Q>>());
	}


	/**
	 * Given a finite tree automaton A, constructs an equivalent reduced finite tree automaton.
	 * 
	 * @param <Q> state type of finite tree automaton to be reduced
	 * @param <F> symbol type of finite tree automaton to be reduced
	 * @param fta finite tree automaton to be reduced
	 * 
	 * @return reduced version of supplied finite tree automaton
	 * 
	 * @see FTAOps#reduceBottomUp
	 */
	public static <F extends RankedSymbol, Q extends State> GenFTA<F,Q> reduceBottomUp(FTA<F,Q,? extends FTARule<F,Q>> fta) {
		return FTAOps.reduceBottomUp(fta, new GenFTACreator<F,Q>());
	}


	/**
	 * Given a finite tree automaton A, constructs an equivalent finite tree automaton A', 
	 * which is top-down reduced.
	 * 
	 * @param <Q> state type of the finite tree automaton to be reduced
	 * @param <F> symbol type of the finite tree automaton to be reduced
	 * @param fta finite tree automaton to be reduced
	 * 
	 * @return equivalent finite tree automaton which only contains states from which a 
	 * final state is reachable and contains only the rules in which merely these states occur.
	 * 
	 * @see FTAOps#reduceTopDown
	 */
	public static <F extends RankedSymbol, Q extends State> GenFTA<F,Q> reduceTopDown(FTA<F,Q, ? extends FTARule<F,Q>> fta) {
		return FTAOps.reduceTopDown(fta, new GenFTACreator<F,Q>());
	}


	/**
	 * Given a finite tree automaton, constructs a finite tree automaton which is both top-down and
	 * bottom-up reduced. 
	 * 
	 * @param <Q> state type of the finite tree automaton to be reduced
	 * @param <F> symbol type of the finite tree automaton to be reduced
	 * @param fta finite tree automaton to be reduced
	 * 
	 * @return fully reduced version of the given finite tree automaton, that means for every rule f(q1,...qn) - q there is a
	 * tree t, a configuration tree tc and a final state qf such that f(q1,...qn) is a subtree of tc, t can
	 * be reduced to tc and tc can be reduced to qf.
	 * 
	 * @see FTAOps#reduceFull
	 */
	public static  <F extends RankedSymbol, Q extends State> GenFTA<F,Q>  reduceFull(FTA<F,Q,? extends FTARule<F,Q>> fta) {
		GenFTACreator<F,Q> fc = new GenFTACreator<F,Q>();
		return FTAOps.reduceFull(fta, fc);
	}


	/**
	 * Given a deterministic finite tree automaton, constructs an equivalent finite tree automaton 
	 * with an almost minimal number of states. 
	 * 
	 * @param fta  finite tree automaton to be minimized
	 * @param qbot state to be added by completion
	 * @param <Q> state type of the given finite tree automaton
	 * @param <F> symbol type of the given finite tree automaton
	 * 
	 * @return finite tree automaton with a minimal number of states which has the same
	 * language as the given one
	 * 
	 * @see FTAOps#minimize
	 */
	public static <F extends RankedSymbol, Q extends State> 
	GenFTA<F, NamedState<Set<Q>>> minimize(FTA<F,Q,? extends FTARule<F,Q>> fta, Q qbot) {
		return FTAOps.minimize(fta, qbot, new GenFTACreator<F,Q>(), new StdStateBuilder<Set<Q>>(), new GenFTACreator<F,NamedState<Set<Q>>>());
	}


	/**
	 * Given a finite tree automaton A, constructs a finite tree automaton 
	 * which accepts a tree over the alphabet of A if and only if A denies it.
	 * 
	 * @param <Q> state type of the finite tree automaton to be complemented
	 * @param <F> symbol type of the finite tree automaton to be complemented
	 * @param fta finite tree automaton to be complemented
	 * @return complemented finite tree automaton
	 * 
	 * @see FTAOps#complement
	 */
	public static <F extends RankedSymbol,Q extends State> GenFTA<F,NamedState<Set<Q>>> complement (FTA<F,Q,? extends FTARule<F,Q>> fta) {
		return FTAOps.complement(fta, new StdStateBuilder<Set<Q>>(), new GenFTACreator<F,NamedState<Set<Q>>>());
	}


	/**
	 * Given a finite tree automaton A, constructs a finite tree automaton which accepts a tree if and only if
	 * A denies it with respect to the union of its alphabet and some given alphabet.
	 * 
	 * @param <Q> state type of automaton to be complemented
	 * @param <F> symbol type of automaton to be complemented
	 * @param fta automaton to be complemented
	 * @param alphabet alphabet to which the automaton is to be complemented
	 * 
	 * @return complemented finite tree automaton
	 * 
	 * @see FTAOps#complementAlphabet
	 */
	public static <F extends RankedSymbol, Q extends State> GenFTA<F,NamedState<Set<Q>>> complementAlphabet (FTA<F,Q, ? extends FTARule<F,Q>> fta, Collection<F> alphabet) {
		return FTAOps.complementAlphabet(fta,alphabet, new StdStateBuilder<Set<Q>>(), new GenFTACreator<F,NamedState<Set<Q>>>());
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
	 * @param <F> symbol type of the finite tree automata
	 * @param <Q1> state type of the first finite tree automaton
	 * @param <Q2> state type of the second finite tree automaton
	 * @param fta1 the first finite tree automaton for the union
	 * @param fta2 the second finite tree automaton for the union
	 * 
	 * @return a finite tree automaton that recognizes exactly the union of the 
	 * languages of the given finite tree tree automata
	 * 
	 * @see FTAOps#union
	 */
	public static <F extends RankedSymbol,
	Q1 extends State, 
	Q2 extends State> 
	GenFTA<F,BiState<Q1,Q2>> union (FTA<F,Q1, ? extends FTARule<F,Q1>> fta1, FTA<F,Q2, ? extends FTARule<F,Q2>> fta2) {

		Converter<Q1,BiState<Q1,Q2>> stateconv1 = new Converter<Q1, BiState<Q1,Q2>>() {
			@Override
			public BiState<Q1, Q2> convert(final Q1 a) {
				return new StdBiState<Q1,Q2>(a,null);
			}

		};

		Converter<Q2,BiState<Q1,Q2>> stateconv2 = new Converter<Q2, BiState<Q1,Q2>>() {
			@Override
			public BiState<Q1, Q2> convert(final Q2 a) {
				return new StdBiState<Q1,Q2>(null, a);
			}
		};
		IdentityConverter<F> symbconv = new IdentityConverter<F>();
		return FTAOps.union(fta1, fta2, stateconv1, stateconv2, symbconv, symbconv, new GenFTACreator<F,BiState<Q1,Q2>>());
	}




	/**
	 * Given two finite tree automata, constructs a finite tree automaton which accepts a tree 
	 * if and only if both automata accept it. The suffix "BU" stands for bottom-up reduction.<br>
	 * That means, the algorithm consists of a {@link FTAOps#intersectionWR product construction}  with additional reduction, such
	 * that in the resulting automaton every state is reachable. 
	 * 
	 * @param <F> symbol type of incoming automata
	 * @param <Q1> state type of first incoming automaton
	 * @param <Q2> state type of second incoming automaton
	 * @param fta1 first automaton
	 * @param fta2 second automaton
	 * @return an automaton which accepts a tree if and only if both A1 and A2 accept it.
	 * @see FTAOps#intersectionBU
	 */
	public static <F extends RankedSymbol,
	Q1 extends State,
	Q2 extends State> 
	GenFTA<F,NamedState<Pair<Q1,Q2>>> intersectionBU(FTA<F,Q1,? extends FTARule<F,Q1>> fta1, FTA<F,Q2, ? extends FTARule<F,Q2>> fta2) {
		StdStateBuilder<Pair<Q1,Q2>> pc = new StdStateBuilder<Pair<Q1,Q2>>();
		GenFTACreator<F,NamedState<Pair<Q1,Q2>>> fc = new GenFTACreator<F,NamedState<Pair<Q1,Q2>>>();
		return FTAOps.intersectionBU(fta1, fta2, pc, fc);
	}



	/**
	 * Given two finite tree automata, constructs a finite tree automaton which accepts a tree 
	 * if and only if both automata accept it.
	 * 
	 * @param <F> symbol type of all three finite tree automata. Since the result recognizes the intersection of
	 * the two operands' languages, all three finite tree automata must have the same symbol type.
	 * @param <Q1> state type of the first finite tree automaton
	 * @param <Q2> state type of the first finite tree automaton
	 * @param fta1 first finite tree automaton for the intersection
	 * @param fta2 second finite tree automaton for the intersection
	 * 
	 * @return finite tree automaton which accepts a tree if and only if both finite tree automata accept it
	 * 
	 * @see FTAOps#intersectionTD
	 */
	public static <F extends RankedSymbol, 
	Q1 extends State, 
	Q2 extends State> 
	GenFTA<F,NamedState<Pair<Q1,Q2>>> intersectionTD(FTA<F,Q1, ? extends FTARule<F,Q1>> fta1, FTA<F,Q2, ? extends FTARule<F,Q2>> fta2) {
		StdStateBuilder<Pair<Q1,Q2>> pc = new StdStateBuilder<Pair<Q1,Q2>>();
		GenFTACreator<F,NamedState<Pair<Q1,Q2>>> fc = new GenFTACreator<F,NamedState<Pair<Q1,Q2>>>();
		return FTAOps.intersectionTD(fta1, fta2, pc, fc);
	}



	/**
	 * Given two finite tree automata, constructs a finite tree automaton which accepts a tree 
	 * if and only if both automata accept it.
	 * @param <F> symbol type of all three automata. Since the result recognizes the intersection of
	 * the two operands' languages, all three automata must have the same symbol type.
	 * @param <Q1> state type of the first finite tree automaton
	 * @param <Q2> state type of the first finite tree automaton
	 * @param fta1 first finite tree automaton for the intersection
	 * @param fta2 second finite tree automaton for the intersection
	 * 
	 * @return finite tree automaton which accepts a tree if and only if both finite tree automata accept it
	 * 
	 * @see FTAOps#intersectionWR
	 */
	public static <F extends RankedSymbol,
	Q1 extends State, 
	Q2 extends State> 
	GenFTA<F,NamedState<Pair<Q1,Q2>>> intersectionWR(FTA<F,Q1, ? extends FTARule<F,Q1>> fta1, FTA<F,Q2, ? extends FTARule<F,Q2>> fta2) {
		StdStateBuilder<Pair<Q1,Q2>> pc = new StdStateBuilder<Pair<Q1,Q2>>();
		GenFTACreator<F,NamedState<Pair<Q1,Q2>>> fc = new GenFTACreator<F,NamedState<Pair<Q1,Q2>>>();
		return FTAOps.intersectionWR(fta1, fta2, pc, fc);
	}




	/**
	 *  Given two finite tree automata, constructs a finite tree automaton which 
	 * recognizes a tree if and only if it is recognized by the first but not by the second
	 * finite tree automaton.
	 * 
	 * @param <F> type of the symbols
	 * @param <Q1> type of the states of the first finite tree automaton
	 * @param <Q2> type of the states of the second finite tree automaton
	 * @param fta1 first finite tree automaton for the basic language 
	 * @param fta2 second finite tree automaton for the language which shall be subtracted
	 * 
	 * @return a finite tree automaton which recognizes a tree
	 * if and only if it is recognized by the first but not by the second finite tree automaton. 
	 * 
	 * @see FTAOps#difference
	 */
	public static <F extends RankedSymbol, Q1 extends State, Q2 extends State>
	GenFTA<F,NamedState<Pair<Q1,NamedState<Set<Q2>>>>> difference(FTA<F,Q1, ? extends FTARule<F,Q1>> fta1, FTA<F,Q2, ? extends FTARule<F,Q2>> fta2) {
		GenFTACreator<F,NamedState<Set<Q2>>> fc1 = new GenFTACreator<F,NamedState<Set<Q2>>>();
		GenFTACreator<F,NamedState<Pair<Q1,NamedState<Set<Q2>>>>> fc2 = new GenFTACreator<F,NamedState<Pair<Q1,NamedState<Set<Q2>>>>> ();
		StdStateBuilder<Pair<Q1,NamedState<Set<Q2>>>> pc = new StdStateBuilder<Pair<Q1,NamedState<Set<Q2>>>>();
		StdStateBuilder<Set<Q2>> sc = new StdStateBuilder<Set<Q2>>();
		return FTAOps.difference(fta1, fta2, sc, fc1, pc, fc2);
	}



	/**
	 * Given a tree containing some constants (symbols with arity 0) that are to be replaced 
	 * and a map mapping exactly these symbols to regular tree languages represented by finite 
	 * tree automata, constructs a finite tree automaton which recognizes exactly
	 * the trees which are obtained by substituting the specified constants by trees of the
	 * corresponding languages.
	 * 
	 * @param <F> type of the symbols of the given finite tree automata and trees
	 * @param <Q> type of the states of the given finite tree automata representing languages
	 * @param tree tree with variables, which shall be replaced by the given regular languages
	 * @param languages given regular languages, given by a map which maps each constant
	 * (symbol with arity 0) which shall be replaced, to a finite tree automaton.
	 * 
	 * @return finite tree automaton which recognizes exactly
	 * the trees which are obtained by substituting each variable by a tree of the
	 * corresponding language.
	 * 
	 * @see FTAOps#substitute(Tree, Map, Converter, Converter, Converter, FTACreator)
	 */
	public static <F extends RankedSymbol,Q extends State> GenFTA<F,NamedState<?>> 
	substitute(Tree<F> tree, Map<? extends F,? extends FTA<F,Q, ? extends FTARule<F,Q>>> languages) {

		Converter<Pair<Q,Integer>,NamedState<?>> cPair = new Converter<Pair<Q,Integer>, NamedState<?>>() {

			@Override
			public NamedState<?> convert(Pair<Q,Integer> a) {
				return StateFactory.getStateFactory().makeState(a);
			}

		};

		Converter<Integer,NamedState<?>> cInt = new Converter<Integer, NamedState<?>>() {

			@Override
			public NamedState<?> convert(Integer a) {
				return StateFactory.getStateFactory().makeState(a);
			}

		};

		Converter<Tree<F>,NamedState<?>> cTree = new Converter<Tree<F>, NamedState<?>>() {

			@Override
			public NamedState<?> convert(Tree<F> a) {
				return StateFactory.getStateFactory().makeState(a);
			}

		};

		//apply generic method
		return FTAOps.substitute(tree,languages,cPair,cInt,cTree,new GenFTACreator<F,NamedState<?>>());
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
	public static <F extends RankedSymbol> GenFTA<F,NamedState<Object>> computeSingletonFTA(Tree<F> tree) {
		return FTAOps.computeSingletonFTA(tree, new GenFTACreator<F,NamedState<Object>>(), new StdStateBuilder<Object>());
	}


	/**
	 * Constructs a finite tree automaton which accepts every tree over a given alphabet.
	 * 
	 * @param <F> type of the ranked symbols in the alphabet
	 * @param alphabet alphabet for trees which are to be accepted
	 * tree automaton and the new tree automaton
	 * @return a finite tree automaton which accepts every tree over the given alphabet
	 * 
	 * @see FTAOps#computeAlphabetFTA(Collection, State, FTACreator)
	 */
	public static <F extends RankedSymbol>
	GenFTA<F,State> computeAlphabetFTA(Collection<F> alphabet){
		return FTAOps.computeAlphabetFTA(alphabet,StateFactory.getStateFactory().makeState(),new GenFTACreator<F,State>());
	}

	
	/**
	 * Constructs the regular tree language containing all trees of this regular tree language 
	 * which are not higher than specified.
	 * 
	 * @param <F> symbol type of the finite tree automaton to be restricted
	 * @param <Q> state type of the finite tree automaton to be restricted
	 * @param fta finite tree automaton whose language is to be restricted 
	 * @param maxHeight maximum height of the trees contained in the language to be returned
	 * 
	 * @return a finite tree automaton representing the regular tree language containing 
	 * all trees of the given language which are not higher than specified
	 */
	public static <F extends RankedSymbol, Q extends State> 
	GenFTA<F,NamedState<Pair<Q,Integer>>> restrictToMaxHeight(
			GenFTA<F,Q> fta,
			int maxHeight) {
		GenFTACreator<F,NamedState<Pair<Q,Integer>>> fc = new GenFTACreator<F,NamedState<Pair<Q,Integer>>>();
		StdStateBuilder<Pair<Q,Integer>> sb = new StdStateBuilder<Pair<Q,Integer>>();
		return FTAOps.restrictToMaxHeight(fta, maxHeight, fc, sb);
	}

	
	/**
	 * Constructs a tree which can be annotated by the given finite tree automaton
	 * with the given state and is at least as high as specified, if there is such a tree. 
	 * Otherwise, null is returned.<br>
	 * @param <F> symbol type of the finite tree automaton to be examined
	 * @param <Q> state type of the finite tree automaton to be examined
	 * @param fta finite tree automaton of the language, for whom a witness shall be constructed
	 * @param accState state which the returned tree can be annotated with
	 * @param minHeight minimum height of the tree to be returned
	 * @param depthFirst indicates whether the worklist is to be organized as a stack or a queue -
	 * in the first case, the resulting tree has minimal height, if the specified height is 0.
	 * @return if the given state is not null: a tree which can be annotated with that state, or
	 * null if there is no such tree <br> 
	 * If the given state is null: a tree of minimum which is accepted by the given finite tree automaton
	 * and has minimum height, or null if there is no such tree
	 * @see FTAOps#constructTreeAcceptedInState
	 */
	public static <Q extends State, F extends RankedSymbol> Tree<F> constructTreeAcceptedInState(
			FTA<F, Q, ? extends FTARule<F, Q>> fta, Q accState, final int minHeight, boolean depthFirst) {
		return FTAOps.constructTreeAcceptedInState(fta, new StdTreeCreator<F>(), accState, minHeight, depthFirst);
	}
	
	/**
	 * Given a finite tree automaton, constructs a tree of minimal height accepted by it. <br>
	 * @param <F> symbol type of the finite tree automaton to be examined
	 * @param <Q> state type of the finite tree automaton to be examined
	 * @param fta finite tree automaton of the language, for which a witness is to be constructed
	 * @return a tree of minimum height accepted by the specified automaton or null if there is
	 * no accepted tree.
	 * @see FTAOps#constructTreeFrom
	 */
	public static <Q extends State, F extends RankedSymbol> Tree<F> constructTreeFrom(
			FTA<F, Q, ? extends FTARule<F, Q>> fta) {
		return FTAOps.constructTreeAcceptedInState(fta, new StdTreeCreator<F>(), null, 0, true);
	}
	
	
	/**
	 * Given a finite tree automaton, constructs a tree accepted by it, which has
	 * at least the specified height. <br>
	 * @param <F> symbol type of the finite tree automaton to be examined
	 * @param <Q> state type of the finite tree automaton to be examined
	 * @param fta finite tree automaton of the language, for which a witness is to be constructed
	 * @param minHeight the height which the resulting tree will have at least
	 * @param depthFirst specifies the order in which the rules of the finite tree automaton
	 * will be iterated.
	 * @return a tree of minimum height accepted by the specified automaton or null if there is
	 * no accepted tree.
	 * @see FTAOps#constructTreeWithMinHeightFrom
	 */
	public static <Q extends State, F extends RankedSymbol> Tree<F> constructTreeWithMinHeightFrom(
			FTA<F, Q, ? extends FTARule<F, Q>> fta, int minHeight, boolean depthFirst) {
		return FTAOps.constructTreeAcceptedInState(fta, new StdTreeCreator<F>(), null, minHeight, depthFirst);
	}
}
