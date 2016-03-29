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

package de.uni_muenster.cs.sev.lethal.hom;

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
import de.uni_muenster.cs.sev.lethal.symbol.standard.InnerSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.standard.LeafSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.tree.common.TreeCreator;
import de.uni_muenster.cs.sev.lethal.tree.common.TreeOps;
import de.uni_muenster.cs.sev.lethal.tree.common.VarTreeOps;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTACreator;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAProperties;
import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTARule;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTAEpsRule;
import de.uni_muenster.cs.sev.lethal.utils.Converter;
import de.uni_muenster.cs.sev.lethal.utils.Pair;

/**
 * Operations on homomorphisms which involve regular tree languages: <br>
 * <ul>
 * <li>{@link #apply apply}: applying a homomorphism on a tree</li>
 * <li>{@link #applyOnAutomaton applyOnAutomaton}: given a linear homomorphism and a regular tree language (represented
 * by a finite tree automaton), returns the regular tree language (automaton) given by the images of the trees of the
 * given language under the homomorphism.</li>
 * <li>{@link #applyInverseOnAutomaton applyInverseOnAutomaton}: given a homomorphism and a regular tree language
 * (represented by a finite tree automaton), returns the regular tree language (automaton) whose language is mapped by
 * the homomorphism to the given language.</li>
 * </ul>
 * <br>
 * 
 * Properties of homomorphisms: <br>
 * <ul>
 * <li>{@link #isLinear linear}: A homomorphism is called linear if each variable occurs at most once.</li>
 * <li>{@link #isEpsilonFree epsilon free}: A homomorphism is called epsilon free if no symbol is mapped just to a
 * variable.</li>
 * <li>{@link #isSymbolToSymbol symbol to symbol}: A homomorphism is called symbol to symbol if for each symbol the
 * height of the image of this symbol is 1.</li>
 * <li>{@link #isComplete complete}: A homomorphism is called complete if for each symbol with arity n, the image of f
 * contains all variables from 0 to n-1.</li>
 * <li>{@link #isDelabeling delabeling}: A homomorphism is called delabeling if it is complete, linear and symbol to
 * symbol.</li>
 * <li>{@link #isAlphabetic alphabetic}: A homomorphism is called alphabetic if for each symbol f the image of f is of
 * the form g(x_0, ...x_{n-1}) where g is a symbol of the destination alphabet.</li>
 * </ul>
 * 
 * @see Hom
 * 
 * @author Dorothea, Irene, Martin
 */
public class HomOps {

	/**
	 * Computes the smallest possible destination alphabet of the homomorphism. <br>
	 * This is the set of function symbols occurring in the image trees of the homomorphism.
	 * 
	 * @param <F>
	 *            type of function symbols in source alphabet of the given homomorphism
	 * @param <G>
	 *            type of function symbols occurring in image trees of the given homomorphism
	 * @param <V>
	 *            type of variables occurring in image trees of the given homomorphism
	 * @param <T>
	 *            type of image trees of the given homomorphism
	 * @param hom
	 *            homomorphism whose destination alphabet is to be identified
	 * @return all function symbols which occur in image trees of given homomorphism
	 */
	public static <F extends RankedSymbol, G extends RankedSymbol, V extends Variable, T extends Tree<? extends BiSymbol<G, V>>> Set<G> computeDestAlphabet(
			Hom<F, G, V> hom) {
		Set<G> ret = new HashSet<G>();
		for (F f : hom.getSrcAlphabet()) {
			ret.addAll(VarTreeOps.computeRankedSymbols(hom.imageOf(f)));
		}

		return ret;
	}

	/* section: applying a homomorphism on a tree */

	/**
	 * Applies the homomorphism on a given tree. <br>
	 * <br>
	 * Algorithm: <br>
	 * Build the tree recursively: Let f(t_0,...,t_{n-1}) be a given tree. First apply the homomorphism on the subtrees,
	 * then gain a list out of function trees of length n, the arity of f. Then replace the variables (using the method
	 * {@link VarTreeOps#replaceVariables(Tree, List, TreeCreator)}) in the image of f according to this list.
	 * 
	 * @param hom
	 *            the homomorphism to be applied to the given tree
	 * @param startTree
	 *            the tree on which the given homomorphism is to be applied to
	 * @param tc
	 *            tree creator to construct the resulting tree
	 * @param <F>
	 *            type of function symbols in source alphabet of the given homomorphism
	 * @param <G>
	 *            type of function symbols occurring in image trees of the given homomorphism
	 * @param <V>
	 *            type of variables occurring in the image trees of the given homomorphism
	 * @param <X>
	 *            type of trees in the source range of the homomorphism
	 * @param <Y>
	 *            type of trees in the destination range of the homomorphism
	 * @return the tree of the destination alphabet which is gained by applying the homomorphism
	 */
	public static <F extends RankedSymbol, G extends RankedSymbol, V extends Variable, X extends Tree<F>, Y extends Tree<G>> Y apply(
			Hom<F, G, V> hom, X startTree, TreeCreator<G, Y> tc) {
		/*
		 * idea: number the variables and save in a list at the i-th place, what should replace variable i, then replace
		 * it
		 */
		List<? extends Tree<F>> subTrees1 = startTree.getSubTrees();
		// apply the homomorphism on subtrees
		List<Y> subTrees2 = new LinkedList<Y>();
		for (Tree<F> sub : subTrees1) {
			Y bla = apply(hom, (X) sub, tc);
			subTrees2.add(bla);
		}
		// in the tree replace the variables by the right subtrees
		if (hom.containsSrcSymbol(startTree.getSymbol()))
			return VarTreeOps.<G, V, Y> replaceVariables(hom.imageOf(startTree.getSymbol()), subTrees2, tc);
		else
			throw new IllegalArgumentException(
					"The homomorphism can not be applied on this tree, because it is not defined for all symbols.");
		// return tc.makeTree(c.convert(startTree.getSymbol()), Collections.<Y>emptyList());
	}

	// SECTION: APPLYING A HOMOMORPHISM ON A TREEAUTOMATON

	/**
	 * Applies a given homomorphism on a regular language. <br>
	 * In detail: Given a finite tree automaton, the method constructs a new one, which recognises the language obtained
	 * by applying the homomorphism on the regular language which is recognised by the given finite tree automaton. This
	 * is only possible, if the homomorphism is linear, i.e. there is no image tree in which a variable occurs twice. If
	 * the given homomorphism is not linear, an Exception is thrown.<br>
	 * <br>
	 * Algorithm: <br>
	 * First a finite tree automaton with epsilon rules is created, then the epsilon rules are eliminated. The rules of
	 * this automaton are gained in the following way:<br>
	 * r = f(q1,...,qn)->q rule of the first ta, <br>
	 * tf = image of f under the map h that specifies the homomorphism <br>
	 * Q^r = {q^p_r | p is a Position of tf} <br>
	 * Delta^r is the set of rules that is given by the following: for all positions p of tf <br>
	 * <ol>
	 * <li>if (tf=g) and if g is an element of the range of h, then g(q_{p1}^r,...,q_{pn}^r)->q_p^r is an new rule</li>
	 * <li>if (tf=xi), then q_i->q_p^r is a new rule</li>
	 * <li>q_{eps}^r->q is a new rule</li>
	 * </ol>
	 * Q' = Q cup bigcup_r Q^r<br>
	 * Q_f' = Q_f<br>
	 * Delta = bigcup_{r} Delta^r<br>
	 * 
	 * @param <F>
	 *            type of function symbols in source alphabet of the given homomorphism
	 * @param <G>
	 *            type of function symbols occurring in image trees of the given homomorphism
	 * @param <V>
	 *            type of variables occurring in image trees of the given homomorphism
	 * @param <Q1>
	 *            type of states of the finite tree automaton which the homomorphism shall be applied to
	 * @param <Q2>
	 *            type of states of the resulting finite tree automaton
	 * @param <R0>
	 *            type of rules of the finite tree automaton which the homomorphism shall be applied to
	 * @param <R>
	 *            type of rules of the resulting finite tree automaton
	 * @param <X>
	 *            type of the resulting finite tree automaton
	 * @param hom
	 *            homomorphism which shall be applied to the given finite tree automaton
	 * @param ta
	 *            finite tree automaton which the given homomorphism shall be applied to
	 * @param c
	 *            converts states of type Q1 into states of type Q2
	 * @param c2
	 *            converts pairs of rules and lists into states of type Q2
	 * @param fc
	 *            to create epsilon rules of the given type
	 * @return new tree automaton which describes all trees gained by applying the homomorphism on all trees given by
	 *         the given finite tree automaton
	 */
	public static <F extends RankedSymbol, G extends RankedSymbol, V extends Variable, Q1 extends State, Q2 extends State, R0 extends FTARule<F, Q1>, R extends FTARule<G, Q2>, X extends FTA<G, Q2, R>> X applyOnAutomaton(
			Hom<F, G, V> hom, FTA<F, Q1, R0> ta, Converter<? super Q1, Q2> c,
			Converter<? super Pair<R0, List<Integer>>, Q2> c2, FTACreator<G, Q2, R, X> fc) {
		if (!isLinear(hom)) {
			throw new IllegalArgumentException("The homomorphismus ist not linear and can therefore "
					+ "not be applied on a finite tree automaton.");
		}
		if (!hom.getSrcAlphabet().containsAll(ta.getAlphabet())) {
			LinkedList<F> notDefinedOn = new LinkedList<F>();
			for (F f : ta.getAlphabet()) {
				if (!hom.getSrcAlphabet().contains(f))
					notDefinedOn.add(f);
			}
			throw new IllegalArgumentException("The homomorphism must be defined for all symbols of the alphabet"
					+ "of the finite tree automaton. It is not defined on: " + notDefinedOn);
		}

		// create set of new states
		HashSet<Q2> newStates = new HashSet<Q2>();
		// embed old states (that is because "Q subset Q' ")
		// create map to remember which old state belongs to which new state
		HashMap<Q1, Q2> mapOldStates = new HashMap<Q1, Q2>();
		for (Q1 oldState : ta.getStates()) {
			// State q = factory.createState(oldState);
			// newStates.add(q);
			mapOldStates.put(oldState, c.convert(oldState));
		}

		// new rules
		HashSet<R> newRules = new HashSet<R>();
		HashSet<GenFTAEpsRule<Q2>> newEpsRules = new HashSet<GenFTAEpsRule<Q2>>();

		// create new states
		for (R0 rule : ta.getRules()) {
			// for each rule r = f(q1,..,q.n)->q, get tf,
			Tree<? extends BiSymbol<G, V>> tree = hom.imageOf(rule.getSymbol());
			// examine the positions of tf,
			LinkedList<Integer> position = new LinkedList<Integer>();
			// add first rule for pole position (case (c))
			// the position is epsilon, in other words: the empty list
			Q2 q = c2.convert(new Pair<R0, List<Integer>>(rule, position));
			newStates.add(q);
			GenFTAEpsRule<Q2> epsRule = new GenFTAEpsRule<Q2>(q, c.convert(rule.getDestState()));// q_{eps}^r->q
			newEpsRules.add(epsRule);

			HomOps.createRulesForAutomaton(rule, tree, position, newStates, newRules, newEpsRules, q, mapOldStates, c2,
					fc);
		}
		// convert final states (Q_f'= Q_f, but of course of the new type)
		HashSet<Q2> newFinalStates = new HashSet<Q2>();
		for (Q1 qf : ta.getFinalStates()) {
			newFinalStates.add(mapOldStates.get(qf));
		}
		// create the new automaton with with these states and rules; that automaton will have eps-rules
		// and make it to an automaton without epsilon-rules
		return fc.createFTA(HomOps.computeDestAlphabet(hom), newStates, newFinalStates, newRules, newEpsRules);
	}

	/**
	 * Helper method for applyOnAutomaton: Creates the rules needed and specified in {@link HomOps#applyOnAutomaton}.
	 * 
	 * @param <F>
	 *            type of function symbols in source alphabet of the given homomorphism
	 * @param <G>
	 *            type of function symbols occurring in image trees of the given homomorphism
	 * @param <V>
	 *            type of variables occurring in image trees of the given homomorphism
	 * @param <Q1>
	 *            type of states of the finite tree automaton which the homomorphism shall be applied to
	 * @param <R0>
	 *            type of rules of the finite tree automaton which the homomorphism shall be applied to
	 * @param <Q2>
	 *            type of states of the resulting finite tree automaton
	 * @param <R>
	 *            type of rules of the resulting finite tree automaton
	 * @param <X>
	 *            type of the resulting finite tree automaton
	 * @param rule
	 *            regarded rule
	 * @param tree
	 *            regarded subtree
	 * @param actPos
	 *            regarded actual position in the tree
	 * @param newStates
	 *            set that contains already created new states, in which newly created states must be inserted
	 * @param newRules
	 *            set that contains already created new rules, in which newly created rules must be inserted
	 * @param newEpsRules
	 *            epsilon rules for the finite tree automaton with epsilon rules that contains already created rules
	 * @param actDestState
	 *            already converted state of the regarded rule
	 * @param map
	 *            map to remember the mapping between old and new states
	 * @param c2
	 *            converts pairs of rules and lists of integers into states of type Q2
	 * @param fc
	 *            to create epsilon rules of given type
	 */
	private static <F extends RankedSymbol, G extends RankedSymbol, V extends Variable, Q1 extends State, R0 extends FTARule<F, Q1>, Q2 extends State, R extends FTARule<G, Q2>, X extends FTA<G, Q2, R>> void createRulesForAutomaton(
			R0 rule, Tree<? extends BiSymbol<G, V>> tree, LinkedList<Integer> actPos, Set<Q2> newStates,
			Set<R> newRules, Set<GenFTAEpsRule<Q2>> newEpsRules, Q2 actDestState, HashMap<Q1, Q2> map,
			Converter<? super Pair<R0, List<Integer>>, Q2> c2, FTACreator<G, Q2, R, X> fc) {
		// symbol = tf (the root symbol of the regarded subtree is exactly tf)
		BiSymbol<G, V> symbol = tree.getSymbol();
		// create new states of subtrees
		newStates.add(c2.convert(new Pair<R0, List<Integer>>(rule, actPos)));
		// create new rule
		// case (b) : is it (tf=xi), then create as a new rule q_i->q_p^r
		if (symbol.isLeafType()) {
			V v = symbol.asLeafSymbol();
			Integer nr = v.getComponentNumber(); // nr=i where symbol=xi
			Q1 qi = rule.getSrcStates().get(nr); // qi in the rule r=f(q1,...,qn)->q
			GenFTAEpsRule<Q2> er = new GenFTAEpsRule<Q2>(map.get(qi), actDestState); // q_i->q_p^r
			newEpsRules.add(er);
			return;
		}
		// else it is not a variable (case (a))
		// it is tf=gfor an element g of the range of h, now create g(q_{p1}^r,...,q_{pn}^r)->q_p^r
		// new states for the subtrees
		int i = 0;
		LinkedList<Q2> srcStates = new LinkedList<Q2>();
		for (Tree<? extends BiSymbol<G, V>> sub : tree.getSubTrees()) {

			LinkedList<Integer> newPos = new LinkedList<Integer>(actPos);
			newPos.add(i);

			// create new State q{pi}^i
			Q2 qnew = c2.convert(new Pair<R0, List<Integer>>(rule, newPos));
			srcStates.add(qnew);
			newStates.add(qnew);

			// recursion
			HomOps.<F, G, V, Q1, R0, Q2, R, X> createRulesForAutomaton(rule, sub, newPos, newStates, newRules,
					newEpsRules, qnew, map, c2, fc);

			i++;
		}
		// create new rule
		R newRule = fc.createRule(tree.getSymbol().asInnerSymbol(), srcStates, actDestState);// g(q_{p_1}^r,...,q_{p_n}^r)->q_p^
		newRules.add(newRule);
	}

	/* section: applying an inverse homomorphism */

	/**
	 * Given a finite tree automaton, this method returns a finite tree automaton whose language is mapped by the
	 * homomorphism to the language of the given automaton. <br>
	 * <br>
	 * Algorithm:<br>
	 * Add an additional state s to the states Q of given automaton. <br>
	 * Consider the symbols in the source alphabet:
	 * <ul>
	 * <li>For each constant a and hom(a)->*q add a rule a->q</li>
	 * <li>For each constant a add a rule a->s</li>
	 * <li>For each symbol f with arity n and hom(f){x_1<-p_1, ... x_n<-p_n} ->* q add a rule f(q_1,...,q_n)->q where
	 * q_i=p_i if x_i occurs and q_i= s otherwise</li>
	 * <li>For each symbol f with arity n add a rule f(s,...,s)->s</li>
	 * </ul>
	 * 
	 * @param <F>
	 *            type of function symbols in the source alphabet of the given homomorphism
	 * @param <G>
	 *            type of function symbols in the destination alphabet of the given homomorphism
	 * @param <V>
	 *            type of variables occurring in the image of the given homomorphism
	 * @param <U>
	 *            type of trees with symbols of type G
	 * @param <V0>
	 *            type of configuration trees associated with the given finite tree automaton
	 * @param <Q1>
	 *            type of states of the given finite tree automaton
	 * @param <Q2>
	 *            type of states of the resulting finite tree automaton
	 * @param <R>
	 *            type of rules of the resulting finite tree automaton
	 * @param <Y>
	 *            type of the resulting finite tree automaton
	 * @param hom
	 *            homomorphism to be inverse-applied to the given finite tree automaton
	 * @param ta
	 *            finite tree automaton which describes the regular tree language on which the inverse homomorphism is
	 *            to be applied
	 * @param btc
	 *            to create configuration trees needed for the algorithm
	 * @param s
	 *            some state needed for the construction - must not be contained in the given finite tree automaton
	 * @param c
	 *            to convert the states of the given finite tree automaton into the states of the resulting finite tree
	 *            automaton - conversion must be injective!
	 * @param tc
	 *            creator object for trees in the range of the given homomorphism - needed for replacing variables
	 * @param fc
	 *            to create the resulting automaton
	 * 
	 * @return a finite tree automaton whose language is mapped by the homomorphism to the language of the given
	 *         automaton. <br>
	 */
	public static <F extends RankedSymbol, G extends RankedSymbol, V extends Variable, U extends Tree<G>, Q2 extends State, V0 extends Tree<BiSymbol<G, Q2>>, Q1 extends State, R extends FTARule<F, Q1>, Y extends FTA<F, Q1, R>> Y applyInverseOnAutomaton(
			Hom<F, G, V> hom, FTA<G, Q2, ? extends FTARule<G, Q2>> ta, Q1 s, Converter<Q2, Q1> c, TreeCreator<G, U> tc,
			FTACreator<F, Q1, R, Y> fc, TreeCreator<BiSymbol<G, Q2>, V0> btc) {

		// add one new state (that is the state s) to the set of states
		HashSet<Q1> newStates = new HashSet<Q1>();
		for (Q2 q2 : ta.getStates())
			newStates.add(c.convert(q2));
		newStates.add(s);

		// set of new rules
		Set<R> newRules = new HashSet<R>();
		// consider all symbols of the source alphabet of the homomorphism
		for (F f : hom.getSrcAlphabet()) {
			// System.out.println("consider symbol "+f + " with arity " + f.getArity());
			int n = f.getArity();
			// tree to which f is mapped by the homomorphism
			Tree<? extends BiSymbol<G, V>> tree = hom.imageOf(f);
			// empty list of source states for the rules we are to create
			List<Q1> newSrcStates = new LinkedList<Q1>();
			// n=0: add rules (a) f->s and (b) f->q for all q with hom(f) ->* q
			// n=0: the tree contains no variables
			if (n == 0) {
				// (a)
				newRules.add(fc.createRule(f, newSrcStates, s));
				// (b)
				// convert tree (is possible, because it contains no variables)
				U tree2 = VarTreeOps.<G, V, U> replaceVariables(tree, new LinkedList<U>(), tc);
				Set<Q2> reachableStates = FTAProperties.accessibleStates(ta, tree2);
				for (Q2 q : reachableStates) {
					newRules.add(fc.createRule(f, newSrcStates, c.convert(q)));
				}
			}
			// n>0: add rules (a) f(s,..,s)->s and (b) f(q1,...,qn)->q where
			// 1. qi=pi if the i-th variable is used in hom(f) and qi=s else
			// 2. hom(f)(xi<-pi) ->* q
			else {
				// (a) ; list (s,...,s) of length n
				for (int i = 0; i < n; i++) {
					newSrcStates.add(s);
				}
				newRules.add(fc.createRule(f, newSrcStates, s));
				newSrcStates.clear();
				// (b)
				for (Q2 dest : ta.getStates()) {
					List<Map<Integer, Q2>> replacing = getStatesForReplacing(tree, ta, dest);
					for (Map<Integer, Q2> map : replacing) {
						LinkedList<Q2> stateCombi = new LinkedList<Q2>();
						List<Q1> src = new LinkedList<Q1>();
						for (int i = 0; i < n; i++) {
							if (map.containsKey(i)) {
								stateCombi.add(map.get(i));
								src.add(c.convert(map.get(i)));
							} else {
								stateCombi.add(null);
								src.add(s);
							}
						}

						Set<Q2> reachableStates = FTAProperties.accessibleStatesFromConfigTree(ta,
								substituteStatesInTree(tree, stateCombi, btc));
						if (reachableStates.contains(dest))
							newRules.add(fc.createRule(f, src, c.convert(dest)));
					}
				}
			} // finished with the second case
		}
		// return new tree automaton
		HashSet<Q1> newFinalStates = new HashSet<Q1>();
		for (Q2 qf2 : ta.getFinalStates())
			newFinalStates.add(c.convert(qf2));
		return fc.createFTA(hom.getSrcAlphabet(), newStates, newFinalStates, newRules);
	}

	private static <G extends RankedSymbol, V extends Variable, U extends Tree<G>, Q2 extends State> List<Map<Integer, Q2>> 
	getStatesForReplacing(
			Tree<? extends BiSymbol<G, V>> tree, FTA<G, Q2, ? extends FTARule<G, Q2>> ta, Q2 dest) {
		// if variable
		// System.out.println(tree.getSymbol() + " and replacing " +replacing);
		if (tree.getSymbol().isLeafType()) {
			int nr = tree.getSymbol().asLeafSymbol().getComponentNumber();
			LinkedList<Map<Integer, Q2>> replacing = new LinkedList<Map<Integer, Q2>>();
			Map<Integer, Q2> map = new HashMap<Integer, Q2>();
			map.put(nr, dest);
			replacing.add(map);
			return replacing;
		} else {
			// if symbol
			G symbol = tree.getSymbol().asInnerSymbol();
			// consider symbol rules
			List<Map<Integer, Q2>> set = new LinkedList<Map<Integer, Q2>>();
			for (FTARule<G, Q2> rule : ta.getSymbolRules(symbol)) {
				if (rule.getDestState().equals(dest)) {
					Map<Integer, Q2> nmap = new HashMap<Integer, Q2>();
					List<Map<Integer, Q2>> repl = new LinkedList<Map<Integer, Q2>>();
					repl.add(nmap);
					// recursion
					int j = 0;
					
					for (Tree<? extends BiSymbol<G, V>> sub : tree.getSubTrees()) {
						// System.out.println("Apply on subtree: " +sub + " replacing intern "+replacing);
						List<Map<Integer, Q2>> newrepl = getStatesForReplacing(sub, ta, rule.getSrcStates().get(j));
						// merge newrepl with all already defined things in other maps in repl
						List<Map<Integer, Q2>> temp = new LinkedList<Map<Integer, Q2>>();
						for (Map<Integer, Q2> m1 : repl) {
							for (Map<Integer, Q2> m2 : newrepl) {
								// merge m1 and m2
								boolean consistent = true;
								Map<Integer, Q2> newm = new HashMap<Integer, Q2>(m1);
								for (int k : m2.keySet()) {
									// look whether the maps are consistent,
									if (!newm.containsKey(k)) {
										newm.put(k, m2.get(k));
									} else {
										if (!newm.get(k).equals(m2.get(k)))
											consistent = false;
									}
								}
								if (consistent) {
									temp.add(newm);
								}
							}
						}
						repl = temp;

						j++;
					}
					set.addAll(repl);
				}
			}
			return set;
		}
	}

	/**
	 * Substitutes the variables of a tree by given states. <br>
	 * Helper method for {@link HomOps#applyInverseOnAutomaton}.
	 * 
	 * @param <F>
	 *            type of function symbols occurring in the given variable tree
	 * @param <V>
	 *            type of variables occurring in given variable tree
	 * @param <U>
	 *            type of resulting configuration tree
	 * @param
	 * 			<Q>
	 *            type of states which the variables in the given variable tree shall be replaced by
	 * @param tree
	 *            variable tree whose variable shall be replaced by given states
	 * @param states
	 *            list of states to replace the variables in the variable tree where the position in the list
	 *            corresponds to the number of the variable to be replaced
	 * @param tc
	 *            for the creation of resulting tree(s)
	 * 
	 * @return tree as given, but where each variable is replaced by the corresponding state
	 */
	private static <F extends RankedSymbol, V extends Variable, Q extends State, U extends Tree<BiSymbol<F, Q>>> U substituteStatesInTree(
			Tree<? extends BiSymbol<F, V>> tree, List<Q> states, TreeCreator<BiSymbol<F, Q>, U> tc) {
		// factory.makeConfigurationTree needs a ConfigurationSymbol!
		BiSymbol<F, V> rootSymbol = tree.getSymbol();
		if (rootSymbol.isLeafType()) {
			int varNr = rootSymbol.asLeafSymbol().getComponentNumber();
			return tc.makeTree(new LeafSymbol<F, Q>(states.get(varNr)));
		} else {
			// symbol is a function symbol
			LinkedList<U> subTrees = new LinkedList<U>();
			for (Tree<? extends BiSymbol<F, V>> sub : tree.getSubTrees()) {
				subTrees.add(HomOps.<F, V, Q, U> substituteStatesInTree(sub, states, tc));
			}
			return tc.makeTree(new InnerSymbol<F, Q>(rootSymbol.asInnerSymbol()), subTrees);
		}
	}

	/* section: properties of homomorphisms */

	/**
	 * Returns whether a given homomorphism is linear. <br>
	 * A homomorphism is called linear if in each tree each variable occurs at most once.<br>
	 * <br>
	 * Algorithm:<br>
	 * For each variable tree given by the homomorphism, check whether there occurs some variable at least twice.
	 * 
	 * @param <F>
	 *            type of function symbols in source alphabet of the given homomorphism
	 * @param <G>
	 *            type of function symbols occurring in image trees of the given homomorphism
	 * @param <V>
	 *            type of variables occurring in image trees of the given homomorphism
	 * @param hom
	 *            homomorphism to be analyzed
	 * @return true if and only if the homomorphism is linear, i.e. in each tree each variable occurs at most once
	 */
	public static <F extends RankedSymbol, G extends RankedSymbol, V extends Variable> boolean isLinear(
			Hom<F, G, V> hom) {
		for (F start : hom.getSrcAlphabet()) {
			// all variable trees must be linear
			if (!VarTreeOps.isLinear(hom.imageOf(start)))
				return false;
		}
		// if no double use found, there is no one.
		return true;
	}

	/**
	 * Returns whether the homomorphism is epsilon free. <br>
	 * A homomorphism is called epsilon free if no symbol is mapped just to a variable.<br>
	 * 
	 * @param <F>
	 *            type of function symbols in source alphabet of the given homomorphism
	 * @param <G>
	 *            type of function symbols occurring in image trees of the given homomorphism
	 * @param <V>
	 *            type of variables occurring in image trees of the given homomorphism
	 * @param hom
	 *            homomorphism to be analyzed
	 * @return true if and only if the given homomorphism is epsilon free, i.e. no symbol is mapped just to a variable
	 */
	public static <F extends RankedSymbol, G extends RankedSymbol, V extends Variable> boolean isEpsilonFree(
			Hom<F, G, V> hom) {
		for (F f : hom.getSrcAlphabet()) {
			if (hom.imageOf(f).getSymbol().isLeafType())
				return false;
		}
		return true;
	}

	/**
	 * Returns whether the homomorphism is symbol to symbol.<br>
	 * A homomorphism is called symbol to symbol if for each symbol the height of the image of this symbol is 1. <br>
	 * Note: A symbolToSymbol-Homomorphism can change the label of the input symbol, possibly erase some subtrees and
	 * modify the order of the subtrees.
	 * 
	 * @param <F>
	 *            type of function symbols in source alphabet of the given homomorphism
	 * @param <G>
	 *            type of function symbols occurring in image trees of the given homomorphism
	 * @param <V>
	 *            type of variables occurring in image trees of the given homomorphism
	 * @param hom
	 *            homomorphism to be analyzed
	 * @return true if and only if the given homomorphism is symbol to symbol, i.e. for each symbol the height of the
	 *         image of this symbol is 1.
	 */
	public static <F extends RankedSymbol, G extends RankedSymbol, V extends Variable> boolean isSymbolToSymbol(
			Hom<F, G, V> hom) {

		for (F f : hom.getSrcAlphabet()) {
			if (TreeOps.getHeight(hom.imageOf(f)) != 1)
				return false;
		}
		return true;
	}

	/**
	 * Returns whether the homomorphism is complete. <br>
	 * A homomorphism is called complete if for each symbol with arity n, the image of f contains all variables from 0
	 * to n-1. <br>
	 * 
	 * @param <F>
	 *            type of function symbols in the source alphabet of the given homomorphism
	 * @param <G>
	 *            type of function symbols occurring in the image trees of the given homomorphism
	 * @param <V>
	 *            type of variables occurring in the image trees of the given homomorphism
	 * @param hom
	 *            homomorphism to be analyzed
	 * @return true if and only if the given homomorphism is complete, i.e. for each symbol with arity n, the image of f
	 *         contains all variables from 0 to n-1
	 */
	public static <F extends RankedSymbol, G extends RankedSymbol, V extends Variable> boolean isComplete(
			Hom<F, G, V> hom) {
		for (F f : hom.getSrcAlphabet()) {
			for (int i = 0; i < f.getArity(); i++) {
				if (!VarTreeOps.containsVariable(hom.imageOf(f), i)) {
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * Returns whether this homomorphism is delabeling. <br>
	 * A homomorphism is called delabeling if it is complete, linear and symbol to symbol. <br>
	 * Note: A delabeling homomorphism only changes the label of the input symbol and possibly the order of the
	 * subtrees.<br>
	 * 
	 * @param <F>
	 *            type of function symbols in the source alphabet of the given homomorphism
	 * @param <G>
	 *            type of function symbols occurring in the image trees of the given homomorphism
	 * @param <V>
	 *            type of variables occurring in the image trees of the given homomorphism
	 * @param hom
	 *            homomorphism to be analyzed
	 * @return true if and only if the given homomorphism is delabeling, i.e. it is complete, linear and symbol to
	 *         symbol
	 */
	public static <F extends RankedSymbol, G extends RankedSymbol, V extends Variable> boolean isDelabeling(
			Hom<F, G, V> hom) {
		return isComplete(hom) && isSymbolToSymbol(hom) && isLinear(hom);
	}

	/**
	 * Returns whether a homomorphism is alphabetic. <br>
	 * A homomorphism is called alphabetic if for each symbol f the image of f is of the form g(x_0,...,x_{n-1}) where g
	 * is a symbol of the destination alphabet.<br>
	 * 
	 * @param <F>
	 *            type of function symbols in the source alphabet of the given homomorphism
	 * @param <G>
	 *            type of function symbols occurring in the image trees of the given homomorphism
	 * @param <V>
	 *            type of variables occurring in the image trees of the given homomorphism
	 * @param hom
	 *            homomorphism to be analyzed
	 * @return true if and only if the given homomorphism is alphabetic, i.e. for each symbol f the image of f is of the
	 *         form g(x_0, ...x_{n-1}) where g is a symbol of the destination alphabet
	 */
	public static <F extends RankedSymbol, G extends RankedSymbol, V extends Variable> boolean isAlphabetic(
			Hom<F, G, V> hom) {
		for (F f : hom.getSrcAlphabet()) {
			int i = 0;
			for (Tree<? extends BiSymbol<G, V>> sub : hom.imageOf(f).getSubTrees()) {
				if (!((sub.getSymbol().isLeafType()) && (sub.getSymbol().asLeafSymbol().getComponentNumber() == i))) {
					return false;
				}
				i++;
			}
		}
		return true;
	}
}
