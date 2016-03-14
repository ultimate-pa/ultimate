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
package de.uni_muenster.cs.sev.lethal.treeautomata.common;

import de.uni_muenster.cs.sev.lethal.grammars.RTG;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;
import de.uni_muenster.cs.sev.lethal.utils.Converter;
import de.uni_muenster.cs.sev.lethal.utils.Pair;

/**
 * Implements the basic functionalities of a finite tree automaton. <br>
 * It can be easily extended.
 * 
 * @param <F> type of ranked symbols in the alphabet the finite tree automaton works on
 * @param <Q> type of states of the finite tree automaton
 * @param <R> type of rules used in the finite tree automaton
 * 
 * @see FTA
 * 
 * @author Dorothea, Irene, Martin
 */
public abstract class AbstractFTA<F extends RankedSymbol, Q extends State, R extends FTARule<F,Q>> implements FTA<F,Q,R> {

	/**
	 * Set of all states occurring in the finite tree automaton.
	 * @see FTA#getStates()
	 */
	protected Set<Q> states;

	/**
	 * Set of final states, where the finite tree automaton accepts.
	 * @see FTA#getFinalStates()
	 */
	protected Set<Q> finalStates;

	/**
	 * Rules of the finite tree automaton, saved in an efficient way.
	 * @see FTA#getRules()
	 */
	protected FTARuleSet<F,Q,R> rules;

	/**
	 * Alphabet of the regular tree language the finite tree automaton represents.
	 * @see FTA#getAlphabet()
	 */
	protected Set<F> alphabet;


	/**
	 * Indicates whether the alphabet has been calculated completely, i.e. from the rules.
	 */
	protected boolean alphComplete = false;


	/**
	 * Indicates whether the states have been calculated completely, i.e. from the rules.
	 */
	protected boolean statesComplete = false;


	/**
	 * Creates an empty finite tree automaton without any states and rules.
	 */
	protected AbstractFTA() {
		states = new HashSet<Q>();
		finalStates = new HashSet<Q>();
		rules = new SimpleFTARuleSet<F,Q,R>();
		alphabet = new HashSet<F>();
	}

	/**
	 * Initializes this finite tree automaton with given rules and final states. The
	 * invariants are preserved. Note, that the rules are not copied into new instances
	 * of type R, so that the type of the incoming rules can be arbitrary. The state set
	 * and the alphabet are set to null because they are not needed until the first call
	 * of the corresponding getter method.
	 * @param rules2 rules which define the finite tree automaton
	 * @param finalStates2 final states which define the finite tree automaton
	 */
	protected void init(Collection<? extends FTARule<F,Q>> rules2, Collection<Q> finalStates2) {
		states = null;
		finalStates = new HashSet<Q>(finalStates2);
		rules = new SimpleFTARuleSet<F,Q,R>();
		alphabet = null;
		for (FTARule<F,Q> rule: rules2)
			rules.add(createRule(rule.getSymbol(), rule.getSrcStates(), rule.getDestState()));
	}

	/**
	 * Initializes the state set of this finite tree automaton, preserving the invariants.
	 * In particular: <br>
	 * <ul>
	 * <li> finalStates is a subset of states. </li>
	 * <li> states contains every state occurring in a rule of this finite tree automaton. </li>
	 * </ul>
	 */
	protected void computeStatesFromRules() {
		if (states==null)
			states = new HashSet<Q>(finalStates);
		for (R rule: rules) {
			states.add(rule.getDestState());
			states.addAll(rule.getSrcStates());
		}
		statesComplete = true;
	}

	/**
	 * Initializes the alphabet of this finite tree automaton, preserving the invariants.
	 * In particular, alphabet contains every symbol occurring in a rule of this finite tree automaton.
	 */
	protected void computeAlphabetFromRules() {
		if (alphabet==null)
			alphabet = new HashSet<F>();
		for (R rule: rules)
			alphabet.add(rule.getSymbol());
		alphComplete = true;
	}


	/**
	 * Creates a new finite tree automaton from rules and final states.<br>
	 * States and alphabet are calculated from the rules and final states.
	 *
	 * @param rules2 rules for the finite tree automaton, see also {@link FTA#getRules()}
	 * @param finalStates2 final states for the finite tree automaton, see also {@link FTA#getRules()}
	 **/
	public AbstractFTA(Collection<? extends FTARule<F,Q>> rules2, Collection<Q> finalStates2) {
		if (rules2 == null) throw new IllegalArgumentException("AbstractFTA(): rules2 must not be null.");
		if (finalStates2 == null) throw new IllegalArgumentException("AbstractFTA(): finalStates2ust not be null.");
		
		init(rules2, new HashSet<Q>(finalStates2));
	}


	/**
	 * Creates a new finite tree automaton from rules, final states and additional epsilon rules.
	 * The epsilon rules are eliminated and thus converted into normal rules.
	 * @param newRules rules of the new finite tree automaton
	 * @param newEpsRules epsilon rules of the new finite tree automaton
	 * @param newFinals final states of the new finite tree automaton
	 */
	public AbstractFTA(Collection<? extends FTARule<F,Q>> newRules, Collection<? extends FTAEpsRule<Q>> newEpsRules, Collection<Q> newFinals) {
		if (newRules == null) throw new IllegalArgumentException("AbstractFTA(): newRules must not be empty.");
		if (newEpsRules == null)  throw new IllegalArgumentException("AbstractFTA(): newEpsRules must not be null.");
		
		init(FTACreator.eliminateEpsilonRules(newRules, newEpsRules), newFinals);
	}

	/**
	 * Creates a new finite tree automaton from the given parameters.
	 * @param newAlphabet alphabet of the new finite tree automaton
	 * @param newStates states of the new finite tree automaton
	 * @param newFinalStates final states of the new finite tree automaton
	 * @param newRules rules of the new finite tree automaton
	 */
	public AbstractFTA(Collection<F> newAlphabet, Collection<Q> newStates, Collection<Q> newFinalStates, Collection<? extends FTARule<F,Q>> newRules) {
		if (newAlphabet == null)    throw new IllegalArgumentException("AbstractFTA(): newAlphabet must not be null.");
		if (newStates == null)      throw new IllegalArgumentException("AbstractFTA(): newStates must not be null.");
		if (newFinalStates == null) throw new IllegalArgumentException("AbstractFTA(): newFinalStates must not be null.");
		if (newRules == null)       throw new IllegalArgumentException("AbstractFTA(): newRules must not be null.");
	
		init(newRules, new HashSet<Q>(newFinalStates));
		states = new HashSet<Q>(newStates);
		alphabet = new HashSet<F>(newAlphabet);
		states.addAll(newStates);
		alphabet.addAll(newAlphabet);
	}




	/**
	 * Creates a new finite tree automaton from a given arbitrary finite tree automaton
	 * with the right state and symbol types. The necessary data is simply copied.
	 * @param fta finite tree automaton which the new instance shall be created out of
	 */
	public AbstractFTA(FTA<F,Q,? extends FTARule<F,Q>> fta) {
		this(fta.getAlphabet(), fta.getStates(), fta.getFinalStates(), fta.getRules());
	}

	/**
	 * Creates a new AbstractFTA out of an arbitrary regular tree grammar.
	 * @param grammar regular tree grammar out of which the new AbstractFTA is to be created
	 * @param stateBuilder creator object, which is used to create states out of non-terminals
	 * and trees in the normalization process
	 * @param <P> type of non-terminals occurring in the grammar rules 
	 * @see FTACreator#makeFTAFromGrammar
	 */
	public <P extends State> AbstractFTA(RTG<F,P> grammar, Converter<Object,Q> stateBuilder) {
		if (grammar == null) throw new IllegalArgumentException("AbstractFTA(): grammar must not be null.");
		if (stateBuilder == null) throw new IllegalArgumentException("AbstractFTA(): stateBuilder must not be null.");
		Pair<Collection<FTARule<F, Q>>, Collection<Q>> ftaFromGrammar = FTACreator.makeFTAFromGrammar(grammar.getStartSymbols(), grammar.getGrammarRules(), stateBuilder);
		init(ftaFromGrammar.getFirst(), ftaFromGrammar.getSecond());
	}


	/**
	 * Given a source symbol, source states and destination states, creates a new rule
	 * with these data, which has the appropriate type.
	 * @param srcSymbol source symbol of the new rule
	 * @param srcStates source states of the new rule
	 * @param destState destination state of the new rule
	 * @return finite tree automaton rule of appropriate type with given source symbol,
	 * source states and destination state
	 */
	protected abstract R createRule(F srcSymbol, List<Q> srcStates, Q destState);

	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA#getAlphabet()
	 */
	@Override
	public Set<F> getAlphabet() {
		if (!alphComplete) {
			computeAlphabetFromRules();
		}
		return Collections.unmodifiableSet(alphabet);
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA#getFinalStates()
	 */
	@Override
	public Set<Q> getFinalStates() {
		return Collections.unmodifiableSet(finalStates);
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA#getRules()
	 */
	@Override
	public Set<R> getRules() {
		return Collections.unmodifiableSet(rules);
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA#getStates()
	 */
	@Override
	public Set<Q> getStates() {
		if (!statesComplete) {
			computeStatesFromRules();
		}
		return Collections.unmodifiableSet(states);
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.FTA#getSymbolRules
	 */
	@Override
	public Set<? extends R> getSymbolRules(F f) {
		return rules.getSymbolRules(f);
	}

	/**
	 * Generates a string representation of the rules; final states are specially marked with '!'
	 * @return a string representation of the rules
	 */
	public String rulesToString() {
		return FTAOps.rulesToString(this);
	}

	/**
	 * Annotates a tree and all its subtrees with states accessible 
	 * on this tree according to the rules in the finite tree automaton.<br>
	 * Every subtree of s gets a set of states, which can be reached with this subtree
	 * at the root of this subtree.
	 *
	 * @param t tree to be annotated
	 * @return a map which assigns each tree contained in t the set of states which
	 * the automaton can annotate this tree with.
	 */
	public Map<Tree<F>, Set<Q>> annotateTreeWithStates(Tree<F> t) {
		return FTAOps.annotateTreeWithStates(this, t);
	}

	/**
	 * Returns whether a given tree is accepted by this finite tree automaton
	 * @param t tree to be checked
	 * @return true if the given tree is accepted by this finite tree automaton,
	 * false otherwise
	 */
	public boolean decide(Tree<F> t) {
		return FTAProperties.decide(this, t);
	}

	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "FTA: Rules:\n" + rulesToString() + "Final States:" + this.finalStates.toString();
	}

}
