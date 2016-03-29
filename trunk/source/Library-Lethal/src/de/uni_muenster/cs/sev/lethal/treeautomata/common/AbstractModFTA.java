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
package de.uni_muenster.cs.sev.lethal.treeautomata.common;

import de.uni_muenster.cs.sev.lethal.grammars.RTG;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTAEpsRule;
import de.uni_muenster.cs.sev.lethal.utils.Converter;


/**
 * Standard implementation for modifiable finite tree automata, which uses sets for
 * states and symbols and {@link FTARuleSet} for the rules. Since the rule type is
 * variable, rule creation of appropriate type is left to the sub types. Thus, this
 * class is abstract.
 * 
 * @param <F> symbol type used in this finite tree automaton
 * @param <Q> state type used in this finite tree automaton
 * @param <R> rule type used in this finite tree automaton
 * 
 * @see ModifiableFTA
 * 
 * @author Dorothea, Irene, Martin
 */
public abstract class AbstractModFTA<F extends RankedSymbol, Q extends State, R extends FTARule<F,Q>> extends AbstractFTA<F,Q,R> implements ModifiableFTA<F,Q,R> {
	
	/**
	 * The additional epsilon rules of this finite tree automaton. They are
	 * eliminated before 
	 */
	protected ArrayList<FTAEpsRule<Q>> epsRules = new ArrayList<FTAEpsRule<Q>>();
	
	/**
	 * Creates a new finite tree automaton from rules, final states and additional epsilon rules.
	 * The epsilon rules are eliminated and thus converted into normal rules. It is possible, that
	 * the new finite tree automaton has more final states than 
	 * @param newRules rules of the new finite tree automaton
	 * @param newEpsRules epsilon rules of the new finite tree automaton
	 * @param newFinals final states of the new finite tree automaton
	 */
	public AbstractModFTA(Collection<? extends FTARule<F, Q>> newRules,
			Collection<? extends FTAEpsRule<Q>> newEpsRules,
			Collection<Q> newFinals) {
		super(newRules, newEpsRules, newFinals);
	}


	/**
	 * Creates an empty finite tree automaton without any states and rules.
	 */
	public AbstractModFTA() {
		super();
	}


	/**
	 * Creates a new finite tree automaton from rules and final states.<br>
	 * States and alphabet are calculated from the rules and final states.
	 *
	 * @param rules2 rules for the finite tree automaton, see also {@link FTA#getRules()}
	 * @param finalStates2 final states for the finite tree automaton, see also {@link FTA#getRules()}
	 **/
	public AbstractModFTA(Collection<? extends FTARule<F,Q>> rules2, Collection<Q> finalStates2) {
		super(rules2,finalStates2);
	}


	/**
	 * Creates a new finite tree automaton from the given parameters.
	 * @param newAlphabet alphabet of the new finite tree automaton
	 * @param newStates states of the new finite tree automaton
	 * @param newFinalStates final states of the new finite tree automaton
	 * @param newRules rules of the new finite tree automaton
	 */
	public AbstractModFTA(Collection<F> newAlphabet, Collection<Q> newStates, Collection<Q> newFinalStates, Collection<? extends FTARule<F,Q>> newRules) {
		super(newAlphabet, newStates, newFinalStates, newRules);
	}
	
	/**
	 * Creates a new AbstractModFTA out of an arbitrary finite tree automaton.
	 * @param fta finite tree automaton out of which the new AbstractModFTA is to be created
	 */
	public AbstractModFTA(FTA<F, Q, ? extends FTARule<F, Q>> fta) {
		super(fta);
	}


	/**
	 * Creates a new AbstractModFTA out of an arbitrary regular tree grammar.
	 * @param grammar regular tree grammar out of which the new AbstractModFTA is to be created
	 * @param stateBuilder creator object, which is used to create states out of non-terminals
	 * and trees in the normalization process
	 * @param <P> type of non-terminals occurring in the grammar rules 
	 * @see FTACreator#makeFTAFromGrammar
	 */
	public <P extends State> AbstractModFTA(RTG<F, P> grammar, Converter<Object, Q> stateBuilder) {
		super(grammar, stateBuilder);
	}
	
	/**
	 * Returns the rules of this finite tree automaton. If there are epsilon rules,
	 * they are eliminated first.
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.AbstractFTA#getRules()
	 */
	@Override
	public Set<R> getRules() {
		if (!epsRules.isEmpty())
			eliminateAddedEpsilonRules();
		return super.getRules();
	}
	
	
	/**
	 * Returns all rules, which have the specified symbol as their symbol. If there are
	 * epsilon rules, they are eliminated first.
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.AbstractFTA#getSymbolRules
	 */
	@Override
	public Set<? extends R> getSymbolRules(F f) {
		if (!epsRules.isEmpty())
			eliminateAddedEpsilonRules();
		return super.getSymbolRules(f);
	}
	
	/**
	 * Eliminates the epsilon rules collected so far by {@link #addEpsilonRule}.
	 * Used by getRules() and getFinalStates()
	 */
	protected void eliminateAddedEpsilonRules() {
		for (FTARule<F,Q> r: FTACreator.eliminateEpsilonRules(rules, epsRules))
			addRule(r.getSymbol(), r.getSrcStates(), r.getDestState());
		for (Q qf: finalStates)
			addToFinals(qf);
		epsRules.clear();
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.ModifiableFTA#addState
	 */
	@Override
	public void addState(Q state) {
		if (states==null)
			states = new HashSet<Q>();
		states.add(state);
	}
	
	/**
	 * Adds multiple states to this finite tree automaton. 
	 * @param states states to be added
	 */
	public void addStates(Collection<? extends Q> states) {
		if (this.states==null)
			this.states = new HashSet<Q>();
		this.states.addAll(states);
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.ModifiableFTA#addSymbol
	 */
	@Override
	public void addSymbol(F f) {
		if (alphabet==null)
			alphabet = new HashSet<F>();
		alphabet.add(f);
	}

	/**
	 * Adds multiple symbols to this finite tree automaton
	 * @param symbols symbols to be added
	 */
	public void addSymbols(Collection<? extends F> symbols) {
		if (alphabet==null)
			alphabet = new HashSet<F>();
		alphabet.addAll(symbols);
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.ModifiableFTA#addRule
	 */
	@Override
	public void addRule(F f, List<Q> srcStates, Q destState) {
		rules.add(createRule(f,srcStates,destState));
		addStates(srcStates);
		addState(destState);
		addSymbol(f);
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.ModifiableFTA#addToFinals
	 */
	@Override
	public void addToFinals(Q state) {
		finalStates.add(state);

		//preserve invariants
		states.add(state);
	}

	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.ModifiableFTA#removeRule
	 */
	@Override
	public boolean removeRule(FTARule<F,Q> rule) {
		return rules.remove(rule);
	}
	
	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.ModifiableFTA#removeFromFinals
	 */
	@Override
	public void removeFromFinals(Q state) {
		finalStates.remove(state);
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.ModifiableFTA#removeState
	 */
	@Override
	public void removeState(Q state, boolean cascade) {
		if (states==null)
			return;
		
		LinkedList<R> toDelete = new LinkedList<R>();
		for (R rule: rules) {
			if (rule.getSrcStates().contains(state) || rule.getDestState().equals(state)) {
				if (cascade)
					toDelete.add(rule);
				else
					throw new StillInUseException("removeState: State to be removed is still used in a rule!");
			}
		}
		rules.removeAll(toDelete);
		states.remove(state);
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.ModifiableFTA#removeSymbol
	 */
	@Override
	public void removeSymbol(F symbol, boolean cascade) {
		if (alphabet==null)
			return;
		Set<? extends R> symbolRules = getSymbolRules(symbol);
		if (!symbolRules.isEmpty())
			if (cascade)
				rules.removeAll(symbolRules);
			else
				throw new StillInUseException("removeSymbol: Symbol to be removed is still used in a rule!");
		alphabet.remove(symbol);
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.treeautomata.common.ModifiableFTA#addEpsilonRule
	 */
	@Override
	public void addEpsilonRule(Q qsrc, Q qdest) {
		epsRules.add(new GenFTAEpsRule<Q>(qsrc,qdest));
		states.add(qsrc);
		states.add(qdest);
	}

	
}
