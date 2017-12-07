/*
 * Copyright (C) 2016 Mostafa M.A. (mostafa.amin93@gmail.com)
 * Copyright (C) 2014-2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.tree;

import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.tree.visualization.TreeAutomatonToUltimateModel;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

/**
 * Interface to create a tree automaton
 * 
 * @author mostafa.amin93@gmail.com, grugelt@uni-freiburg.de
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 * 
 * @param <LETTER>
 *            symbol
 * @param <STATE>
 *            state
 */
public interface ITreeAutomatonBU<LETTER extends IRankedLetter, STATE> extends IAutomaton<LETTER, STATE> {

	/***
	 * Add a new rule to the automaton.
	 * 
	 * @param rule
	 */
	void addRule(final TreeAutomatonRule<LETTER, STATE> rule);

	/**
	 * Gets the amount of rules contained in this automaton. This operation operates
	 * in O(1), i.e. it is fast.
	 * 
	 * @return The amount of rules contained in this automaton
	 */
	int getAmountOfRules();

	// /**
	// * @return a set of all initial states in the automaton.
	// */
	// Set<STATE> getInitialStates();

	/**
	 * @param state
	 * @return a map that denotes all the lists of rules that goes to given state.
	 */
	//Map<LETTER, Iterable<List<STATE>>> getPredecessors(final STATE state);

	// /**
	// * @param state
	// * @return true, if given state is initial.
	// */letter
	// boolean isInitialState(final STATE state);

	/**
	 * @param state
	 * @param letter
	 * @return Given a letter and a state, get all rules that goes to the given
	 *         state using the given letter.
	 */
	//Iterable<List<STATE>> getPredecessors(final STATE state, final LETTER letter);

	/**
	 * 
	 * @return Get the rules of the automaton.
	 */
	//Iterable<TreeAutomatonRule<LETTER, STATE>> getRules();
	
	/**
	 * 
	 * @return iterable of all source lists occuring in some rules.
	 */
	Iterable<List<STATE>> getSourceCombinations();

	/***
	 * Complement the set of final states
	 */
	void complementFinals();
	
	/**
	 * @return a set of all the states in the automaton.
	 */
	Set<STATE> getStates();

	/**
	 * @param states
	 * @return a list of all successor states for given states.
	 */
	Iterable<TreeAutomatonRule<LETTER, STATE>> getSuccessors(final List<STATE> states);
	
	/***
	 * @param letter
	 * @return
	 */
	Iterable<TreeAutomatonRule<LETTER, STATE>> getSuccessors(final LETTER letter);

	/**
	 * @param states
	 * @param letter
	 * @return a list of all successors for given states and given letter.
	 */
	Iterable<STATE> getSuccessors(final List<STATE> states, final LETTER letter);

	/**
	 * @param state
	 * @return true, if given state is final.
	 */
	boolean isFinalState(final STATE state);

	@Override
	default IElement transformToUltimateModel(final AutomataLibraryServices services)
			throws AutomataOperationCanceledException {
		return new TreeAutomatonToUltimateModel<LETTER, STATE>().transformToUltimateModel(this);
	}
}
