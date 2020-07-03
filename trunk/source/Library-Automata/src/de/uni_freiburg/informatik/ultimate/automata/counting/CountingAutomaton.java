/*
 * Copyright (C) 2020 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.automata.counting;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;


/**
 * Data structure for Counting Automata
 *
 * @author Marcel Ebbinghaus
 * @author who is the author?
 */
public class CountingAutomaton<LETTER, STATE> implements IAutomaton<LETTER, STATE> {

	protected final AutomataLibraryServices mServices;
	
	private Set<LETTER> mAlphabet;
	private Set<STATE> mStates;
	private ArrayList<Counter> mCounter;
	private Map<STATE, InitialCondition> mInitialConditions;
	private Map<STATE, FinalCondition> mFinalConditions;
	private Map<STATE, ArrayList<Transition<LETTER, STATE>>> mTransitions;
	
	/**
	private Set<LETTER> mAlphabet;
	private Set<STATE> mStates;
	private ArrayList<Counter> mCounter;
	private Map<STATE, ArrayList<ArrayList<Guard>>> mInitialConditions;
	private Map<STATE, ArrayList<ArrayList<Guard>>> mFinalConditions;
	private Map<STATE, ArrayList<Transition<LETTER, STATE>>> mTransitions;
	*/

	public CountingAutomaton(final AutomataLibraryServices services) {
		super();
		mServices = services;
	}
	
	public CountingAutomaton(final AutomataLibraryServices services,
			Set<LETTER> alphabet,
			Set<STATE> states,
			ArrayList<Counter> counter, 
			Map<STATE, InitialCondition> initialConditions,
			Map<STATE, FinalCondition> finalConditions,
			Map<STATE, ArrayList<Transition<LETTER, STATE>>> transitions) {
		super();
		mServices = services;
		mAlphabet = alphabet;
		mStates = states;
		mCounter = counter;
		mInitialConditions = initialConditions;
		mFinalConditions = finalConditions;
		mTransitions = transitions; 
	}
	
	/**
	public CountingAutomaton(final AutomataLibraryServices services,
			Set<LETTER> alphabet,
			Set<STATE> states,
			ArrayList<Counter> counter, 
			Map<STATE,ArrayList<ArrayList<Guard>>> initialConditions,
			Map<STATE, ArrayList<ArrayList<Guard>>> finalConditions,
			Map<STATE, ArrayList<Transition<LETTER, STATE>>> transitions) {
		super();
		mServices = services;
		mAlphabet = alphabet;
		mStates = states;
		mCounter = counter;
		mInitialConditions = initialConditions;
		mFinalConditions = finalConditions;
		mTransitions = transitions;
	}
	*/

	@Override
	public Set<LETTER> getAlphabet() {
		return mAlphabet;
	}
	
	public Set<STATE> getStates() {
		return mStates;
	}
	
	public ArrayList<Counter> getCounter() {
		return mCounter;
	}

	public Map<STATE, InitialCondition> getInitialConditions() {
		return mInitialConditions;
	}
	
	public Map<STATE, FinalCondition> getFinalConditions(){
		return mFinalConditions;
	}
	/**
	public Map<STATE,ArrayList<ArrayList<Guard>>> getInitialConditions() {
		return mInitialConditions;
	}
	
	public Map<STATE,ArrayList<ArrayList<Guard>>> getFinalConditions() {
		return mFinalConditions;
	}
	*/
	
	public Map<STATE, ArrayList<Transition<LETTER, STATE>>> getTransitions() {
		return mTransitions;
	}
	
	public void addTransition(STATE preState, Transition<LETTER, STATE> transition) {
		ArrayList<Transition<LETTER, STATE>> currentTransitions = mTransitions.get(preState);
		currentTransitions.add(transition);
		mTransitions.put(preState, currentTransitions);
	}
	
	public void addInitialCondition(STATE state, ArrayList<ArrayList<Guard>> conditionDNF) {
		InitialCondition currentInitialCondition = mInitialConditions.get(state);
		ConjunctGuards conjunction = new ConjunctGuards(currentInitialCondition.getCondition(), conditionDNF);
		InitialCondition newInitialCondition = new InitialCondition(conjunction.getResult());
		mInitialConditions.put(state, newInitialCondition);
	}
	
	public void addFinalCondition(STATE state, ArrayList<ArrayList<Guard>> conditionDNF) {
		FinalCondition currentFinalCondition = mFinalConditions.get(state);
		ConjunctGuards conjunction = new ConjunctGuards(currentFinalCondition.getCondition(), conditionDNF);
		FinalCondition newFinalCondition = new FinalCondition(conjunction.getResult());
		mFinalConditions.put(state, newFinalCondition);
	}
	
	/**
	public void addInitialCondition(STATE state, ArrayList<ArrayList<Guard>> conditionDNF) {
		ArrayList<ArrayList<Guard>> currentInitialConditions = mInitialConditions.get(state);
		ConjunctGuards conjunction = new ConjunctGuards(currentInitialConditions, conditionDNF);
		mInitialConditions.put(state, conjunction.getResult());
	}
	
	public void addFinalCondition(STATE state, ArrayList<ArrayList<Guard>> conditionDNF) {
		ArrayList<ArrayList<Guard>> currentFinalConditions = mFinalConditions.get(state);
		ConjunctGuards conjunction = new ConjunctGuards(currentFinalConditions, conditionDNF);
		mFinalConditions.put(state, conjunction.getResult());
	}
	*/
	
	public CountingAutomaton<LETTER, STATE> copyCountingAutomaton() {
		
		ArrayList<Counter> counterListCopy = new ArrayList<Counter>();
		for (Counter counter : mCounter) {
			counterListCopy.add(counter.copyCounter());
		}
		
		Map<STATE, InitialCondition> initialConditionsCopy = new HashMap<STATE, InitialCondition>();
		Map<STATE, FinalCondition> finalConditionsCopy = new HashMap<STATE, FinalCondition>();
		Map<STATE, ArrayList<Transition<LETTER, STATE>>> transitionsCopy = new HashMap<STATE, ArrayList<Transition<LETTER, STATE>>>();
		for (STATE state : mStates) {
			InitialCondition initialConditionCopy = mInitialConditions.get(state).copyInitialCondition();
			initialConditionsCopy.put(state, initialConditionCopy);
			FinalCondition finalConditionCopy = mFinalConditions.get(state).copyFinalCondition();
			finalConditionsCopy.put(state, finalConditionCopy);
			ArrayList<Transition<LETTER, STATE>> transitionListCopy = new ArrayList<Transition<LETTER, STATE>>();
			for (Transition<LETTER, STATE> transition : mTransitions.get(state)) {
				transitionListCopy.add(transition.copyTransition());
			}
			transitionsCopy.put(state, transitionListCopy);
		}
		
		
		CountingAutomaton<LETTER, STATE> copy = new CountingAutomaton<LETTER, STATE>(
				mServices, 
				mAlphabet, 
				mStates, 
				counterListCopy, 
				initialConditionsCopy, 
				finalConditionsCopy, 
				transitionsCopy);
		return copy;
	}
	
	@Override
	public int size() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public String sizeInformation() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IElement transformToUltimateModel(final AutomataLibraryServices services)
			throws AutomataOperationCanceledException {
		// TODO Auto-generated method stub
		return null;
	}


	@Override
	public String toString() {
		return (AutomatonDefinitionPrinter.toString(mServices, "ca", this));
	}
}