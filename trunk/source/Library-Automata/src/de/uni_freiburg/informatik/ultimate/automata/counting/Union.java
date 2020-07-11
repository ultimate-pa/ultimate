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
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Union method for Counting Automata
 *
 * @author Marcel Ebbinghaus
 * @author who is the author?
 */

public class Union<LETTER, STATE, CRSF extends IStateFactory<STATE>> implements IOperation<LETTER, STATE, CRSF> {

	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	private final CountingAutomaton<LETTER, STATE> mFstOperand;
	private final CountingAutomaton<LETTER, STATE> mSndOperand;
	private final STATE mNewInitialState;
	private final CountingAutomaton<LETTER, STATE> mResult;
	private final IIntersectionStateFactory<STATE> mStateFactory;


	public Union(
			final AutomataLibraryServices services, 
			final IIntersectionStateFactory<STATE> stateFactory,
			final CountingAutomaton<LETTER, STATE> fstOperand,
			final CountingAutomaton<LETTER, STATE> sndOperand,
			final STATE newInitialState) throws AutomataLibraryException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(this.getClass());
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;
		mNewInitialState = newInitialState;
		mStateFactory = stateFactory;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		mResult = computeResult();

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	private CountingAutomaton<LETTER, STATE> computeResult() {
		
		Set<LETTER> unionAlphabet = mFstOperand.getAlphabet();
		ArrayList<Counter> unionCounter = new ArrayList<Counter>();
		for (Counter counter : mFstOperand.getCounter()) {
			unionCounter.add(counter.copyCounter());
		}
		for (Counter counter : mSndOperand.getCounter()) {
			unionCounter.add(counter.copyCounter());
		}
		Set<STATE> unionStates = new HashSet<STATE>();
		unionStates.addAll(mFstOperand.getStates());
		unionStates.addAll(mSndOperand.getStates());
		unionStates.add(mNewInitialState);
		Map<STATE, InitialCondition> unionInitialConditions = new HashMap<STATE, InitialCondition>();
		Map<STATE, FinalCondition> unionFinalConditions = new HashMap<STATE, FinalCondition>();
		Map<STATE, ArrayList<Transition<LETTER, STATE>>> unionTransitions = new HashMap<STATE, ArrayList<Transition<LETTER, STATE>>>();
		
		//initialConditions
		Guard newInitialGuard = new Guard();
		newInitialGuard.changeTermType(TermType.TRUE);
		ArrayList<Guard> newGuardList = new ArrayList<Guard>();
		newGuardList.add(newInitialGuard);
		ArrayList<ArrayList<Guard>> newInitialConditionList = new ArrayList<ArrayList<Guard>>();
		newInitialConditionList.add(newGuardList);
		unionInitialConditions.put(mNewInitialState, new InitialCondition(newInitialConditionList));
		addNewUnionInitialConditions(mFstOperand, unionInitialConditions);
		addNewUnionInitialConditions(mSndOperand, unionInitialConditions);
		
		//finalConditions
		ArrayList<ArrayList<Guard>> newFinalConditionList = new ArrayList<ArrayList<Guard>>();
		addNewUnionFinalConditions(mFstOperand, newFinalConditionList, unionFinalConditions);
		addNewUnionFinalConditions(mSndOperand, newFinalConditionList, unionFinalConditions);
		
		//construct finalCondition == false, if there were no states in mFstOperand and mSndOperand which are initial and final at once
		if (newFinalConditionList.size() == 0) {
			
			Guard newGuardFalse = new Guard();
			newGuardFalse.changeTermType(TermType.FALSE);
			ArrayList<Guard> guardList = new ArrayList<Guard>();
			guardList.add(newGuardFalse);
			newFinalConditionList.add(guardList);
		}
		unionFinalConditions.put(mNewInitialState, new FinalCondition(newFinalConditionList));
		
		//transitions
		ArrayList<Transition<LETTER, STATE>> newTransitions = new ArrayList<Transition<LETTER, STATE>>();
		addNewUnionTransitions(mFstOperand, newTransitions, unionTransitions);
		addNewUnionTransitions(mSndOperand, newTransitions, unionTransitions);
		unionTransitions.put(mNewInitialState, newTransitions);
		
		//result
		CountingAutomaton<LETTER, STATE> resultAutomaton = new CountingAutomaton<LETTER, STATE>(
				mServices,
				unionAlphabet,
				unionStates,
				unionCounter,
				unionInitialConditions,
				unionFinalConditions,
				unionTransitions);
		return resultAutomaton;
	}
	
	private void addNewUnionInitialConditions (CountingAutomaton<LETTER, STATE> automaton, Map<STATE, InitialCondition> unionInitialConditions) {
		
		for (STATE state : automaton.getStates()) {
			
			Guard newInitialGuard = new Guard();
			newInitialGuard.changeTermType(TermType.FALSE);
			ArrayList<Guard> newGuardList = new ArrayList<Guard>();
			newGuardList.add(newInitialGuard);
			ArrayList<ArrayList<Guard>> newInitialConditionList = new ArrayList<ArrayList<Guard>>();
			newInitialConditionList.add(newGuardList);
			unionInitialConditions.put(state, new InitialCondition(newInitialConditionList));
		}
	}
	
	private void addNewUnionFinalConditions (CountingAutomaton<LETTER, STATE> automaton, ArrayList<ArrayList<Guard>> newFinalConditionList, Map<STATE, FinalCondition> unionFinalConditions) {
		
		for (STATE state : automaton.getStates()) {
			
			unionFinalConditions.put(state, automaton.getFinalConditions().get(state).copyFinalCondition());
			
			if (automaton.getInitialConditions().get(state).getCondition().get(0).get(0).getTermType() != TermType.FALSE &&
					automaton.getFinalConditions().get(state).getCondition().get(0).get(0).getTermType() != TermType.FALSE) {
				
				ConjunctGuards conjunction = new ConjunctGuards(
						automaton.getFinalConditions().get(state).copyFinalCondition().getCondition(), 
						automaton.getInitialConditions().get(state).copyInitialCondition().getCondition());
				newFinalConditionList.addAll(conjunction.getResult());
			}
		}
	}
	
	private void addNewUnionTransitions (CountingAutomaton<LETTER, STATE> automaton, ArrayList<Transition<LETTER, STATE>> newTransitions, Map<STATE, ArrayList<Transition<LETTER, STATE>>> unionTransitions) {
		
			for (STATE state : automaton.getStates()) {
			
				ArrayList<Transition<LETTER, STATE>> transitionList = new ArrayList<Transition<LETTER, STATE>>();
				for (Transition<LETTER, STATE> transition : automaton.getTransitions().get(state)) {
					Transition<LETTER, STATE> transitionCopy = transition.copyTransition();
					transitionList.add(transitionCopy);
				}
				unionTransitions.put(state, transitionList);
				
				if (automaton.getInitialConditions().get(state).getCondition().get(0).get(0).getTermType() != TermType.FALSE) {
				
					for (Transition<LETTER, STATE> transition : automaton.getTransitions().get(state)) {
					
						Transition<LETTER, STATE> transitionCopy = transition.copyTransition();
						ConjunctGuards conjunction = new ConjunctGuards(transitionCopy.getGuards(), automaton.getInitialConditions().get(state).copyInitialCondition().getCondition());
						Transition<LETTER, STATE> newTransition = new Transition<LETTER, STATE>(
								transitionCopy.getLetter(), 
								mNewInitialState, 
								transitionCopy.getSucState(), 
								conjunction.getResult(), 
								transitionCopy.getUpdates());
						newTransitions.add(newTransition);
				}
			}
		}
	}

	@Override
	public CountingAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(CRSF stateFactory) throws AutomataLibraryException {
		// TODO Auto-generated method stub
		return false;
	}
}
