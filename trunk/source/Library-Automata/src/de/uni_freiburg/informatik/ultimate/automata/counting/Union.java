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

	//needs to be adjusted to suit new datastructure
	private CountingAutomaton<LETTER, STATE> computeResult() {
		
		Set<LETTER> unionAlphabet = mFstOperand.getAlphabet();
		ArrayList<Counter> unionCounter = mFstOperand.getCounter();
		unionCounter.addAll(mSndOperand.getCounter());
		Set<STATE> unionStates = mFstOperand.getStates();
		unionStates.addAll(mSndOperand.getStates());
		unionStates.add(mNewInitialState);
		Map<STATE, ArrayList<ArrayList<Guard>>> unionInitialConditions = new HashMap<STATE, ArrayList<ArrayList<Guard>>>();
		Map<STATE, ArrayList<ArrayList<Guard>>> unionFinalConditions = new HashMap<STATE, ArrayList<ArrayList<Guard>>>();
		Map<STATE, ArrayList<Transition<LETTER, STATE>>> unionTransitions = new HashMap<STATE, ArrayList<Transition<LETTER, STATE>>>();
		
		//initialConditions
		Guard newInitialGuard = new Guard();
		newInitialGuard.changeTermType(0);
		ArrayList<Guard> newGuardList = new ArrayList<Guard>();
		newGuardList.add(newInitialGuard);
		ArrayList<ArrayList<Guard>> newInitialConditions = new ArrayList<ArrayList<Guard>>();
		newInitialConditions.add(newGuardList);
		unionInitialConditions.put(mNewInitialState, newInitialConditions);
		
		//finalConditions
		unionFinalConditions.putAll(mFstOperand.getFinalConditions());
		unionFinalConditions.putAll(mSndOperand.getFinalConditions());
		ArrayList<ArrayList<Guard>> newFinalConditions = new ArrayList<ArrayList<Guard>>();
		addNewUnionFinalConditions(mFstOperand, newFinalConditions);
		addNewUnionFinalConditions(mSndOperand, newFinalConditions);
		
		//construct finalCondition == false, if there were no states in mFstOperand and mSndOperand which are initial and final at once
		if (newFinalConditions.size() == 0) {
			
			Guard newGuardFalse = new Guard();
			newGuardFalse.changeTermType(1);
			ArrayList<Guard> guardList = new ArrayList<Guard>();
			guardList.add(newGuardFalse);
			newFinalConditions.add(guardList);
		}
		unionFinalConditions.put(mNewInitialState, newFinalConditions);
		
		//transitions
		unionTransitions.putAll(mFstOperand.getTransitions());
		unionTransitions.putAll(mSndOperand.getTransitions());
		ArrayList<Transition<LETTER, STATE>> newTransitions = new ArrayList<Transition<LETTER, STATE>>();
		addNewUnionTransitions(mFstOperand, newTransitions);
		addNewUnionTransitions(mSndOperand, newTransitions);
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
	
	private void addNewUnionFinalConditions (CountingAutomaton<LETTER, STATE> automaton, ArrayList<ArrayList<Guard>> newFinalConditions) {
		
		for (STATE state : automaton.getStates()) {
			
			if (automaton.getInitialConditions().get(state).get(0).get(0).getTermType() != 1 &&
					automaton.getFinalConditions().get(state).get(0).get(0).getTermType() != 1) {
				
				ConjunctGuards conjunction = new ConjunctGuards(
						automaton.getFinalConditions().get(state), 
						automaton.getInitialConditions().get(state));
				newFinalConditions.addAll(conjunction.getResult());
			}
		}
	}
	
	private void addNewUnionTransitions (CountingAutomaton<LETTER, STATE> automaton, ArrayList<Transition<LETTER, STATE>> newTransitions) {
		
			for (STATE state : automaton.getStates()) {
			
				if (automaton.getInitialConditions().get(state).get(0).get(0).getTermType() != 1) {
				
					for (Transition<LETTER, STATE> transition : automaton.getTransitions().get(state)) {
					
						ConjunctGuards conjunction = new ConjunctGuards(transition.getGuards(), automaton.getInitialConditions().get(state));
						Transition<LETTER, STATE> newTransition = new Transition<LETTER, STATE>(
								transition.getLetter(), 
								mNewInitialState, 
								transition.getSucState(), 
								conjunction.getResult(), 
								transition.getUpdates());
						newTransitions.add(newTransition);
				}
			}
		}
	}

	@Override
	public Object getResult() {
		// TODO Auto-generated method stub
		return mResult;
	}

	@Override
	public boolean checkResult(CRSF stateFactory) throws AutomataLibraryException {
		// TODO Auto-generated method stub
		return false;
	}
}
