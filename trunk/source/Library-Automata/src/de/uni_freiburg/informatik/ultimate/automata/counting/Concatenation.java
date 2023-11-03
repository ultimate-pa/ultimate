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
 * Concatenation method for Counting Automata
 *
 * @author Marcel Ebbinghaus
 * @author who is the author?
 */
public class Concatenation<LETTER, STATE, CRSF extends IStateFactory<STATE>> implements IOperation<LETTER, STATE, CRSF> {

	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	private final CountingAutomaton<LETTER, STATE> mFstOperand;
	private final CountingAutomaton<LETTER, STATE> mSndOperand;
	private final CountingAutomaton<LETTER, STATE> mResult;
	private final IIntersectionStateFactory<STATE> mStateFactory;


	public Concatenation(
			final AutomataLibraryServices services, 
			final IIntersectionStateFactory<STATE> stateFactory,
			final CountingAutomaton<LETTER, STATE> fstOperand,
			final CountingAutomaton<LETTER, STATE> sndOperand) throws AutomataLibraryException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(this.getClass());
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;
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
		Set<LETTER> concatenationAlphabet = new HashSet<LETTER>();
		concatenationAlphabet.addAll(mFstOperand.getAlphabet());
		ArrayList<Counter> concatenationCounter = new ArrayList<Counter>();
		for (Counter counter : mFstOperand.getCounter()) {
			concatenationCounter.add(counter.copyCounter());
		}
		for (Counter counter : mSndOperand.getCounter()) {
			concatenationCounter.add(counter.copyCounter());
		}
		Set<STATE> concatenationStates = new HashSet<STATE>();
		concatenationStates.addAll(mFstOperand.getStates());
		concatenationStates.addAll(mSndOperand.getStates());
		Map<STATE, InitialCondition> concatenationInitialConditions = new HashMap<STATE, InitialCondition>();
		Map<STATE, FinalCondition> concatenationFinalConditions = new HashMap<STATE, FinalCondition>();
		Map<STATE, ArrayList<Transition<LETTER, STATE>>> concatenationTransitions = new HashMap<STATE, ArrayList<Transition<LETTER, STATE>>>();
		
		//initialize parameters of fstOperand
		for (STATE state : mFstOperand.getStates()) {		
			concatenationInitialConditions.put(state, mFstOperand.getInitialConditions().get(state).copyInitialCondition());
			concatenationFinalConditions.put(state, mFstOperand.getFinalConditions().get(state).copyFinalCondition());
			ArrayList<Transition<LETTER, STATE>> transitionList = new ArrayList<Transition<LETTER, STATE>>();
			for (Transition<LETTER, STATE> transition : mFstOperand.getTransitions().get(state)) {
				transitionList.add(transition.copyTransition());
			}
			concatenationTransitions.put(state, transitionList);
		}
		
		//initialize parameters of SndOperand
		for (STATE state : mSndOperand.getStates()) {
			Guard newGuardFalse = new Guard();
			newGuardFalse.changeTermType(TermType.FALSE);
			ArrayList<Guard> guardListFalse = new ArrayList<Guard>();
			guardListFalse.add(newGuardFalse);
			ArrayList<ArrayList<Guard>> newInitialConditionList = new ArrayList<ArrayList<Guard>>();
			newInitialConditionList.add(guardListFalse);
			InitialCondition newInitialCondition = new InitialCondition(newInitialConditionList);
			concatenationInitialConditions.put(state, newInitialCondition);
			concatenationFinalConditions.put(state, mSndOperand.getFinalConditions().get(state).copyFinalCondition());
			ArrayList<Transition<LETTER, STATE>> transitionList = new ArrayList<Transition<LETTER, STATE>>();
			for (Transition<LETTER, STATE> transition : mSndOperand.getTransitions().get(state)) {
				transitionList.add(transition.copyTransition());
			}
			concatenationTransitions.put(state, transitionList);
		}
		
		//connect finalStates of mFstOperand with initialStates of mSndOperand
		for (STATE stateFstOp : mFstOperand.getStates()) {
			
			if (mFstOperand.getFinalConditions().get(stateFstOp).getCondition().get(0).get(0).getTermType() != TermType.FALSE) {
				
				ArrayList<Transition<LETTER, STATE>> newTransitions = new ArrayList<Transition<LETTER, STATE>>();
				for (Transition<LETTER, STATE> transition : concatenationTransitions.get(stateFstOp))
						newTransitions.add(transition);
				ArrayList<ArrayList<Guard>> newFinalConditionsList = new ArrayList<ArrayList<Guard>>();
				
				for (STATE stateSndOp : mSndOperand.getStates()) {
					
					if (mSndOperand.getInitialConditions().get(stateSndOp).getCondition().get(0).get(0).getTermType() != TermType.FALSE) {
						
						//add new transitions
						for (Transition<LETTER, STATE> transition : mSndOperand.getTransitions().get(stateSndOp)) {
							
							Transition<LETTER, STATE> transitionCopy = transition.copyTransition();
							ConjunctGuards conjunction1 = new ConjunctGuards(
									transitionCopy.getGuards(), 
									mFstOperand.getFinalConditions().get(stateFstOp).copyFinalCondition().getCondition());
							ConjunctGuards conjunction2 = new ConjunctGuards(
									conjunction1.getResult(),
									mSndOperand.getInitialConditions().get(stateSndOp).copyInitialCondition().getCondition());
							Transition<LETTER, STATE> newTransition = new Transition<LETTER, STATE>(transitionCopy.getLetter(), stateFstOp, transitionCopy.getSucState(), conjunction2.getResult(), transitionCopy.getUpdates());
							newTransitions.add(newTransition);
						}
						
						//add finalCondition if stateSndOp is final as well
						if (mSndOperand.getFinalConditions().get(stateSndOp).getCondition().get(0).get(0).getTermType() != TermType.FALSE) {
							
							ConjunctGuards conjunction1 = new ConjunctGuards(
									mFstOperand.getFinalConditions().get(stateFstOp).copyFinalCondition().getCondition(),
									mSndOperand.getInitialConditions().get(stateSndOp).copyInitialCondition().getCondition());
							ConjunctGuards conjunction2 = new ConjunctGuards(
									conjunction1.getResult(),
									mSndOperand.getFinalConditions().get(stateSndOp).copyFinalCondition().getCondition());
							
							newFinalConditionsList.addAll(conjunction2.getResult());
						}
					}
				}
				concatenationTransitions.put(stateFstOp, newTransitions);
				
				//construct finalCondition == false, if there were no states in mSndOperand which are initial and final at once
				if (newFinalConditionsList.size() == 0) {

					Guard newGuardFalse = new Guard();
					newGuardFalse.changeTermType(TermType.FALSE);
					ArrayList<Guard> guardListFalse = new ArrayList<Guard>();
					guardListFalse.add(newGuardFalse);
					newFinalConditionsList.add(guardListFalse);
				}
				FinalCondition newFinalCondition = new FinalCondition(newFinalConditionsList);
				concatenationFinalConditions.put(stateFstOp, newFinalCondition);
			}			
		}
		
		//result
		CountingAutomaton<LETTER, STATE> resultAutomaton = new CountingAutomaton<LETTER, STATE>(
				mServices,
				concatenationAlphabet,
				concatenationStates,
				concatenationCounter,
				concatenationInitialConditions,
				concatenationFinalConditions,
				concatenationTransitions);
		return resultAutomaton;
	}

	@Override
	public CountingAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(CRSF stateFactory) throws AutomataLibraryException {
		// TODO: Check the result
		return true;
	}
}