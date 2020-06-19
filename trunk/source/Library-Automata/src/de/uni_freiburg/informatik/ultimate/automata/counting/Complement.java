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
 * Complement method for Counting Automata
 * Needs a deterministic Automaton as Input
 *
 * @author Marcel Ebbinghaus
 * @author who is the author?
 */

public class Complement<LETTER, STATE, CRSF extends IStateFactory<STATE>> implements IOperation<LETTER, STATE, CRSF> {

	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	private final CountingAutomaton<LETTER, STATE> mOperand;
	private final CountingAutomaton<LETTER, STATE> mResult;
	private final IIntersectionStateFactory<STATE> mStateFactory;


	public Complement(
			final AutomataLibraryServices services, 
			final IIntersectionStateFactory<STATE> stateFactory,
			final CountingAutomaton<LETTER, STATE> operand,
			final STATE newInitialState) throws AutomataLibraryException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(this.getClass());
		mOperand = operand;
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
		
		Map<STATE, ArrayList<ArrayList<Guard>>> complementFinalConditions = new HashMap<STATE, ArrayList<ArrayList<Guard>>>();
		
		for (STATE state : mOperand.getStates()) {
			
			ArrayList<ArrayList<Guard>> finalConditionsCopy1 = mOperand.getFinalConditions().get(state);
			
			//negate guards
			for (ArrayList<Guard> guardList : finalConditionsCopy1) {
				
				for (Guard guard : guardList) {
					
					if (guard.getTermType() == 0) {
						
						guard.changeTermType(1);
					}
					else if (guard.getTermType() == 1) {
						
						guard.changeTermType(0);
					}
					else {
						
						switch(guard.getRelationType()) {
						
						case 0:
							guard.changeRelationType(1);
							break;
							
						case 1:
							guard.changeRelationType(0);
							break;
							
						case 2:
							guard.changeRelationType(5);
							break;
							
						case 3:
							guard.changeRelationType(4);
							break;
							
						case 4:
							guard.changeRelationType(3);
							break;
							
						case 5:
							guard.changeRelationType(2);
							break;
						}
					}
				}
			}
			
			//transform back to DNF
			if (finalConditionsCopy1.size() == 1) {
				
				complementFinalConditions.put(state, finalConditionsCopy1);
			}
			else {
				
				ArrayList<ArrayList<Guard>> finalConditionsCopy2 = new ArrayList<ArrayList<Guard>>();
				ArrayList<ArrayList<Guard>> finalConditionsCopy3 = new ArrayList<ArrayList<Guard>>();
				
				for (Guard guard1 : finalConditionsCopy1.get(0)) {
					
					for (Guard guard2 : finalConditionsCopy1.get(1)) {
						
						ArrayList<Guard> tempCondition = new ArrayList<Guard>();
						tempCondition.add(guard1);
						tempCondition.add(guard2);
						finalConditionsCopy3.add(tempCondition);
					}
				}
				finalConditionsCopy1.remove(0);
				finalConditionsCopy1.remove(0);
				
				while (finalConditionsCopy1.size() > 0) {
					
					for (Guard guard : finalConditionsCopy1.get(0)) {
						
						for (ArrayList<Guard> guardList : finalConditionsCopy3) {
							
							ArrayList<Guard> tempCondition = guardList;
							tempCondition.add(guard);
							finalConditionsCopy2.add(tempCondition);
						}
					}
					finalConditionsCopy3 = finalConditionsCopy2;
					finalConditionsCopy1.remove(0);
					finalConditionsCopy2.clear();
				}
				complementFinalConditions.put(state, finalConditionsCopy3);
			}
		}
		
		//result
				CountingAutomaton<LETTER, STATE> resultAutomaton = new CountingAutomaton<LETTER, STATE>(
						mServices,
						mOperand.getAlphabet(),
						mOperand.getStates(),
						mOperand.getCounter(),
						mOperand.getInitialConditions(),
						complementFinalConditions,
						mOperand.getTransitions());
				return resultAutomaton;
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