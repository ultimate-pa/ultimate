/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.ReachableStatesCopy;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class RemoveUnreachable<LETTER,STATE> implements IOperation<LETTER,STATE> {
	
	private final INestedWordAutomatonSimple<LETTER,STATE> m_Input;
	private final NestedWordAutomatonReachableStates<LETTER,STATE> m_Result;

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);

	/**
	 * Given an INestedWordAutomaton nwa return a NestedWordAutomaton that has
	 * the same states, but all states that are not reachable are omitted.
	 * Each state of the result also occurred in the input. Only the auxiliary
	 * empty stack state of the result is different. 
	 * 
	 * @param nwa
	 * @throws OperationCanceledException
	 */
	public RemoveUnreachable(INestedWordAutomatonSimple<LETTER,STATE> nwa)
			throws OperationCanceledException {
		m_Input = nwa;
		s_Logger.info(startMessage());
		m_Result = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Input);
		s_Logger.info(exitMessage());
	}
	

	@Override
	public String operationName() {
		return "removeUnreachable";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Input "
				+ m_Input.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result "
				+ m_Result.sizeInformation();
	}


	@Override
	public NestedWordAutomatonReachableStates<LETTER,STATE> getResult() throws OperationCanceledException {
		return m_Result;
	}

	
	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory) throws OperationCanceledException {
		boolean correct = true;
		if (m_Input instanceof INestedWordAutomatonOldApi) {
			s_Logger.info("Start testing correctness of " + operationName());
			// correct &= (ResultChecker.nwaLanguageInclusion(m_Input, m_Result)
			// == null);
			// correct &= (ResultChecker.nwaLanguageInclusion(m_Result, m_Input)
			// == null);
			assert correct;
			DoubleDeckerAutomaton<LETTER, STATE> reachalbeStatesCopy = (DoubleDeckerAutomaton<LETTER, STATE>) (new ReachableStatesCopy(
					(INestedWordAutomatonOldApi) m_Input, false, false, false,
					false)).getResult();
			correct &=
			ResultChecker.isSubset(reachalbeStatesCopy.getStates(),m_Result.getStates());
			assert correct;
			correct &=
			ResultChecker.isSubset(m_Result.getStates(),reachalbeStatesCopy.getStates());
			assert correct;
			for (STATE state : reachalbeStatesCopy.getStates()) {
				for (OutgoingInternalTransition<LETTER, STATE> outTrans : reachalbeStatesCopy.internalSuccessors(state)) {
					correct &= m_Result.containsInternalTransition(state, outTrans.getLetter(), outTrans.getSucc());
					assert correct;
				}
				for (OutgoingCallTransition<LETTER, STATE> outTrans : reachalbeStatesCopy.callSuccessors(state)) {
					correct &= m_Result.containsCallTransition(state, outTrans.getLetter(), outTrans.getSucc());
					assert correct;
				}
				for (OutgoingReturnTransition<LETTER, STATE> outTrans : reachalbeStatesCopy.returnSuccessors(state)) {
					correct &= m_Result.containsReturnTransition(state, outTrans.getHierPred(), outTrans.getLetter(), outTrans.getSucc());
					assert correct;
				}
				for (OutgoingInternalTransition<LETTER, STATE> outTrans : m_Result.internalSuccessors(state)) {
					correct &= reachalbeStatesCopy.containsInternalTransition(state, outTrans.getLetter(), outTrans.getSucc());
					assert correct;
				}
				for (OutgoingCallTransition<LETTER, STATE> outTrans : m_Result.callSuccessors(state)) {
					correct &= reachalbeStatesCopy.containsCallTransition(state, outTrans.getLetter(), outTrans.getSucc());
					assert correct;
				}
				for (OutgoingReturnTransition<LETTER, STATE> outTrans : m_Result.returnSuccessors(state)) {
					correct &= reachalbeStatesCopy.containsReturnTransition(state, outTrans.getHierPred(), outTrans.getLetter(), outTrans.getSucc());
					assert correct;
				}
				Set<STATE> rCSdownStates = reachalbeStatesCopy
						.getDownStates(state);
				Set<STATE> rCAdownStates = m_Result.getDownStates(state);
				correct &= ResultChecker.isSubset(rCAdownStates, rCSdownStates);
				assert correct;
				correct &= ResultChecker.isSubset(rCSdownStates, rCAdownStates);
				assert correct;
			}
			if (!correct) {
				ResultChecker.writeToFileIfPreferred(
						operationName() + "Failed", "", m_Input);
			}
			s_Logger.info("Finished testing correctness of " + operationName());
		}
		return correct;
	}

}