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

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;


public class Totalize<LETTER,STATE> implements IOperation<LETTER,STATE> {
	
	private final IUltimateServiceProvider m_Services;

	protected static Logger s_Logger = 
		NestedWordAutomata.getLogger();
	
	private final INestedWordAutomatonSimple<LETTER,STATE> m_Operand;
	private final TotalizeNwa<LETTER, STATE> m_Totalized;
	private final NestedWordAutomatonReachableStates<LETTER,STATE> m_Result;
	private final StateFactory<STATE> m_StateFactory;
	
	
	@Override
	public String operationName() {
		return "determinize";
	}
	
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand " + 
			m_Operand.sizeInformation();
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result " + 
				m_Result.sizeInformation();
	}
	
	
	public Totalize(IUltimateServiceProvider services,
			INestedWordAutomatonSimple<LETTER,STATE> input) throws OperationCanceledException {
		m_Services = services;
		this.m_StateFactory = input.getStateFactory();
		this.m_Operand = input;
		s_Logger.info(startMessage());
		m_Totalized = new TotalizeNwa<LETTER, STATE>(input, m_StateFactory);
		m_Result = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Services, m_Totalized);
		s_Logger.info(exitMessage());
	}
	


	@Override
	public INestedWordAutomatonOldApi<LETTER, STATE> getResult() {
		return m_Result;
	}


	@Override
	public boolean checkResult(StateFactory<STATE> sf) throws AutomataLibraryException {
		boolean correct = true;
			s_Logger.info("Start testing correctness of " + operationName());
			INestedWordAutomatonOldApi<LETTER, STATE> operandOldApi = ResultChecker.getOldApiNwa(m_Services, m_Operand);

			// should recognize same language imput
			correct &= (ResultChecker.nwaLanguageInclusion(m_Services, operandOldApi, m_Result, sf) == null);
			correct &= (ResultChecker.nwaLanguageInclusion(m_Services, m_Result, operandOldApi, sf) == null);
			if (!correct) {
				ResultChecker.writeToFileIfPreferred(m_Services, operationName() + "Failed", "", m_Operand);
			}
		s_Logger.info("Finished testing correctness of " + operationName());
		return correct;
	}
	
	
}

