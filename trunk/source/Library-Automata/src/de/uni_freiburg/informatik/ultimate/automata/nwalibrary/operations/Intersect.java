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
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IntersectDD;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;


public class Intersect<LETTER,STATE> implements IOperation<LETTER,STATE> {

	private final IUltimateServiceProvider m_Services;
	protected static Logger s_Logger = 
		NestedWordAutomata.getLogger();
	
	private final INestedWordAutomatonSimple<LETTER,STATE> m_FstOperand;
	private final INestedWordAutomatonSimple<LETTER,STATE> m_SndOperand;
	private final IntersectNwa<LETTER, STATE> m_Intersect;
	private final NestedWordAutomatonReachableStates<LETTER,STATE> m_Result;
	private final StateFactory<STATE> m_StateFactory;
	
	
	@Override
	public String operationName() {
		return "intersect";
	}
	
	
	@Override
	public String startMessage() {
		return "Start intersect. First operand " + 
				m_FstOperand.sizeInformation() + ". Second operand " + 
				m_SndOperand.sizeInformation();	
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result " + 
				m_Result.sizeInformation();
	}
	
	
	
	
	public Intersect(IUltimateServiceProvider services,
			INestedWordAutomatonOldApi<LETTER,STATE> fstOperand,
			INestedWordAutomatonOldApi<LETTER,STATE> sndOperand
			) throws AutomataLibraryException {
		m_Services = services;
		m_FstOperand = fstOperand;
		m_SndOperand = sndOperand;
		m_StateFactory = m_FstOperand.getStateFactory();
		s_Logger.info(startMessage());
		m_Intersect = new IntersectNwa<LETTER, STATE>(m_FstOperand, m_SndOperand, m_StateFactory, false);
		m_Result = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Services, m_Intersect);
		s_Logger.info(exitMessage());
	}
	






	@Override
	public INestedWordAutomatonOldApi<LETTER, STATE> getResult()
			throws OperationCanceledException {
		return m_Result;
	}


	
	public boolean checkResult(StateFactory<STATE> sf) throws AutomataLibraryException {
		s_Logger.info("Start testing correctness of " + operationName());
		INestedWordAutomatonOldApi<LETTER, STATE> fstOperandOldApi = ResultChecker.getOldApiNwa(m_Services, m_FstOperand);
		INestedWordAutomatonOldApi<LETTER, STATE> sndOperandOldApi = ResultChecker.getOldApiNwa(m_Services, m_SndOperand);
		INestedWordAutomatonOldApi<LETTER, STATE> resultDD = (new IntersectDD<LETTER, STATE>(m_Services, fstOperandOldApi,sndOperandOldApi)).getResult();
		boolean correct = true;
		correct &= (resultDD.size() == m_Result.size());
		assert correct;
		correct &= (ResultChecker.nwaLanguageInclusion(m_Services, resultDD, m_Result, sf) == null);
		assert correct;
		correct &= (ResultChecker.nwaLanguageInclusion(m_Services, m_Result, resultDD, sf) == null);
		assert correct;
		if (!correct) {
			ResultChecker.writeToFileIfPreferred(m_Services, operationName() + "Failed", "", m_FstOperand,m_SndOperand);
		}
		s_Logger.info("Finished testing correctness of " + operationName());
		return correct;
	}
	
	
	
}

