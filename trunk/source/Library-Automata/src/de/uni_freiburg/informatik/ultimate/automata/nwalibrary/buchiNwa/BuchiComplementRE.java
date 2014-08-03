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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DeterminizeUnderappox;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.ReachableStatesCopy;

public class BuchiComplementRE<LETTER,STATE> implements IOperation<LETTER,STATE> {

	
	private static Logger s_Logger = 
			NestedWordAutomata.getLogger();

	private INestedWordAutomatonOldApi<LETTER,STATE> m_Operand;
	private INestedWordAutomatonOldApi<LETTER,STATE> m_Result;
	
	private boolean m_buchiComplementREApplicable;
	
	@Override
	public String operationName() {
		return "buchiComplementRE";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand " + 
			m_Operand.sizeInformation();
	}

	@Override
	public String exitMessage() {
		if (m_buchiComplementREApplicable) {
			return "Finished " + operationName() + " Result " + 
				m_Result.sizeInformation();
		} else {
			return "Unable to perform " + operationName() + "on this input";
		}
	}

	@Override
	public INestedWordAutomatonOldApi<LETTER,STATE> getResult() throws OperationCanceledException {
		if (m_buchiComplementREApplicable) {
			return m_Result;
		} else {
			assert m_Result == null;
			throw new UnsupportedOperationException("Operation was not applicable");
		}
	}
	
	
	public BuchiComplementRE(StateFactory<STATE> stateFactory,
			INestedWordAutomatonOldApi<LETTER,STATE> operand) throws AutomataLibraryException {
		m_Operand = operand;
		s_Logger.info(startMessage());
		INestedWordAutomatonOldApi<LETTER,STATE> operandWithoutNonLiveStates = 
				(new ReachableStatesCopy<LETTER,STATE>(operand, false, false, false, true)).getResult();
		if (operandWithoutNonLiveStates.isDeterministic()) {
			s_Logger.info("Rüdigers determinization knack not necessary, already deterministic");
			m_Result = (new BuchiComplementDeterministic<LETTER,STATE>(operandWithoutNonLiveStates)).getResult();
		}
		else {
			PowersetDeterminizer<LETTER,STATE> pd = 
					new PowersetDeterminizer<LETTER,STATE>(operandWithoutNonLiveStates, true, stateFactory);
			INestedWordAutomatonOldApi<LETTER,STATE> determinized = 
					(new DeterminizeUnderappox<LETTER,STATE>(operandWithoutNonLiveStates,pd)).getResult();
			INestedWordAutomatonOldApi<LETTER,STATE> determinizedComplement =
					(new BuchiComplementDeterministic<LETTER,STATE>(determinized)).getResult();
			INestedWordAutomatonOldApi<LETTER,STATE> intersectionWithOperand =
					(new BuchiIntersectDD<LETTER,STATE>(operandWithoutNonLiveStates, determinizedComplement, true)).getResult();
			NestedLassoRun<LETTER,STATE> run = (new BuchiIsEmpty<LETTER,STATE>(intersectionWithOperand)).getAcceptingNestedLassoRun();
			if (run == null) {
				s_Logger.info("Rüdigers determinization knack applicable");
				m_buchiComplementREApplicable = true;
				m_Result = determinizedComplement;
			}
			else {
				s_Logger.info("Rüdigers determinization knack not applicable");
				m_buchiComplementREApplicable = false;
				m_Result = null;
			}
		}


		
		s_Logger.info(exitMessage());
	}
	
	
	/**
	 * Return true if buchiComplementRE was applicable on the input.
	 */
	public boolean applicable() {
		return m_buchiComplementREApplicable;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		return ResultChecker.buchiComplement(m_Operand, m_Result);
	}

}
