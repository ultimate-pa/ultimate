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
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.incremental_inclusion.InclusionViaDifference;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

/**
 * Operation that takes three Operands A, B_1 and B_2 and checks if the language
 * of A is included in the union of the languages of B_1 and B_2.
 * Since this operation is restricted to exactly three operands
 * it is not useful in practice and only used for testing correctness
 * of our incremental inclusion check.
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class IsIncluded2<LETTER, STATE> implements IOperation<LETTER,STATE> {
	
	private static Logger s_Logger = 
			NestedWordAutomata.getLogger();
	
	private final INestedWordAutomatonSimple<LETTER, STATE> m_A;
	private final INestedWordAutomatonSimple<LETTER, STATE> m_B1;
	private final INestedWordAutomatonSimple<LETTER, STATE> m_B2;
	
	private final InclusionViaDifference<LETTER, STATE> m_InclusionViaDifference;
	
	private final Boolean m_Result;
	private final NestedRun<LETTER, STATE> m_Counterexample;
	
	
	public IsIncluded2(StateFactory<STATE> stateFactory,
			INestedWordAutomatonSimple<LETTER, STATE> a, 
			INestedWordAutomatonSimple<LETTER, STATE> b_1,
			INestedWordAutomatonSimple<LETTER, STATE> b_2) throws AutomataLibraryException {
		m_A = a;
		m_B1 = b_1;
		m_B2 = b_2;
		// workaround until Matthias implemented this
		IUltimateServiceProvider services = null;
		s_Logger.info(startMessage());
		m_InclusionViaDifference = new InclusionViaDifference<>(services, stateFactory, a);
		m_InclusionViaDifference.addSubtrahend(m_B1);
		m_InclusionViaDifference.addSubtrahend(m_B2);
		m_Counterexample = m_InclusionViaDifference.getCounterexample();
		m_Result = (m_Counterexample == null);
		s_Logger.info(exitMessage());
	}

	@Override
	public String operationName() {
		return "isIncluded2";
	}

	@Override
	public String startMessage() {
			return "Start " + operationName() + ". Operand A " + 
					m_A.sizeInformation() + ". Operand B_1 " + 
					m_B1.sizeInformation() + ". Operand B_2 " + 
					m_B2.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ". Language is " 
				+ (m_Result ? "" : "not ") + "included";
	}

	@Override
	public Boolean getResult() throws OperationCanceledException {
		return m_Result;
	}

	public NestedRun<LETTER, STATE> getCounterexample() {
		return m_Counterexample;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		// FIXME: not result check implemented yet
		return true;
	}
	


}
