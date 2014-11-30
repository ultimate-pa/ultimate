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
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

/**
 * Operation that checks if the language of the first Buchi automaton is 
 * included in the language of the second Buchi automaton.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 * @param <LETTER>
 * @param <STATE>
 */
public class BuchiIsIncluded<LETTER, STATE> implements IOperation<LETTER,STATE> {

	private final IUltimateServiceProvider m_Services;
	private static Logger s_Logger = NestedWordAutomata.getLogger();

	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Operand1;
	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Operand2;

	private final Boolean m_Result;

	private final NestedLassoRun<LETTER, STATE> m_Counterexample;

	public BuchiIsIncluded(IUltimateServiceProvider services,
			StateFactory<STATE> stateFactory,
			INestedWordAutomatonOldApi<LETTER, STATE> nwa1,
			INestedWordAutomatonOldApi<LETTER, STATE> nwa2)
			throws AutomataLibraryException {
		m_Services = services;
		m_Operand1 = nwa1;
		m_Operand2 = nwa2;
		s_Logger.info(startMessage());

		INestedWordAutomatonOldApi<LETTER, STATE> sndComplement = (new BuchiComplementFKV<LETTER, STATE>(
				m_Services, stateFactory, m_Operand2)).getResult();
		INestedWordAutomatonOldApi<LETTER, STATE> difference = (new BuchiIntersectDD<LETTER, STATE>(
				m_Services, m_Operand1, sndComplement, true)).getResult();
		BuchiIsEmpty<LETTER, STATE> emptinessCheck = new BuchiIsEmpty<LETTER, STATE>(
				m_Services, (INestedWordAutomatonOldApi<LETTER, STATE>) difference);

		m_Result = emptinessCheck.getResult();
		m_Counterexample = emptinessCheck.getAcceptingNestedLassoRun();
		s_Logger.info(exitMessage());
	}

	@Override
	public String operationName() {
		return "isIncluded";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Operand1 "
				+ m_Operand1.sizeInformation() + ". Operand2 "
				+ m_Operand2.sizeInformation();
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

	public NestedLassoRun<LETTER, STATE> getCounterexample() {
		return m_Counterexample;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		return true;
	}

}
