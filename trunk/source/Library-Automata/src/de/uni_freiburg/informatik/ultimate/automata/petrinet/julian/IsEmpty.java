/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetUnfolder.order;

public class IsEmpty<LETTER,STATE> implements IOperation<LETTER,STATE> {
	private final AutomataLibraryServices m_Services;
	
	private final Logger m_Logger;

	private final PetriNetJulian<LETTER,STATE> m_Operand;
	private final Boolean m_Result;
	
	public IsEmpty(AutomataLibraryServices services, 
			PetriNetJulian<LETTER,STATE> operand) throws AutomataLibraryException {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_Operand = operand;
		m_Logger.info(startMessage());
		PetriNetUnfolder<LETTER,STATE> unf = 
				new PetriNetUnfolder<LETTER,STATE>(m_Services, operand, order.ERV, false, true);
		PetriNetRun<LETTER,STATE> run = unf.getAcceptingRun();
		m_Result = (run == null);
		m_Logger.info(exitMessage());
	}
	
	@Override
	public String operationName() {
		return "isEmpty";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() +
			"Operand " + m_Operand.sizeInformation();
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() +
			" language " + (m_Result ? "is empty" : "is not emtpy");
	}

	@Override
	public Boolean getResult() throws AutomataLibraryException {
		return m_Result;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		INestedWordAutomatonOldApi<LETTER, STATE> finiteAutomaton = (new PetriNet2FiniteAutomaton<>(m_Services, m_Operand)).getResult();
		boolean automatonEmpty = (new de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IsEmpty<LETTER, STATE>(m_Services, finiteAutomaton)).getResult();
		return (m_Result == automatonEmpty);
	}

}
