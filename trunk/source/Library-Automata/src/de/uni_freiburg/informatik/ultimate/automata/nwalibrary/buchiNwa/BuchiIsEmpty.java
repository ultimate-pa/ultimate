/*
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 * Copyright (C) 2010-2015 wuxio
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.AcceptingComponentsAnalysis;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;


/**
 * Class that provides the Buchi emptiness check for nested word automata. 
 * 
 * @param <LETTER> Symbol. Type of the symbols used as alphabet.
 * @param <STATE> Content. Type of the labels (the content) of the automata states. 
 * @version 2010-12-18
 */
public class BuchiIsEmpty<LETTER,STATE> implements IOperation<LETTER,STATE> {
	
	private final AutomataLibraryServices m_Services;
	INestedWordAutomatonSimple<LETTER, STATE> m_Nwa;
	NestedWordAutomatonReachableStates<LETTER, STATE> m_Reach;
	AcceptingComponentsAnalysis<LETTER, STATE> m_Sccs;
	final Boolean m_Result;
	
	public BuchiIsEmpty(AutomataLibraryServices services,
			INestedWordAutomatonSimple<LETTER, STATE> nwa) throws AutomataLibraryException {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		m_Nwa = nwa;
		m_Logger.info(startMessage());
		try {
			if (m_Nwa instanceof NestedWordAutomatonReachableStates) {
				m_Reach = (NestedWordAutomatonReachableStates<LETTER, STATE>) m_Nwa;
			} else {
				m_Reach = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Services, m_Nwa);
			}
			m_Sccs = m_Reach.getOrComputeAcceptingComponents();
			m_Result = m_Sccs.buchiIsEmpty();
		} catch (OperationCanceledException oce) {
			throw new OperationCanceledException(getClass());
		}
		m_Logger.info(exitMessage());
	}
	
	@Override
	public String operationName() {
		return "buchiIsEmpty";
	}

	@Override
	public String startMessage() {
			return "Start " + operationName() + ". Operand " + 
			m_Nwa.sizeInformation();	
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result is " + m_Result; 
	}

	@Override
	public Boolean getResult() throws AutomataLibraryException {
		return m_Result;
	}
	

	private final ILogger m_Logger;
	
	
	public NestedLassoRun<LETTER,STATE> getAcceptingNestedLassoRun() throws AutomataLibraryException {
		if (m_Result) {
			m_Logger.info("There is no accepting nested lasso run");
			return null;
		} else {
			m_Logger.info("Starting construction of run");
			return m_Reach.getOrComputeAcceptingComponents().getNestedLassoRun();
		}
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		return true;
	}



}
