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

import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;


/**
 * Class that provides the Buchi emptiness check for nested word automata. 
 * 
 * @param <LETTER> Symbol. Type of the symbols used as alphabet.
 * @param <STATE> Content. Type of the labels (the content) of the automata states. 
 * @version 2010-12-18
 */
public class BuchiIsEmpty<LETTER,STATE> implements IOperation<LETTER,STATE> {
	
	private final IUltimateServiceProvider m_Services;
	INestedWordAutomatonSimple<LETTER, STATE> m_Nwa;
	NestedWordAutomatonReachableStates<LETTER, STATE> m_Reach;
	NestedWordAutomatonReachableStates<LETTER, STATE>.StronglyConnectedComponents m_Sccs;
	final Boolean m_Result;
	
	public BuchiIsEmpty(IUltimateServiceProvider services,
			INestedWordAutomatonSimple<LETTER, STATE> nwa) throws OperationCanceledException {
		m_Services = services;
		m_Nwa = nwa;
		s_Logger.info(startMessage());
		if (m_Nwa instanceof NestedWordAutomatonReachableStates) {
			m_Reach = (NestedWordAutomatonReachableStates<LETTER, STATE>) m_Nwa;
		} else {
			m_Reach = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Services, m_Nwa);
		}
		m_Sccs = m_Reach.getOrComputeStronglyConnectedComponents();
		m_Result = m_Sccs.buchiIsEmpty();
		s_Logger.info(exitMessage());
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
	public Boolean getResult() throws OperationCanceledException {
		return m_Result;
	}
	

	private static Logger s_Logger = 
		NestedWordAutomata.getLogger();	
	
	
	public NestedLassoRun<LETTER,STATE> getAcceptingNestedLassoRun() throws OperationCanceledException {
		if (m_Result) {
			s_Logger.info("There is no accepting nested lasso run");
			return null;
		} else {
			s_Logger.info("Starting construction of run");
			return m_Sccs.getNestedLassoRun();
		}
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		return true;
	}



}
