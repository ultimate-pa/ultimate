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
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

/**
 * TODO: comment
 * 
 * 
 * @author Thomas Lang
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class LoopComplexity<LETTER, STATE> implements IOperation<LETTER, STATE> {
	
	
	private final IUltimateServiceProvider m_Services;
	private final Logger m_Logger;
	
	private final INestedWordAutomaton<LETTER, STATE> m_Operand;
	private final Integer m_Result;
	
	

	public LoopComplexity(IUltimateServiceProvider services,
			INestedWordAutomaton<LETTER, STATE> operand) {
		super();
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		m_Operand = operand;
		m_Logger.info(this.startMessage());
		
		m_Result = 42;
		m_Logger.info(this.exitMessage());
	}

	@Override
	public String operationName() {
		return "loopComplexity";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Operand " + 
				m_Operand.sizeInformation();	
	}

	@Override
	public String exitMessage() {
		return "test";
	}

	@Override
	public Integer getResult() throws OperationCanceledException {
		return m_Result;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		// TODO Auto-generated method stub
		return true;
	}

}
