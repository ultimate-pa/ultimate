/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2009-2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.fair;

import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StringFactory;
import de.uni_freiburg.informatik.ultimate.core.services.ToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;

/**
 * Doc comes later.
 * 
 * @author Daniel Tischner
 * @param <LETTER>
 * @param <STATE>
 *
 */
public final class ReduceBuchiFairSimulation<LETTER, STATE> implements IOperation<LETTER, STATE> {
	
	private final Logger m_Logger;
	
	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Operand;

	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Result;

	private final IUltimateServiceProvider m_Services;

	public ReduceBuchiFairSimulation(IUltimateServiceProvider services, StateFactory<STATE> stateFactory,
			INestedWordAutomatonOldApi<LETTER, STATE> operand) {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_Operand = operand;
		m_Logger.info(startMessage());

		m_Result = new FairSimulation<LETTER, STATE>(m_Services, m_Operand, true, stateFactory).m_Result;

		boolean compareWithNonSccResult = false;
		if (compareWithNonSccResult) {
			NestedWordAutomaton<LETTER, STATE> nonSCCresult = new FairSimulation<LETTER, STATE>(m_Services, m_Operand,
					false, stateFactory).m_Result;
			if (m_Result.size() != nonSCCresult.size()) {
				throw new AssertionError();
			}
		}

		m_Logger.info(exitMessage());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.IOperation#checkResult(
	 * de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory)
	 */
	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory) throws AutomataLibraryException {
		m_Logger.info("Start testing correctness of " + operationName());
		boolean correct = true;
		correct &= (ResultChecker.nwaLanguageInclusion(m_Services, m_Operand, m_Result, stateFactory) == null);
		correct &= (ResultChecker.nwaLanguageInclusion(m_Services, m_Result, m_Operand, stateFactory) == null);
		if (!correct) {
			ResultChecker.writeToFileIfPreferred(m_Services, operationName() + "Failed", "", m_Operand);
		}
		m_Logger.info("Finished testing correctness of " + operationName());
		return correct;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.automata.IOperation#exitMessage()
	 */
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result " + m_Result.sizeInformation();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.IOperation#getResult()
	 */
	@Override
	public Object getResult() throws AutomataLibraryException {
		return m_Result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.automata.IOperation#operationName()
	 */
	@Override
	public String operationName() {
		return "reduceBuchiFairSimulation";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.automata.IOperation#startMessage()
	 */
	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Operand has " + m_Operand.sizeInformation();
	}
	
	public static void main(String[] args) {
		ToolchainStorage service = new ToolchainStorage();
		StateFactory<String> snf = (StateFactory<String>) new StringFactory();
		
		// Buechi automaton
		Set<String> alphabet = new HashSet<String>();
		alphabet.add("a");
		alphabet.add("b");
		NestedWordAutomaton<String, String> buechi =
				new NestedWordAutomaton<String, String>(service, alphabet, null, null, snf);
		
		// Big example from tutors cardboard
//		buechi.addState(true, false, "q0");
//		buechi.addState(false, false, "q1");
//		buechi.addState(false, true, "q2");
//		buechi.addState(false, false, "q3");
//		buechi.addState(false, true, "q4");
//		buechi.addInternalTransition("q0", "a", "q1");
//		buechi.addInternalTransition("q1", "a", "q1");
//		buechi.addInternalTransition("q1", "a", "q2");
//		buechi.addInternalTransition("q2", "a", "q2");
//		buechi.addInternalTransition("q2", "a", "q1");
//		buechi.addInternalTransition("q0", "a", "q3");
//		buechi.addInternalTransition("q3", "b", "q3");
//		buechi.addInternalTransition("q3", "a", "q4");
//		buechi.addInternalTransition("q4", "a", "q4");
//		buechi.addInternalTransition("q4", "b", "q3");
		
		// Small example from cav02 paper
//		buechi.addState(true, true, "q1");
//		buechi.addState(false, false, "q2");
//		buechi.addInternalTransition("q1", "a", "q1");
//		buechi.addInternalTransition("q1", "b", "q2");
//		buechi.addInternalTransition("q2", "b", "q2");
//		buechi.addInternalTransition("q2", "a", "q1");
		
		// Small example from cav02 paper extended so that nodes share the same transitions
//		buechi.addState(true, true, "q1");
//		buechi.addState(false, false, "q2");
//		buechi.addInternalTransition("q1", "a", "q1");
//		buechi.addInternalTransition("q1", "b", "q1");
//		buechi.addInternalTransition("q1", "a", "q2");
//		buechi.addInternalTransition("q1", "b", "q2");
//		buechi.addInternalTransition("q2", "a", "q2");
//		buechi.addInternalTransition("q2", "b", "q2");
//		buechi.addInternalTransition("q2", "a", "q1");
//		buechi.addInternalTransition("q2", "b", "q1");
		
		// Small circle example from mind
//		buechi.addState(true, true, "q1");
//		buechi.addState(false, false, "q2");
//		buechi.addState(true, false, "q3");
//		buechi.addState(false, false, "q4");
//		buechi.addInternalTransition("q1", "a", "q2");
//		buechi.addInternalTransition("q2", "b", "q3");
//		buechi.addInternalTransition("q3", "a", "q4");
//		buechi.addInternalTransition("q4", "b", "q1");
		
		// Non merge-able example with a one-directed fair simulation
//		buechi.addState(true, true, "q0");
//		buechi.addState(false, false, "q1");
//		buechi.addInternalTransition("q0", "b", "q0");
//		buechi.addInternalTransition("q0", "a", "q1");
//		buechi.addInternalTransition("q1", "a", "q1");
//		buechi.addInternalTransition("q1", "b", "q1");
		
		// Big example from cav02
		buechi.addState(true, false, "q1");
		buechi.addState(false, false, "q2");
		buechi.addState(false, true, "q3");
		buechi.addState(false, true, "q4");
		buechi.addState(false, false, "q5");
		buechi.addState(false, true, "q6");
		buechi.addState(false, false, "q7");
		buechi.addState(false, false, "q8");
		buechi.addState(false, false, "q9");
		buechi.addState(false, true, "q10");
		buechi.addInternalTransition("q1", "a", "q2");
		buechi.addInternalTransition("q1", "a", "q3");
		buechi.addInternalTransition("q2", "a", "q6");
		buechi.addInternalTransition("q2", "b", "q4");
		buechi.addInternalTransition("q2", "b", "q7");
		buechi.addInternalTransition("q4", "a", "q2");
		buechi.addInternalTransition("q6", "a", "q6");
		buechi.addInternalTransition("q3", "b", "q5");
		buechi.addInternalTransition("q3", "b", "q7");
		buechi.addInternalTransition("q5", "a", "q3");
		buechi.addInternalTransition("q7", "b", "q8");
		buechi.addInternalTransition("q8", "a", "q9");
		buechi.addInternalTransition("q8", "b", "q10");
		buechi.addInternalTransition("q9", "a", "q9");
		buechi.addInternalTransition("q9", "b", "q10");
		buechi.addInternalTransition("q10", "b", "q10");
		
		// Fair simulation
		FairSimulation<String, String> simulation = new FairSimulation<String, String>(service, buechi, true, snf);
		System.out.println(simulation);
	}

}
