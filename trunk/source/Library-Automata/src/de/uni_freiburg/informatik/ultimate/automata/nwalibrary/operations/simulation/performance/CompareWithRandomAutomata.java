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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.performance;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.GetRandomDfa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.GetRandomNwa;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Operation that compares the different types of simulation methods for buechi
 * reduction using random automata.<br/>
 * The resulting automaton is the input automaton.
 * 
 * @author Daniel Tischner
 * 
 * @param <LETTER>
 *            Letter class of buechi automaton, not used
 * @param <STATE>
 *            State class of buechi automaton, not used
 */
public final class CompareWithRandomAutomata<LETTER, STATE> implements IOperation<LETTER, STATE> {

	/**
	 * The logger used by the Ultimate framework.
	 */
	private final ILogger m_Logger;
	/**
	 * The inputed buechi automaton.
	 */
	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Operand;
	/**
	 * The resulting buechi automaton.
	 */
	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Result;
	/**
	 * Service provider of Ultimate framework.
	 */
	private final AutomataLibraryServices m_Services;

	/**
	 * Compares the different types of simulation methods for buechi reduction
	 * using random automata. Resulting automaton is the input automaton.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param stateFactory
	 *            The state factory used for creating states
	 * @param operand
	 *            A buechi automaton, it is not used by the operation
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public CompareWithRandomAutomata(final AutomataLibraryServices services, final StateFactory<STATE> stateFactory,
			final INestedWordAutomatonOldApi<LETTER, STATE> operand) throws OperationCanceledException {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		m_Operand = operand;
		m_Result = operand;
		m_Logger.info(startMessage());

		// Use operation with random automata
		StateFactory<String> snf = (StateFactory<String>) new StringFactory();

		int n = 100;
		int k = 30;
		int f = 20;
		int totalityInPerc = 10;
		int logEvery = 100;
		int amount = 1000;
		NestedWordAutomaton<String, String> buechi;

		for (int i = 1; i <= amount; i++) {
			if (i % logEvery == 0) {
				m_Logger.info("Worked " + i + " automata");
			}

			boolean useNwaInsteadDfaMethod = false;
			if (useNwaInsteadDfaMethod) {
				buechi = new GetRandomNwa(services, k, n, 0.2, 0, 0, (totalityInPerc + 0.0f) / 100).getResult();
			} else {
				buechi = new GetRandomDfa(services, n, k, f, totalityInPerc, true, false, false, false).getResult();
			}

			try {
				new CompareReduceBuchiSimulation<String, String>(services, snf, buechi);
			} catch (OperationCanceledException e) {
				e.printStackTrace();
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
	public boolean checkResult(final StateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.automata.IOperation#exitMessage()
	 */
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ".";
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
		return "compareWithRandomAutomata";
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
}
