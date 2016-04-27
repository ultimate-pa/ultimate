/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2011-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
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
/**
 * Reduce the state space of a given Buchi automaton, as described in the paper
 * "Fair simulation relations, parity games and state space reduction for
 * Buchi automata" - Etessami, Wilke and Schuller.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.delayed;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.ReachableStatesCopy;

/**
 * Operation that reduces a given buechi automaton by using
 * {@link DelayedSimulation}.<br/>
 * Once constructed the reduction automatically starts, the result can be get by
 * using {@link #getResult()}.
 * 
 * @author Daniel Tischner
 * @author Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * @author Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * @date 10.12.2011
 * 
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public class BuchiReduce<LETTER, STATE> implements IOperation<LETTER, STATE> {

	/**
	 * The logger used by the Ultimate framework.
	 */
	private final Logger m_Logger;
	/**
	 * The inputed buechi automaton.
	 */
	private INestedWordAutomatonOldApi<LETTER, STATE> m_Operand;
	/**
	 * The resulting possible reduced buechi automaton.
	 */
	private INestedWordAutomatonOldApi<LETTER, STATE> m_Result;
	/**
	 * Service provider of Ultimate framework.
	 */
	private final AutomataLibraryServices m_Services;

	/**
	 * Creates a new buechi reduce object that starts reducing the given buechi
	 * automaton.<br/>
	 * Once finished the result can be get by using {@link #getResult()}.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param stateFactory
	 *            The state factory used for creating states
	 * @param operand
	 *            The buechi automaton to reduce
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public BuchiReduce(AutomataLibraryServices services, StateFactory<STATE> stateFactory,
			INestedWordAutomatonOldApi<LETTER, STATE> operand) throws OperationCanceledException {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_Operand = operand;
		m_Logger.info(startMessage());

		// Remove dead ends.
		// Removal of dead ends is no optimization but a requirement for
		// correctness of the algorithm
		m_Operand = new ReachableStatesCopy<LETTER, STATE>(m_Services, operand, false, false, true, false).getResult();
		if (m_Logger.isDebugEnabled()) {
			StringBuilder msg = new StringBuilder();
			msg.append(" W/O dead ends ").append(m_Operand.sizeInformation());
			m_Logger.debug(msg.toString());
		}

		DelayedGameGraph<LETTER, STATE> graph = new DelayedGameGraph<>(m_Services,
				m_Services.getProgressMonitorService(), m_Logger, m_Operand, stateFactory);
		graph.generateGameGraphFromAutomaton();
		DelayedSimulation<LETTER, STATE> sim = new DelayedSimulation<>(m_Services.getProgressMonitorService(), m_Logger,
				true, stateFactory, graph);
		sim.doSimulation();
		m_Result = sim.getResult();

		boolean compareWithNonSccResult = false;
		if (compareWithNonSccResult) {
			graph = new DelayedGameGraph<>(m_Services, m_Services.getProgressMonitorService(), m_Logger, m_Operand,
					stateFactory);
			graph.generateGameGraphFromAutomaton();
			DelayedSimulation<LETTER, STATE> nonSccSim = new DelayedSimulation<>(m_Services.getProgressMonitorService(),
					m_Logger, false, stateFactory, graph);
			nonSccSim.doSimulation();
			INestedWordAutomatonOldApi<LETTER, STATE> nonSCCresult = nonSccSim.getResult();
			if (m_Result.size() != nonSCCresult.size()) {
				throw new AssertionError();
			}
		}

		m_Logger.info(exitMessage());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.automata.IOperation#checkResult(de.
	 * uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory)
	 */
	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return ResultChecker.reduceBuchi(m_Services, m_Operand, m_Result);
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
	public INestedWordAutomatonOldApi<LETTER, STATE> getResult() {
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
		return "reduceBuchi";
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
