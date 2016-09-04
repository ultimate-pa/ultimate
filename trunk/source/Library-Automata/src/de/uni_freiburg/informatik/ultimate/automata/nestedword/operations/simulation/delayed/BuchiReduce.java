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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.delayed;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.TestBuchiEquivalence;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

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
public class BuchiReduce<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE> {
	/**
	 * The inputed buechi automaton.
	 */
	private INestedWordAutomaton<LETTER, STATE> mOperand;
	/**
	 * The resulting possible reduced buechi automaton.
	 */
	private INestedWordAutomaton<LETTER, STATE> mResult;
	/**
	 * Performance statistics of this operation.
	 */
	private final AutomataOperationStatistics mStatistics;

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
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public BuchiReduce(final AutomataLibraryServices services, final IStateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		this(services, stateFactory, operand,
				new DelayedSimulation<>(services.getProgressMonitorService(),
						services.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID), false, stateFactory,
						new DelayedGameGraph<>(services, services.getProgressMonitorService(),
								services.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID), operand,
								stateFactory)));
	}

	/**
	 * Creates a new buechi reduce object that starts reducing the given buechi
	 * automaton with a given simulation.<br/>
	 * Once finished the result can be get by using {@link #getResult()}.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param stateFactory
	 *            The state factory used for creating states
	 * @param operand
	 *            The buechi automaton to reduce
	 * @param simulation
	 *            Simulation to use for reduction
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	protected BuchiReduce(final AutomataLibraryServices services, final IStateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand, final DelayedSimulation<LETTER, STATE> simulation)
					throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		mLogger.info(startMessage());

		simulation.getGameGraph().generateGameGraphFromAutomaton();
		simulation.doSimulation();
		mResult = simulation.getResult();
		mStatistics = simulation.getSimulationPerformance().exportToAutomataOperationStatistics();

		final boolean compareWithSccResult = false;
		if (compareWithSccResult) {
			final DelayedGameGraph<LETTER, STATE> graph = new DelayedGameGraph<>(mServices,
					mServices.getProgressMonitorService(), mLogger, mOperand, stateFactory);
			graph.generateGameGraphFromAutomaton();
			final DelayedSimulation<LETTER, STATE> sccSim = new DelayedSimulation<>(
					mServices.getProgressMonitorService(), mLogger, true, stateFactory, graph);
			sccSim.doSimulation();
			final INestedWordAutomaton<LETTER, STATE> sccResult = sccSim.getResult();
			if (mResult.size() != sccResult.size()) {
				throw new AssertionError();
			}
		}

		mLogger.info(exitMessage());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.automata.IOperation#checkResult(de.
	 * uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory)
	 */
	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		mLogger.info("Start testing correctness of " + operationName());
		final boolean correct = (new TestBuchiEquivalence<LETTER, STATE>(mServices, stateFactory, getOperand(),
				getResult())).getResult();
		mLogger.info("Finished testing correctness of " + operationName());
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
		return "Finished " + operationName() + " Result " + mResult.sizeInformation();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.IOperation#
	 * getAutomataOperationStatistics()
	 */
	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		return mStatistics;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.IOperation#getResult()
	 */
	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.automata.IOperation#operationName()
	 */
	@Override
	public String operationName() {
		return "BuchiReduce";
	}

	/**
	 * Gets the logger used by the Ultimate framework.
	 * 
	 * @return The logger used by the Ultimate framework.
	 */
	protected ILogger getLogger() {
		return mLogger;
	}

	/**
	 * Gets the inputed automaton.
	 * 
	 * @return The inputed automaton.
	 */
	@Override
	protected INestedWordAutomaton<LETTER, STATE> getOperand() {
		return mOperand;
	}

	/**
	 * Gets the service provider of the Ultimate framework.
	 * 
	 * @return The service provider of the Ultimate framework.
	 */
	protected AutomataLibraryServices getServices() {
		return mServices;
	}
}
