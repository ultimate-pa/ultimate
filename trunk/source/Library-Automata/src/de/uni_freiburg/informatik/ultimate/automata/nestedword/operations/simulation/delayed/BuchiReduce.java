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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.AbstractMinimizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizationCheckResultStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizationStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance.SimulationPerformance;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Operation that reduces a given buechi automaton by using {@link DelayedSimulation}.<br/>
 * Once constructed the reduction automatically starts, the result can be get by using {@link #getResult()}.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 * @author Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * @author Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * @date 10.12.2011
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public class BuchiReduce<LETTER, STATE> extends AbstractMinimizeNwa<LETTER, STATE> {
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
	private final SimulationPerformance mStatistics;

	/**
	 * Creates a new buechi reduce object that starts reducing the given buechi automaton.<br/>
	 * Once finished the result can be get by using {@link #getResult()}.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param stateFactory
	 *            The state factory used for creating states
	 * @param operand
	 *            The buechi automaton to reduce
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate framework.
	 */
	public BuchiReduce(final AutomataLibraryServices services, final IMinimizationStateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		this(services, stateFactory, operand,
				new DelayedSimulation<>(services.getProgressAwareTimer(),
						services.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID), false, stateFactory,
						new DelayedGameGraph<>(services, stateFactory, services.getProgressAwareTimer(),
								services.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID), operand)));
	}

	/**
	 * Creates a new buechi reduce object that starts reducing the given buechi automaton with a given simulation.<br/>
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
	 *             If the operation was canceled, for example from the Ultimate framework.
	 */
	protected BuchiReduce(final AutomataLibraryServices services, final IMinimizationStateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand, final DelayedSimulation<LETTER, STATE> simulation)
			throws AutomataOperationCanceledException {
		super(services, stateFactory);
		mOperand = operand;
		mLogger.info(startMessage());

		simulation.getGameGraph().generateGameGraphFromAutomaton();
		simulation.doSimulation();
		mResult = simulation.getResult();
		super.directResultConstruction(mResult);
		mStatistics = simulation.getSimulationPerformance();

		final boolean compareWithSccResult = false;
		if (compareWithSccResult) {
			final DelayedGameGraph<LETTER, STATE> graph = new DelayedGameGraph<>(mServices, stateFactory,
					mServices.getProgressAwareTimer(), mLogger, mOperand);
			graph.generateGameGraphFromAutomaton();
			final DelayedSimulation<LETTER, STATE> sccSim =
					new DelayedSimulation<>(mServices.getProgressAwareTimer(), mLogger, true, stateFactory, graph);
			sccSim.doSimulation();
			final INestedWordAutomaton<LETTER, STATE> sccResult = sccSim.getResult();
			if (mResult.size() != sccResult.size()) {
				throw new AssertionError();
			}
		}

		mLogger.info(exitMessage());
	}

	@Override
	public Pair<Boolean, String> checkResultHelper(final IMinimizationCheckResultStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		return checkBuchiEquivalence(stateFactory);
	}

	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		final AutomataOperationStatistics statistics = super.getAutomataOperationStatistics();
		mStatistics.exportToExistingAutomataOperationStatistics(statistics);
		return statistics;
	}

	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return mResult;
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
