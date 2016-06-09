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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.fair.nwa;

import java.util.Collection;
import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.fair.FairSimulation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;

/**
 * Simulation that realizes <b>fair simulation</b> for reduction of a given nwa
 * automaton.<br/>
 * Once started, results can then be get by using {@link #getResult()}.<br/>
 * <br/>
 * 
 * For more information on the type of simulation see {@link FairNwaGameGraph}.
 * 
 * @author Daniel Tischner
 * 
 * @param <LETTER>
 *            Letter class of nwa automaton
 * @param <STATE>
 *            State class of nwa automaton
 */
public final class FairNwaSimulation<LETTER, STATE> extends FairSimulation<LETTER, STATE> {

	/**
	 * Creates a new fair simulation that tries to reduce the given nwa
	 * automaton using <b>fair simulation</b>. Uses a given collection of
	 * equivalence classes to optimize the simulation.<br/>
	 * After construction the simulation can be started and results can be get
	 * by using {@link #getResult()}.<br/>
	 * <br/>
	 * 
	 * For correctness its important that the inputed automaton has <b>no dead
	 * ends</b> nor <b>duplicate transitions</b>.
	 * 
	 * @param progressTimer
	 *            Timer used for responding to timeouts and operation
	 *            cancellation.
	 * @param logger
	 *            ILogger of the Ultimate framework.
	 * @param useSCCs
	 *            If the simulation calculation should be optimized using SCC,
	 *            Strongly Connected Components.
	 * @param stateFactory
	 *            The state factory used for creating states.
	 * @param possibleEquivalentClasses
	 *            A collection of sets which contains states of the nwa
	 *            automaton that may be merge-able. States which are not in the
	 *            same set are definitely not merge-able which is used as an
	 *            optimization for the simulation
	 * @param game
	 *            The fair nwa game graph to use for simulation.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public FairNwaSimulation(final IProgressAwareTimer progressTimer, final ILogger logger, final boolean useSCCs,
			final StateFactory<STATE> stateFactory, final Collection<Set<STATE>> possibleEquivalentClasses,
			final FairNwaGameGraph<LETTER, STATE> game) throws AutomataOperationCanceledException {
		super(progressTimer, logger, useSCCs, stateFactory, possibleEquivalentClasses, game);
	}

	/**
	 * Creates a new fair simulation that tries to reduce the given nwa
	 * automaton using <b>fair simulation</b>.<br/>
	 * After construction the simulation starts and results can be get by using
	 * {@link #getResult()}.<br/>
	 * <br/>
	 * 
	 * For correctness its important that the inputed automaton has <b>no dead
	 * ends</b> nor <b>duplicate transitions</b>.
	 * 
	 * @param progressTimer
	 *            Timer used for responding to timeouts and operation
	 *            cancellation.
	 * @param logger
	 *            ILogger of the Ultimate framework.
	 * @param useSCCs
	 *            If the simulation calculation should be optimized using SCC,
	 *            Strongly Connected Components.
	 * @param stateFactory
	 *            The state factory used for creating states.
	 * @param game
	 *            The fair nwa game graph to use for simulation.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public FairNwaSimulation(final IProgressAwareTimer progressTimer, final ILogger logger, final boolean useSCCs,
			final StateFactory<STATE> stateFactory, final FairNwaGameGraph<LETTER, STATE> game)
					throws AutomataOperationCanceledException {
		this(progressTimer, logger, useSCCs, stateFactory, Collections.emptyList(), game);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.ASimulation#doSimulation()
	 */
	@Override
	public void doSimulation() throws AutomataOperationCanceledException {
		// super.doSimulation();
		//getLogger().debug(getGameGraph().toAtsFormat());
		setResult(getGameGraph().generateAutomatonFromGraph());
		// TODO Implement some different stuff
	}
}
