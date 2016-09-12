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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.direct.nwa;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.direct.DirectSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.NwaSimulationUtil;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.SpoilerNwaVertex;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;

/**
 * Simulation that realizes <b>direct simulation</b> for reduction of a given
 * nwa automaton.<br/>
 * Once started, results can then be get by using {@link #getResult()}.<br/>
 * <br/>
 * 
 * For more information on the type of simulation see {@link DirectNwaGameGraph}
 * .
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 *            Letter class of nwa automaton
 * @param <STATE>
 *            State class of nwa automaton
 */
public final class DirectNwaSimulation<LETTER, STATE> extends DirectSimulation<LETTER, STATE> {

	/**
	 * Creates a new direct nwa simulation with a given graph that tries to
	 * reduce the given nwa automaton using <b>direct simulation</b>.<br/>
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
	 * @param game
	 *            The game graph to use for simulation.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public DirectNwaSimulation(final IProgressAwareTimer progressTimer, final ILogger logger, final boolean useSCCs,
			final IStateFactory<STATE> stateFactory, final DirectNwaGameGraph<LETTER, STATE> game)
					throws AutomataOperationCanceledException {
		super(progressTimer, logger, useSCCs, stateFactory, game);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * simulation.ASimulation#doSimulation()
	 */
	@Override
	public void doSimulation() throws AutomataOperationCanceledException {
		super.doSimulation();

		// getLogger().debug(getGameGraph().toAtsFormat());

		// TODO Remove debug stuff when finished
		// Print some debug stuff
		if (getLogger().isDebugEnabled()) {
			getLogger().debug("Simulation results (filtered):");
			for (final Vertex<LETTER, STATE> vertex : getGameGraph().getSpoilerVertices()) {
				final int progressMeasure = vertex.getPM(null, getGameGraph().getGlobalInfinity());
				if (!(vertex instanceof SpoilerNwaVertex<?, ?>)
						|| (progressMeasure >= getGameGraph().getGlobalInfinity() && (vertex.getQ0() != vertex.getQ1()))
						|| (progressMeasure < getGameGraph().getGlobalInfinity()
								&& (vertex.getQ0() == vertex.getQ1()))) {
					continue;
				}
				String progressMeasureText = Integer.toString(progressMeasure);
				if (progressMeasure >= getGameGraph().getGlobalInfinity()) {
					progressMeasureText = "inf";
				}
				getLogger().debug("\t(" + vertex.getQ0() + "," + vertex.getQ1() + ") = " + progressMeasureText);
			}
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * simulation.ASimulation#retrieveGeneralAutomataPerformance()
	 */
	@Override
	protected void retrieveGeneralAutomataPerformance() {
		super.retrieveGeneralAutomataPerformance();
		NwaSimulationUtil.retrieveGeneralNwaAutomataPerformance(getSimulationPerformance(),
				getGameGraph().getAutomaton(), getResult(), getGameGraph().getServices());
	}
}
