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

import java.util.Collection;
import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.direct.DirectSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * Simulation that realizes <b>fair and direct simulation</b> for reduction of a
 * given buechi automaton. It primarily uses fair simulation and uses direct
 * simulation as an optimization.<br/>
 * Once created it starts the simulation, results can then be get by using
 * {@link #getResult()}.<br/>
 * <br/>
 * 
 * For more information on the type of simulation see
 * {@link FairDirectGameGraph}.
 * 
 * @author Daniel Tischner
 * 
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public final class FairDirectSimulation<LETTER, STATE> extends FairSimulation<LETTER, STATE> {

	/**
	 * The underlying buechi automaton from which the game graph gets generated.
	 */
	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Buechi;

	/**
	 * True if the simulation currently mimics the behavior of a
	 * DirectSimulation, false if it mimics a FairSimulation.
	 */
	private boolean m_IsCurrentlyDirectSimulation;

	/**
	 * Creates a new fair simulation that tries to reduce the given buechi
	 * automaton using <b>fair and direct simulation</b>.<br/>
	 * After construction the simulation starts and results can be get by using
	 * {@link #getResult()}.<br/>
	 * <br/>
	 * 
	 * For correctness its important that the inputed automaton has <b>no dead
	 * ends</b> nor <b>duplicate transitions</b>.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework.
	 * @param buechi
	 *            The buechi automaton to reduce with no dead ends nor with
	 *            duplicate transitions
	 * @param useSCCs
	 *            If the simulation calculation should be optimized using SCC,
	 *            Strongly Connected Components.
	 * @param stateFactory
	 *            The state factory used for creating states.
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public FairDirectSimulation(final IUltimateServiceProvider services,
			final INestedWordAutomatonOldApi<LETTER, STATE> buechi, final boolean useSCCs,
			final StateFactory<STATE> stateFactory) throws OperationCanceledException {
		this(services, buechi, useSCCs, stateFactory, Collections.emptyList());
	}

	/**
	 * Creates a new fair simulation that tries to reduce the given buechi
	 * automaton using <b>fair and direct simulation</b>. Uses a given
	 * collection of equivalence classes to optimize the simulation.<br/>
	 * After construction the simulation starts and results can be get by using
	 * {@link #getResult()}.<br/>
	 * <br/>
	 * 
	 * For correctness its important that the inputed automaton has <b>no dead
	 * ends</b> nor <b>duplicate transitions</b>.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework.
	 * @param buechi
	 *            The buechi automaton to reduce with no dead ends nor with
	 *            duplicate transitions
	 * @param useSCCs
	 *            If the simulation calculation should be optimized using SCC,
	 *            Strongly Connected Components.
	 * @param stateFactory
	 *            The state factory used for creating states.
	 * @param possibleEquivalentClasses
	 *            A collection of sets which contains states of the buechi
	 *            automaton that may be merge-able. States which are not in the
	 *            same set are definitely not merge-able which is used as an
	 *            optimization for the simulation
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public FairDirectSimulation(final IUltimateServiceProvider services,
			final INestedWordAutomatonOldApi<LETTER, STATE> buechi, final boolean useSCCs,
			final StateFactory<STATE> stateFactory, final Collection<Set<STATE>> possibleEquivalentClasses)
					throws OperationCanceledException {
		super(services, buechi, useSCCs, stateFactory, possibleEquivalentClasses,
				new FairDirectGameGraph<LETTER, STATE>(services, buechi, stateFactory));
		m_Buechi = buechi;
		m_IsCurrentlyDirectSimulation = false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.fair.FairSimulation#attemptMerge(java.lang.Object,
	 * java.lang.Object)
	 */
	@Override
	protected FairGameGraphChanges<LETTER, STATE> attemptMerge(final STATE firstState, final STATE secondState)
			throws OperationCanceledException {
		// Use previous calculated direct simulation results as optimization
		if (getGameGraph() instanceof FairDirectGameGraph) {
			FairDirectGameGraph<LETTER, STATE> game = (FairDirectGameGraph<LETTER, STATE>) getGameGraph();
			// If states direct simulate each other (in both directions) we can
			// safely merge without validating the change.
			if (game.isDirectSimulating(game.getSpoilerVertex(firstState, secondState, false))
					&& game.isDirectSimulating(game.getSpoilerVertex(secondState, firstState, false))) {
				if (getLogger().isDebugEnabled()) {
					getLogger().debug("\tAttempted merge for " + firstState + " and " + secondState
							+ " clearly is possible since they direct simulate each other.");
				}
				return null;
			}
		}

		// If there is no direct simulation attempt the merge using fair
		// simulation
		return super.attemptMerge(firstState, secondState);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.fair.FairSimulation#attemptTransitionRemoval(java.lang.
	 * Object, java.lang.Object, java.lang.Object)
	 */
	@Override
	protected FairGameGraphChanges<LETTER, STATE> attemptTransitionRemoval(final STATE src, final LETTER a,
			final STATE dest, final STATE invoker) throws OperationCanceledException {
		// Use previous calculated direct simulation results as optimization
		if (getGameGraph() instanceof FairDirectGameGraph) {
			FairDirectGameGraph<LETTER, STATE> game = (FairDirectGameGraph<LETTER, STATE>) getGameGraph();
			// If invoker direct simulates the destination we can safely remove
			// the transition without validating the change.
			if (game.isDirectSimulating(game.getSpoilerVertex(dest, invoker, false))) {
				if (getLogger().isDebugEnabled()) {
					getLogger().debug("\tAttempted transition removal for " + src + " -" + a + "-> " + dest
							+ " clearly is possible since invoker " + invoker + " direct simulates " + dest + ".");
				}
				return null;
			}
		}

		// If there is no direct simulation attempt the removal using fair
		// simulation
		return super.attemptTransitionRemoval(src, a, dest, invoker);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.ASimulation#calculateInfinityOfSCC(de.uni_freiburg.
	 * informatik.ultimate.util.scc.StronglyConnectedComponent)
	 */
	@Override
	protected int calculateInfinityOfSCC(final StronglyConnectedComponent<Vertex<LETTER, STATE>> scc) {
		if (m_IsCurrentlyDirectSimulation) {
			// In a direct simulation every SCC will have a local infinity of 1
			return 1;
		} else {
			// Use the original fair infinity
			return super.calculateInfinityOfSCC(scc);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.ASimulation#doSimulation()
	 */
	@Override
	protected void doSimulation() throws OperationCanceledException {
		// First calculate direct simulation
		if (getGameGraph() instanceof FairDirectGameGraph) {
			long startTime = System.currentTimeMillis();

			FairDirectGameGraph<LETTER, STATE> game = (FairDirectGameGraph<LETTER, STATE>) getGameGraph();

			// Do direct simulation
			getLogger().debug("Starting direct simulation...");
			m_IsCurrentlyDirectSimulation = true;
			game.transformToDirectGameGraph();
			new DirectSimulation<LETTER, STATE>(getServiceProvider(), m_Buechi, isUsingSCCs(), getStateFactory(), game);

			// Remember results before transforming back and clear changes made
			// in the direct simulation
			game.rememberAndClearDirectSimulationResults();

			// Transform back to fair simulation
			game.transformToFairGameGraph();
			m_IsCurrentlyDirectSimulation = false;

			long duration = System.currentTimeMillis() - startTime;
			getLogger().info((isUsingSCCs() ? "SCC version" : "nonSCC version") + " of direct simulation took "
					+ duration + " milliseconds");
			getLogger().debug("Starting fair simulation...");
		}

		// After that do the normal fair simulation process that will use the
		// overridden methods which profit from the direct simulation.
		super.doSimulation();
	}

	/**
	 * Returns if the simulation currently mimics the behavior of a
	 * DirectSimulation or a FairSimulation.
	 * 
	 * @return True if the simulation currently mimics the behavior of a
	 *         DirectSimulation, false if it mimics a FairSimulation.
	 */
	protected boolean isCurrentlyDirectGameGraph() {
		return m_IsCurrentlyDirectSimulation;
	}
}
