/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.summarycomputationgraph;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.LookaheadPartitionConstructor;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaMaxSat2;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.QuotientNwaConstructor;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ASimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ESimulationType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.NwaSimulationUtil;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.SpoilerNwaVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.SpoilerWinningSink;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.GameFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.IGameLetter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.IGameState;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.util.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <STATE>
 */
public abstract class ReduceNwaSimulationBased<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE> {
	
	private final IDoubleDeckerAutomaton<LETTER, STATE> mOperand;
	private final IDoubleDeckerAutomaton<LETTER, STATE> mResult;
	private final AutomataOperationStatistics mStatistics;

	public ReduceNwaSimulationBased(final AutomataLibraryServices services, final IStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand, final ISimulationInfoProvider<LETTER, STATE> simulationInfoProvider) throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		
		final Collection<Set<STATE>> possibleEquivalentClasses = new LookaheadPartitionConstructor<LETTER, STATE>(mServices, mOperand).getResult();
		final int sizeOfLargestEquivalenceClass = NestedWordAutomataUtils.computeSizeOfLargestEquivalenceClass(possibleEquivalentClasses);
		mLogger.info("Initial partition has " + possibleEquivalentClasses.size() + 
				" equivalence classes, largest equivalence class has " + sizeOfLargestEquivalenceClass + " states.");
		
		try {
		
			final GameFactory gameFactory = new GameFactory();
			final SpoilerNwaVertex<LETTER, STATE> uniqueSpoilerWinningSink = constructUniqueSpoilerWinninSink();
			final INestedWordAutomatonSimple<IGameLetter<LETTER, STATE>, IGameState> gameAutomaton;

			gameAutomaton = new GameAutomaton<LETTER, STATE>(mServices, gameFactory, possibleEquivalentClasses, operand, simulationInfoProvider, uniqueSpoilerWinningSink);
			final IDoubleDeckerAutomaton<IGameLetter<LETTER, STATE>, IGameState> ga = new RemoveUnreachable<IGameLetter<LETTER, STATE>, IGameState>(mServices, gameAutomaton).getResult();
			final AGameGraph<LETTER, STATE> graph = new GameAutomatonToGamGraphTransformer<LETTER, STATE>(mServices, ga, uniqueSpoilerWinningSink, mOperand).getResult();
			final ParsimoniousSimulation sim = new ParsimoniousSimulation(null, mLogger, false, null, null, graph);
			sim.doSimulation();
			final HashRelation<STATE, STATE> simRelation = readoutSimulationRelation(graph, simulationInfoProvider, operand);
			final UnionFind<STATE> equivalenceRelation = computeEquivalenceRelation(simRelation, operand.getStates());

			assert (NwaSimulationUtil.areNwaSimulationResultsCorrect(graph, mOperand, ESimulationType.DIRECT,
					mLogger)) : "The computed simulation results are incorrect.";

			if (mOperand.getCallAlphabet().isEmpty()) {
				final boolean addMapping = false;
				final QuotientNwaConstructor<LETTER, STATE> quotientNwaConstructor =
						new QuotientNwaConstructor<LETTER, STATE>(mServices, stateFactory, mOperand, equivalenceRelation, addMapping );
				mResult = (IDoubleDeckerAutomaton<LETTER, STATE>) quotientNwaConstructor.getResult();
			} else {
				final boolean mergeFinalAndNonFinalStates = simulationInfoProvider.mayMergeFinalAndNonFinalStates();
				final MinimizeNwaMaxSat2<LETTER, STATE> maxSatMinimizer = new MinimizeNwaMaxSat2<LETTER, STATE>(mServices, stateFactory, mOperand,
						!mergeFinalAndNonFinalStates, equivalenceRelation.getAllEquivalenceClasses(), false, false, false, true, false);
				mResult = maxSatMinimizer.getResult();
			}
			sim.triggerComputationOfPerformanceData(mResult);
			sim.getSimulationPerformance();
			NwaSimulationUtil.retrieveGeneralNwaAutomataPerformance(sim.getSimulationPerformance(),
					mOperand, mResult, mServices);
			mStatistics = sim.getSimulationPerformance().exportToAutomataOperationStatistics();
			mStatistics.addKeyValuePair(StatisticsType.SIZE_MAXIMAL_INITIAL_EQUIVALENCE_CLASS, sizeOfLargestEquivalenceClass);
		
		} catch (final ToolchainCanceledException tce) {
			final RunningTaskInfo rti = new RunningTaskInfo(getClass(), 
					NestedWordAutomataUtils.generateGenericMinimizationRunningTaskDescription(mOperand, possibleEquivalentClasses));
			tce.addRunningTaskInfo(rti);
			throw tce;
		}

	}

	private SpoilerNwaVertex<LETTER, STATE> constructUniqueSpoilerWinninSink() {
		final SpoilerNwaVertex<LETTER, STATE> uniqueSpoilerWinningSink = new SpoilerNwaVertex<LETTER, STATE>(1, false, null, null, new SpoilerWinningSink<>(null));
		return uniqueSpoilerWinningSink;
	}

	private UnionFind<STATE> computeEquivalenceRelation(final HashRelation<STATE, STATE> simRelation, final Set<STATE> set) {
		final UnionFind<STATE> result = new UnionFind<>();
		for (final STATE state : set) {
			result.makeEquivalenceClass(state);
		}
		for (final STATE q0 : simRelation.getDomain()) {
			for (final STATE q1 : simRelation.getImage(q0)) {
				if (simRelation.containsPair(q1, q0)) {
					final STATE q0rep = result.find(q0);
					final STATE q1rep = result.find(q1);
					result.union(q0rep, q1rep);
				}
			}
		}
		return result;
	}

	/**
	 * @return relation that contains a pair of states (q0, q1) iff the 
	 * analysis of the game graph yielded the information that the state q1 
	 * simulates the state q0.
	 */
	private HashRelation<STATE, STATE> readoutSimulationRelation(final AGameGraph<LETTER, STATE> gameGraph,
			final ISimulationInfoProvider<LETTER, STATE> simulationInfoProvider, final INestedWordAutomatonSimple<LETTER, STATE> operand) {
		final HashRelation<STATE, STATE> result = new HashRelation<>();
		for (final SpoilerVertex<LETTER, STATE> spoilerVertex : gameGraph.getSpoilerVertices()) {
			if (!isAuxiliaryVertex(spoilerVertex)) {
				if(simulationInfoProvider.isSimulationInformationProvider(spoilerVertex, operand)) {
					if (spoilerVertex.getPM(null, gameGraph.getGlobalInfinity()) < gameGraph.getGlobalInfinity()) {
						result.addPair(spoilerVertex.getQ0(), spoilerVertex.getQ1());
					}

				}
			}
		}
		return result;
	}

	/**
	 * Workaround to check if vertex is auxiliary vertex. This method check
	 * if one the vertex' states is null. In the future we want to have
	 * separate classes for auxiliary vertices. 
	 */
	private boolean isAuxiliaryVertex(final SpoilerVertex<LETTER, STATE> spoilerVertex) {
		return spoilerVertex.getQ0() == null || spoilerVertex.getQ1() == null;
	}

	@Override
	public IDoubleDeckerAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}

	@Override
	protected IDoubleDeckerAutomaton<LETTER, STATE> getOperand() {
		return mOperand;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.automata.IOperation#getAutomataOperationStatistics()
	 */
	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		return mStatistics;
	}
	
	
	
	private class ParsimoniousSimulation extends ASimulation<LETTER, STATE> {
		
		private final AGameGraph<LETTER, STATE> mGameGraph;
		
		

		public ParsimoniousSimulation(final IProgressAwareTimer progressTimer, final ILogger logger, final boolean useSCCs,
				final IStateFactory<STATE> stateFactory, final ESimulationType simType, final AGameGraph<LETTER, STATE> gameGraph)
				throws AutomataOperationCanceledException {
			super(progressTimer, logger, useSCCs, stateFactory, simType);
			mGameGraph = gameGraph;
		}

		public void triggerComputationOfPerformanceData(final IDoubleDeckerAutomaton<LETTER, STATE> result) {
			super.mResult = result;
			super.retrieveGeneralAutomataPerformance();
		}

		@Override
		protected AGameGraph<LETTER, STATE> getGameGraph() {
			return mGameGraph;
		}
		
	}
	

}
