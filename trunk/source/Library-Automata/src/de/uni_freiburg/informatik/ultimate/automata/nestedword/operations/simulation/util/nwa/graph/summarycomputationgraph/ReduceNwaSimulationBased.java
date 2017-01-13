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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaPmaxSat;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaPmaxSatAsymmetric;
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
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Computes a simulation relation and applies PMax-SAT-based minimization afterward.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public abstract class ReduceNwaSimulationBased<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE> {
	private static final boolean DEFAULT_USE_BISIMULATION = true;
	
	private final IDoubleDeckerAutomaton<LETTER, STATE> mOperand;
	private final IDoubleDeckerAutomaton<LETTER, STATE> mResult;
	private final AutomataOperationStatistics mStatistics;
	
	/**
	 * @param services
	 *            Ultimate services.
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            operand
	 * @param simulationInfoProvider
	 *            simulation info provider
	 * @throws AutomataOperationCanceledException
	 *             if suboperations fail
	 */
	public ReduceNwaSimulationBased(final AutomataLibraryServices services, final IStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final ISimulationInfoProvider<LETTER, STATE> simulationInfoProvider)
			throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		final MinimizationBackend backend;
		if (isFiniteAutomaton()) {
			backend = MinimizationBackend.FINITE_AUTOMATON;
		} else if (DEFAULT_USE_BISIMULATION) {
			backend = MinimizationBackend.BISIMULATION;
		} else {
			backend = MinimizationBackend.SIMULATION;
		}
		
		mLogger.info(startMessage());
		
		final Collection<Set<STATE>> possibleEquivalentClasses =
				new LookaheadPartitionConstructor<>(mServices, mOperand).getPartition();
		final int sizeOfLargestEquivalenceClass =
				NestedWordAutomataUtils.computeSizeOfLargestEquivalenceClass(possibleEquivalentClasses);
		mLogger.info("Initial partition has " + possibleEquivalentClasses.size()
				+ " equivalence classes, largest equivalence class has " + sizeOfLargestEquivalenceClass + " states.");
		
		try {
			final GameFactory gameFactory = new GameFactory();
			final SpoilerNwaVertex<LETTER, STATE> uniqueSpoilerWinningSink = constructUniqueSpoilerWinningSink();
			final INestedWordAutomatonSimple<IGameLetter<LETTER, STATE>, IGameState> gameAutomaton;
			
			gameAutomaton = new GameAutomaton<>(mServices, gameFactory, possibleEquivalentClasses, operand,
					simulationInfoProvider, uniqueSpoilerWinningSink);
			final IDoubleDeckerAutomaton<IGameLetter<LETTER, STATE>, IGameState> ga =
					new RemoveUnreachable<>(mServices, gameAutomaton).getResult();
			final int gameAutomatonSize = ga.size();
			final SummaryComputation<LETTER, STATE> sc = new SummaryComputation<>(mServices, ga, mOperand);
			final AGameGraph<LETTER, STATE> graph = new GameAutomatonToGameGraphTransformer<>(mServices, ga,
					uniqueSpoilerWinningSink, mOperand, sc.getGameSummaries()).getResult();
			final ParsimoniousSimulation sim = new ParsimoniousSimulation(null, mLogger, false, null, null, graph);
			sim.doSimulation();
			
			assert NwaSimulationUtil.areNwaSimulationResultsCorrect(graph, mOperand, getSimulationType(),
					mLogger) : "The computed simulation results are incorrect.";
			
			switch (backend) {
				case FINITE_AUTOMATON:
					mResult = useFiniteAutomatonBackend(stateFactory, operand, simulationInfoProvider, graph);
					break;
				case BISIMULATION:
					mResult = useBisimulationBackend(stateFactory, operand, simulationInfoProvider, graph);
					break;
				case SIMULATION:
					mResult = useSimulationBackend(stateFactory, operand, simulationInfoProvider, graph);
					break;
				default:
					throw new IllegalArgumentException("Unknown backend type: " + backend);
			}
			
			sim.triggerComputationOfPerformanceData(mResult);
			sim.getSimulationPerformance();
			NwaSimulationUtil.retrieveGeneralNwaAutomataPerformance(sim.getSimulationPerformance(),
					mOperand, mResult, mServices);
			mStatistics = sim.getSimulationPerformance().exportToAutomataOperationStatistics();
			mStatistics.addKeyValuePair(StatisticsType.SIZE_MAXIMAL_INITIAL_EQUIVALENCE_CLASS,
					sizeOfLargestEquivalenceClass);
			mStatistics.addKeyValuePair(StatisticsType.SIZE_GAME_AUTOMATON,
					gameAutomatonSize);
			mStatistics.addKeyValuePair(StatisticsType.SIZE_GAME_GRAPH,
					graph.getSize());


			
		} catch (final AutomataOperationCanceledException aoce) {
			final RunningTaskInfo rti = new RunningTaskInfo(getClass(),
					NestedWordAutomataUtils.generateGenericMinimizationRunningTaskDescription(mOperand,
							possibleEquivalentClasses));
			aoce.addRunningTaskInfo(rti);
			throw aoce;
		}
		mLogger.info(exitMessage());
	}
	
	private boolean isFiniteAutomaton() {
		return mOperand.getReturnAlphabet().isEmpty();
	}
	
	private SpoilerNwaVertex<LETTER, STATE> constructUniqueSpoilerWinningSink() {
		return new SpoilerNwaVertex<>(1, false, null, null, new SpoilerWinningSink<>(null));
	}
	
	private UnionFind<STATE> computeEquivalenceRelation(final HashRelation<STATE, STATE> simRelation,
			final Set<STATE> set) {
		final UnionFind<STATE> result = new UnionFind<>();
		for (final STATE state : set) {
			result.makeEquivalenceClass(state);
		}
		for (final STATE state1 : simRelation.getDomain()) {
			for (final STATE state2 : simRelation.getImage(state1)) {
				if (simRelation.containsPair(state2, state1)) {
					final STATE state1rep = result.find(state1);
					final STATE state2rep = result.find(state2);
					result.union(state1rep, state2rep);
				}
			}
		}
		return result;
	}
	
	/**
	 * @return relation that contains a pair of states (q0, q1) iff the
	 *         analysis of the game graph yielded the information that the state q1
	 *         simulates the state q0.
	 */
	private void readoutSimulationRelation(final AGameGraph<LETTER, STATE> gameGraph,
			final ISimulationInfoProvider<LETTER, STATE> simulationInfoProvider,
			final INestedWordAutomatonSimple<LETTER, STATE> operand, final IBinaryRelation<STATE> simulationRelation) {
		for (final SpoilerVertex<LETTER, STATE> spoilerVertex : gameGraph.getSpoilerVertices()) {
			if (isAuxiliaryVertex(spoilerVertex)) {
				continue;
			}
			if ((simulationInfoProvider.isSimulationInformationProvider(spoilerVertex, operand))
					&& (spoilerVertex.getPM(null, gameGraph.getGlobalInfinity()) < gameGraph.getGlobalInfinity())) {
				simulationRelation.addPair(spoilerVertex.getQ0(), spoilerVertex.getQ1());
			}
		}
	}
	
	/**
	 * Workaround to check if vertex is auxiliary vertex. This method check
	 * if one the vertex' states is null. In the future we want to have
	 * separate classes for auxiliary vertices.
	 */
	private boolean isAuxiliaryVertex(final SpoilerVertex<LETTER, STATE> spoilerVertex) {
		return spoilerVertex.getQ0() == null || spoilerVertex.getQ1() == null;
	}
	
	private UnionFind<STATE> simulationToEquivalenceRelation(final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final ISimulationInfoProvider<LETTER, STATE> simulationInfoProvider,
			final AGameGraph<LETTER, STATE> graph) {
		final HashRelationBackedBinaryRelation simRelation = new HashRelationBackedBinaryRelation();
		readoutSimulationRelation(graph, simulationInfoProvider, operand, simRelation);
		return computeEquivalenceRelation(simRelation.getSimulation(), operand.getStates());
	}
	
	private IDoubleDeckerAutomaton<LETTER, STATE> useFiniteAutomatonBackend(final IStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final ISimulationInfoProvider<LETTER, STATE> simulationInfoProvider,
			final AGameGraph<LETTER, STATE> graph) {
		final UnionFind<STATE> equivalenceRelation =
				simulationToEquivalenceRelation(operand, simulationInfoProvider, graph);
		final boolean addMapping = false;
		final QuotientNwaConstructor<LETTER, STATE> quotientNwaConstructor =
				new QuotientNwaConstructor<>(mServices, stateFactory, mOperand, equivalenceRelation, addMapping);
		return (IDoubleDeckerAutomaton<LETTER, STATE>) quotientNwaConstructor.getResult();
	}
	
	private IDoubleDeckerAutomaton<LETTER, STATE> useBisimulationBackend(final IStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final ISimulationInfoProvider<LETTER, STATE> simulationInfoProvider, final AGameGraph<LETTER, STATE> graph)
			throws AutomataOperationCanceledException {
		final UnionFind<STATE> equivalenceRelation =
				simulationToEquivalenceRelation(operand, simulationInfoProvider, graph);
		final boolean mergeFinalAndNonFinalStates = simulationInfoProvider.mayMergeFinalAndNonFinalStates();
		final MinimizeNwaPmaxSat<LETTER, STATE> maxSatMinimizer =
				new MinimizeNwaPmaxSat<>(mServices, stateFactory, mOperand,
						equivalenceRelation.getAllEquivalenceClasses(),
						new MinimizeNwaMaxSat2.Settings<STATE>()
								.setFinalStateConstraints(!mergeFinalAndNonFinalStates));
		return maxSatMinimizer.getResult();
	}
	
	private IDoubleDeckerAutomaton<LETTER, STATE> useSimulationBackend(final IStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final ISimulationInfoProvider<LETTER, STATE> simulationInfoProvider,
			final AGameGraph<LETTER, STATE> graph) throws AutomataOperationCanceledException {
		final NestedMapBackedBinaryRelation simRelation = new NestedMapBackedBinaryRelation();
		readoutSimulationRelation(graph, simulationInfoProvider, operand, simRelation);
		
		final boolean mergeFinalAndNonFinalStates = simulationInfoProvider.mayMergeFinalAndNonFinalStates();
		final MinimizeNwaPmaxSatAsymmetric<LETTER, STATE> maxSatMinimizer =
				new MinimizeNwaPmaxSatAsymmetric<>(mServices, stateFactory, mOperand, simRelation.getSimulation(),
						new MinimizeNwaMaxSat2.Settings<STATE>()
								.setFinalStateConstraints(!mergeFinalAndNonFinalStates));
		return maxSatMinimizer.getResult();
	}
	
	@Override
	public IDoubleDeckerAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}
	
	@Override
	protected IDoubleDeckerAutomaton<LETTER, STATE> getOperand() {
		return mOperand;
	}
	
	protected abstract ESimulationType getSimulationType();
	
	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		return mStatistics;
	}
	
	/**
	 * Which PMax-SAT-based backend to use for minimization.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private enum MinimizationBackend {
		/**
		 * Finite automaton minimization.
		 */
		FINITE_AUTOMATON,
		/**
		 * Bisimulation minimization.
		 */
		BISIMULATION,
		/**
		 * Simulation minimization.
		 */
		SIMULATION
	}
	
	/**
	 * General data structure interface to store pairs.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 * @param <T>
	 *            element type
	 */
	@FunctionalInterface
	private interface IBinaryRelation<T> {
		void addPair(T state1, T state2);
	}
	
	/**
	 * {@link HashRelation} data structure.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private class HashRelationBackedBinaryRelation implements IBinaryRelation<STATE> {
		private final HashRelation<STATE, STATE> mSimulation;
		
		public HashRelationBackedBinaryRelation() {
			mSimulation = new HashRelation<>();
		}
		
		@Override
		public void addPair(final STATE state1, final STATE state2) {
			mSimulation.addPair(state1, state2);
		}
		
		public HashRelation<STATE, STATE> getSimulation() {
			return mSimulation;
		}
	}
	
	/**
	 * {@link NestedMap2} data structure.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private class NestedMapBackedBinaryRelation implements IBinaryRelation<STATE> {
		private final NestedMap2<STATE, STATE, Pair<STATE, STATE>> mSimulation;
		
		public NestedMapBackedBinaryRelation() {
			mSimulation = new NestedMap2<>();
		}
		
		@Override
		public void addPair(final STATE state1, final STATE state2) {
			mSimulation.put(state1, state2, new Pair<>(state1, state2));
		}
		
		public NestedMap2<STATE, STATE, Pair<STATE, STATE>> getSimulation() {
			return mSimulation;
		}
	}
	
	private class ParsimoniousSimulation extends ASimulation<LETTER, STATE> {
		private final AGameGraph<LETTER, STATE> mGameGraph;
		
		public ParsimoniousSimulation(final IProgressAwareTimer progressTimer, final ILogger logger,
				final boolean useSccs, final IStateFactory<STATE> stateFactory, final ESimulationType simType,
				final AGameGraph<LETTER, STATE> gameGraph) throws AutomataOperationCanceledException {
			super(progressTimer, logger, useSccs, stateFactory, simType);
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
