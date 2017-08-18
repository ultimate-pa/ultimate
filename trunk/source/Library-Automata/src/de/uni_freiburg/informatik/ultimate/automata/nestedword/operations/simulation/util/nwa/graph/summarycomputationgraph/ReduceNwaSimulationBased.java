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
import java.util.Iterator;
import java.util.Set;
import java.util.function.BiPredicate;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.AbstractMinimizeNwaDd;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizationStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaMaxSat2;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaMaxSat2.Settings;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaPmaxSat;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaPmaxSatDirect;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaPmaxSatDirectBi;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.NwaApproximateBisimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.NwaApproximateSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.NwaApproximateXsimulation.SimulationType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.QuotientNwaConstructor;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ASimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.SimulationOrMinimizationType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.NwaSimulationUtil;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.SpoilerNwaVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.SpoilerWinningSink;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.GameFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.IGameLetter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.IGameState;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.util.HashRelationBackedSetOfPairs;
import de.uni_freiburg.informatik.ultimate.automata.util.ISetOfPairs;
import de.uni_freiburg.informatik.ultimate.automata.util.NestedMapBackedSetOfPairs;
import de.uni_freiburg.informatik.ultimate.automata.util.PartitionAndMapBackedSetOfPairs;
import de.uni_freiburg.informatik.ultimate.automata.util.PartitionBackedSetOfPairs;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
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
public abstract class ReduceNwaSimulationBased<LETTER, STATE> extends AbstractMinimizeNwaDd<LETTER, STATE> {
	private static final boolean DEFAULT_USE_BISIMULATION = false;
	private static final boolean DEFAULT_USE_BISIMULATION_PREPROCESSING = false;
	private static final boolean OMIT_MAX_SAT_FOR_FINITE_AUTOMATA = false;
	private static final boolean USE_FULL_PREPROCESSING = false;

	private final IDoubleDeckerAutomaton<LETTER, STATE> mOperand;
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
	public ReduceNwaSimulationBased(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final ISimulationInfoProvider<LETTER, STATE> simulationInfoProvider)
			throws AutomataOperationCanceledException {
		super(services, stateFactory);
		mOperand = operand;
		final MinimizationBackend backend;
		if (OMIT_MAX_SAT_FOR_FINITE_AUTOMATA && NestedWordAutomataUtils.isFiniteAutomaton(mOperand)) {
			backend = MinimizationBackend.FINITE_AUTOMATON;
		} else if (DEFAULT_USE_BISIMULATION) {
			backend = MinimizationBackend.BISIMULATION;
		} else {
			backend = MinimizationBackend.SIMULATION;
		}

		printStartMessage();

		final ISetOfPairs<STATE, ?> initialPairs;
		final int sizeOfLargestEquivalenceClass;
		long timer = System.currentTimeMillis();
		if (DEFAULT_USE_BISIMULATION_PREPROCESSING) {
			final PartitionBackedSetOfPairs<STATE> partitionBackedSetOfPairs =
					new NwaApproximateBisimulation<>(services, operand,
							simulationInfoProvider.mayMergeFinalAndNonFinalStates()
									? SimulationType.ORDINARY
									: SimulationType.DIRECT,
							USE_FULL_PREPROCESSING).getResult();
			final Collection<Set<STATE>> initialPartition = partitionBackedSetOfPairs.getRelation();
			initialPairs = new PartitionAndMapBackedSetOfPairs<>(initialPartition);
			sizeOfLargestEquivalenceClass =
					NestedWordAutomataUtils.computeSizeOfLargestEquivalenceClass(initialPartition);
			mLogger.info("Initial partition has " + initialPartition.size()
					+ " equivalence classes, largest equivalence class has " + sizeOfLargestEquivalenceClass
					+ " states.");
		} else {
			initialPairs =
					new NwaApproximateSimulation<>(services, operand,
							simulationInfoProvider.mayMergeFinalAndNonFinalStates()
									? SimulationType.ORDINARY
									: SimulationType.DIRECT,
							USE_FULL_PREPROCESSING).getResult();
			sizeOfLargestEquivalenceClass = -1;
		}
		final long timePreprocessing = System.currentTimeMillis() - timer;

		timer = System.currentTimeMillis();
		long timeSimulation;
		try {
			final GameFactory gameFactory = new GameFactory();
			final SpoilerNwaVertex<LETTER, STATE> uniqueSpoilerWinningSink = constructUniqueSpoilerWinningSink();
			final INwaOutgoingLetterAndTransitionProvider<IGameLetter<LETTER, STATE>, IGameState> gameAutomaton;

			gameAutomaton = new GameAutomaton<>(mServices, gameFactory, initialPairs, operand, simulationInfoProvider,
					uniqueSpoilerWinningSink);
			final IDoubleDeckerAutomaton<IGameLetter<LETTER, STATE>, IGameState> ga =
					new RemoveUnreachable<>(mServices, gameAutomaton).getResult();
			final int gameAutomatonSize = ga.size();
			final SummaryComputation<LETTER, STATE> sc = new SummaryComputation<>(mServices, ga, mOperand);
			final AGameGraph<LETTER, STATE> graph = new GameAutomatonToGameGraphTransformer<>(mServices, ga,
					uniqueSpoilerWinningSink, mOperand, sc.getGameSummaries()).getResult();
			final ParsimoniousSimulation sim =
					new ParsimoniousSimulation(mServices.getProgressAwareTimer(), mLogger, false, null, null, graph);
			sim.doSimulation();
			timeSimulation = System.currentTimeMillis() - timer;

			assert NwaSimulationUtil.areNwaSimulationResultsCorrect(graph, mOperand, getSimulationType(),
					initialPairs::containsPair, mLogger) : "The computed simulation results are incorrect.";
			Pair<IDoubleDeckerAutomaton<LETTER, STATE>, MinimizeNwaMaxSat2<LETTER, STATE, ?>> resultPair;
			switch (backend) {
				case FINITE_AUTOMATON:
					resultPair = useFiniteAutomatonBackend(stateFactory, operand, simulationInfoProvider, graph);
					break;
				case BISIMULATION:
					resultPair = useBisimulationBackend(stateFactory, operand, simulationInfoProvider, graph);
					break;
				case SIMULATION:
					resultPair = useSimulationBackend(stateFactory, operand, simulationInfoProvider, graph);
					break;
				default:
					throw new IllegalArgumentException("Unknown backend type: " + backend);
			}
			final IDoubleDeckerAutomaton<LETTER, STATE> result = resultPair.getFirst();
			super.directResultConstruction(result);

			sim.triggerComputationOfPerformanceData(result);
			sim.getSimulationPerformance();
			NwaSimulationUtil.retrieveGeneralNwaAutomataPerformance(sim.getSimulationPerformance(), mOperand, result,
					mServices);

			mStatistics = collectStatistics(initialPairs, sizeOfLargestEquivalenceClass, gameAutomatonSize, graph, sim,
					resultPair, timePreprocessing, timeSimulation);

		} catch (final AutomataOperationCanceledException aoce) {
			if (initialPairs instanceof PartitionBackedSetOfPairs<?>) {
				final Collection<Set<STATE>> initialPartition =
						((PartitionBackedSetOfPairs<STATE>) initialPairs).getRelation();
				final RunningTaskInfo rti = new RunningTaskInfo(getClass(),
						NestedWordAutomataUtils.generateGenericMinimizationRunningTaskDescription(getOperationName(),
								mOperand, initialPartition));
				aoce.addRunningTaskInfo(rti);
			} else {
				addGenericRunningTaskInfo(aoce);
			}
			throw aoce;
		}
		printExitMessage();
	}

	private AutomataOperationStatistics collectStatistics(final ISetOfPairs<STATE, ?> initialPairs,
			final int sizeOfLargestEquivalenceClass, final int gameAutomatonSize, final AGameGraph<LETTER, STATE> graph,
			final ParsimoniousSimulation sim,
			final Pair<IDoubleDeckerAutomaton<LETTER, STATE>, MinimizeNwaMaxSat2<LETTER, STATE, ?>> resultPair,
			final long timePreprocessing, final long timeSimulation) {
		final AutomataOperationStatistics statistics = new AutomataOperationStatistics();
		statistics.addKeyValuePair(StatisticsType.TIME_PREPROCESSING, timePreprocessing);
		statistics.addKeyValuePair(StatisticsType.TIME_SIMULATION, timeSimulation);
		if (initialPairs instanceof PartitionBackedSetOfPairs<?>) {
			final Collection<Set<STATE>> possibleEquivalentClasses =
					((PartitionBackedSetOfPairs<STATE>) initialPairs).getRelation();
			statistics.addKeyValuePair(StatisticsType.NUMBER_INITIAL_PAIRS,
					new PartitionAndMapBackedSetOfPairs<>(possibleEquivalentClasses)
							.getOrConstructPartitionSizeInformation().getNumberOfPairs());
			statistics.addKeyValuePair(StatisticsType.SIZE_INITIAL_PARTITION, possibleEquivalentClasses.size());
			statistics.addKeyValuePair(StatisticsType.SIZE_MAXIMAL_INITIAL_BLOCK, sizeOfLargestEquivalenceClass);

		} else {
			long numberOfPairs = 0;
			for (final Iterator<Pair<STATE, STATE>> it = initialPairs.iterator(); it.hasNext(); it.next()) {
				++numberOfPairs;
			}
			statistics.addKeyValuePair(StatisticsType.NUMBER_INITIAL_PAIRS, numberOfPairs);
		}
		statistics.addKeyValuePair(StatisticsType.SIZE_GAME_AUTOMATON, gameAutomatonSize);
		statistics.addKeyValuePair(StatisticsType.SIZE_GAME_GRAPH, graph.getSize());
		final MinimizeNwaMaxSat2<LETTER, STATE, ?> maxSatMinimizer = resultPair.getSecond();
		if (maxSatMinimizer != null) {
			maxSatMinimizer.addStatistics(statistics);
		}
		return statistics;
	}

	private static <LETTER, STATE> SpoilerNwaVertex<LETTER, STATE> constructUniqueSpoilerWinningSink() {
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
	 * @return relation that contains a pair of states (q0, q1) iff the analysis of the game graph yielded the
	 *         information that the state q1 simulates the state q0.
	 */
	private void readoutSimulationRelation(final AGameGraph<LETTER, STATE> gameGraph,
			final ISimulationInfoProvider<LETTER, STATE> simulationInfoProvider,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand, final ISetOfPairs<STATE, ?> simulationRelation) {
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
	 * Workaround to check if vertex is auxiliary vertex. This method check if one the vertex' states is null. In the
	 * future we want to have separate classes for auxiliary vertices.
	 */
	private boolean isAuxiliaryVertex(final SpoilerVertex<LETTER, STATE> spoilerVertex) {
		return spoilerVertex.getQ0() == null || spoilerVertex.getQ1() == null;
	}

	private UnionFind<STATE> simulationToEquivalenceRelation(final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final ISimulationInfoProvider<LETTER, STATE> simulationInfoProvider,
			final AGameGraph<LETTER, STATE> graph) {
		final HashRelationBackedSetOfPairs<STATE> simRelation = new HashRelationBackedSetOfPairs<>();
		readoutSimulationRelation(graph, simulationInfoProvider, operand, simRelation);
		return computeEquivalenceRelation(simRelation.getRelation(), operand.getStates());
	}

	private Pair<IDoubleDeckerAutomaton<LETTER, STATE>, MinimizeNwaMaxSat2<LETTER, STATE, ?>> useFiniteAutomatonBackend(
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final ISimulationInfoProvider<LETTER, STATE> simulationInfoProvider,
			final AGameGraph<LETTER, STATE> graph) {
		final UnionFind<STATE> equivalenceRelation =
				simulationToEquivalenceRelation(operand, simulationInfoProvider, graph);
		final boolean addMapping = false;
		final QuotientNwaConstructor<LETTER, STATE> quotientNwaConstructor =
				new QuotientNwaConstructor<>(mServices, stateFactory, mOperand, equivalenceRelation, addMapping);
		return new Pair<>((IDoubleDeckerAutomaton<LETTER, STATE>) quotientNwaConstructor.getResult(), null);
	}

	private Pair<IDoubleDeckerAutomaton<LETTER, STATE>, MinimizeNwaMaxSat2<LETTER, STATE, ?>> useBisimulationBackend(
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final ISimulationInfoProvider<LETTER, STATE> simulationInfoProvider, final AGameGraph<LETTER, STATE> graph)
			throws AutomataOperationCanceledException {
		final UnionFind<STATE> equivalenceRelation =
				simulationToEquivalenceRelation(operand, simulationInfoProvider, graph);

		final Settings<STATE> settings = getPmaxSatSettings(simulationInfoProvider);
		final MinimizeNwaPmaxSat<LETTER, STATE> maxSatMinimizer = new MinimizeNwaPmaxSatDirectBi<>(mServices, stateFactory,
				mOperand, new PartitionBackedSetOfPairs<>(equivalenceRelation.getAllEquivalenceClasses()), settings);
		return new Pair<>(maxSatMinimizer.getResult(), maxSatMinimizer);
	}

	private Pair<IDoubleDeckerAutomaton<LETTER, STATE>, MinimizeNwaMaxSat2<LETTER, STATE, ?>> useSimulationBackend(
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final ISimulationInfoProvider<LETTER, STATE> simulationInfoProvider, final AGameGraph<LETTER, STATE> graph)
			throws AutomataOperationCanceledException {
		final NestedMapBackedSetOfPairs<STATE> simRelation = new NestedMapBackedSetOfPairs<>();
		readoutSimulationRelation(graph, simulationInfoProvider, operand, simRelation);

		final Settings<STATE> settings = getPmaxSatSettings(simulationInfoProvider);
		final MinimizeNwaPmaxSatDirect<LETTER, STATE> maxSatMinimizer = new MinimizeNwaPmaxSatDirect<>(
				mServices, stateFactory, mOperand, simRelation.getRelation(), settings);
		return new Pair<>(maxSatMinimizer.getResult(), maxSatMinimizer);
	}

	private Settings<STATE> getPmaxSatSettings(final ISimulationInfoProvider<LETTER, STATE> simulationInfoProvider) {
		final boolean mergeFinalAndNonFinalStates = simulationInfoProvider.mayMergeFinalAndNonFinalStates();
		final BiPredicate<STATE, STATE> finalNonfinalConstraint = mergeFinalAndNonFinalStates
				? new MinimizeNwaMaxSat2.RelationBackedBiPredicate<>(new HashRelationBackedSetOfPairs<>())
				: new MinimizeNwaMaxSat2.TrueBiPredicate<>();
		final Settings<STATE> settings =
				new MinimizeNwaMaxSat2.Settings<STATE>().setFinalNonfinalConstraintPredicate(finalNonfinalConstraint);
		return settings;
	}

	@Override
	protected IDoubleDeckerAutomaton<LETTER, STATE> getOperand() {
		return mOperand;
	}

	protected abstract SimulationOrMinimizationType getSimulationType();

	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		final AutomataOperationStatistics statistics = super.getAutomataOperationStatistics();
		statistics.addAllStatistics(mStatistics);
		return statistics;
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

	private class ParsimoniousSimulation extends ASimulation<LETTER, STATE> {
		private final AGameGraph<LETTER, STATE> mGameGraph;

		public ParsimoniousSimulation(final IProgressAwareTimer progressTimer, final ILogger logger,
				final boolean useSccs, final IStateFactory<STATE> stateFactory,
				final SimulationOrMinimizationType simType, final AGameGraph<LETTER, STATE> gameGraph)
				throws AutomataOperationCanceledException {
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
