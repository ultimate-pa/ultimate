package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.summarycomputationgraph;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
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
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class ReduceNwaDirectSimulationB<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE> {
	
	private final IDoubleDeckerAutomaton<LETTER, STATE> mOperand;
	private final IDoubleDeckerAutomaton<LETTER, STATE> mResult;
	private final AutomataOperationStatistics mStatistics;

	public ReduceNwaDirectSimulationB(final AutomataLibraryServices services, final IStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		final Collection<Set<STATE>> possibleEquivalentClasses = new LookaheadPartitionConstructor<LETTER, STATE>(mServices, mOperand).getResult();
		final GameFactory gameFactory = new GameFactory();
		final DirectSimulationInfoProvider<LETTER, STATE> simulationInfoProvider = new DirectSimulationInfoProvider<>();
		final SpoilerNwaVertex<LETTER, STATE> uniqueSpoilerWinningSink = constructUniqueSpoilerWinninSink();
		final INestedWordAutomatonSimple<IGameLetter<LETTER, STATE>, IGameState> gameAutomaton = 
				new GameAutomaton<LETTER, STATE>(mServices, gameFactory, possibleEquivalentClasses, operand, simulationInfoProvider, uniqueSpoilerWinningSink);
		final IDoubleDeckerAutomaton<IGameLetter<LETTER, STATE>, IGameState> ga = new RemoveUnreachable<IGameLetter<LETTER, STATE>, IGameState>(mServices, gameAutomaton).getResult();
		final AGameGraph<LETTER, STATE> graph = new GameAutomatonToGamGraphTransformer<LETTER, STATE>(mServices, ga, uniqueSpoilerWinningSink, mOperand).getResult();
		final ASimulation<LETTER, STATE> sim = new ASimulation<LETTER, STATE>(null, mLogger, false, null, null) {

			@Override
			protected AGameGraph<LETTER, STATE> getGameGraph() {
				return graph;
			}
		};
		sim.doSimulation();
		assert (NwaSimulationUtil.areNwaSimulationResultsCorrect(graph, mOperand, ESimulationType.DIRECT,
				mLogger)) : "The computed simulation results are incorrect.";
		
		final HashRelation<STATE, STATE> simRelation = readoutSimulationRelation(graph, simulationInfoProvider, operand);
		final UnionFind<STATE> equivalenceRelation = computeEquivalenceRelation(simRelation, operand.getStates());
		if (mOperand.getCallAlphabet().isEmpty()) {
			final boolean addMapping = false;
			final QuotientNwaConstructor<LETTER, STATE> quotientNwaConstructor =
					new QuotientNwaConstructor<LETTER, STATE>(mServices, stateFactory, mOperand, equivalenceRelation, addMapping );
			mResult = (IDoubleDeckerAutomaton<LETTER, STATE>) quotientNwaConstructor.getResult();
		} else {
			final boolean mergeFinalAndNonFinalStates = false;
			final MinimizeNwaMaxSat2<LETTER, STATE> maxSatMinimizer = new MinimizeNwaMaxSat2<LETTER, STATE>(mServices, stateFactory, mOperand,
					!mergeFinalAndNonFinalStates, equivalenceRelation.getAllEquivalenceClasses(), false, false, false, true, false);
			mResult = maxSatMinimizer.getResult();
		}
		NwaSimulationUtil.retrieveGeneralNwaAutomataPerformance(sim.getSimulationPerformance(),
				mOperand, mResult, mServices);
		mStatistics = sim.getSimulationPerformance().exportToAutomataOperationStatistics();
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
	
	

}
