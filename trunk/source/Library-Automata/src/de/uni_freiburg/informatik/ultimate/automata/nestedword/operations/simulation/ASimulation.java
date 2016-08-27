/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
 * Buchi automata state space reduction algorithm based on the following paper:
 * "Fair simulation relations, parity games and state space reduction for
 * Buchi automata" - Etessami, Wilke and Schuller.
 * 
 * Algorithm optimized to work using strongly connected components.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation;

import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.PriorityQueue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Analyze;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Analyze.ESymbolType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance.ECountingMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance.EMultipleDataOption;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance.ETimeMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance.SimulationPerformance;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.VertexPmReverseComparator;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.util.scc.DefaultStronglyConnectedComponentFactory;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * Abstract class for simulations which can be used for <b>reducing buechi
 * automaton</b>.<br/>
 * <br/>
 * 
 * The simulation sets a {@link AGameGraph} object up that is based on the
 * original buechi automaton. It then simulates the game, explained in
 * {@link AGameGraph}, and calculates so called progress measure for every
 * vertex of the graph.<br/>
 * The simulation does so by comparing vertices with their neighbors and
 * choosing the optimal transition based on which player is at turn.
 * <i>Duplicator</i> wants to decrease the progress measure, which is done by
 * visiting vertices with priority 0, and <i>Spoiler</i> wants to increase it by
 * visiting odd priorities.<br/>
 * <br/>
 * 
 * For correctness its important that the inputed automaton has <b>no dead
 * ends</b> nor <b>duplicate transitions</b>.<br/>
 * <br/>
 * 
 * The exact conditions are determined by the type of game graph. If, for a
 * vertex (q0, q1), the progress measure does not reach infinity we say q1
 * simulates q0.<br/>
 * This simulation information can then be used for buechi reduction. In some
 * types of simulation such simulating states can be merged without changing the
 * underlying language.<br/>
 * <br/>
 * 
 * After starting the simulation, its result can be accessed by using
 * {@link #getResult()}.<br/>
 * <br/>
 * 
 * For game graphs see {@link AGameGraph}, for information on the magic infinity
 * bound see {@link AGameGraph#getGlobalInfinity()}.<br/>
 * <br/>
 * 
 * The simulation process runs in <b>O(n^3 * k)</b> time and <b>O(n * k)</b>
 * space where n is the amount of states and k the amount of transitions from
 * the inputed automaton.<br/>
 * The algorithm is based on the paper: <i>Fair simulation relations, parity
 * games, and state space reduction for büchi automata</i> by <i>Etessami, Wilke
 * and Schuller</i>.
 * 
 * @author Daniel Tischner
 * @author Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * @author Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * 
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public abstract class ASimulation<LETTER, STATE> {

	/**
	 * The logger used by the Ultimate framework.
	 */
	private final ILogger mLogger;
	/**
	 * Holds information about the performance of the simulation after usage.
	 */
	private final SimulationPerformance mPerformance;
	/**
	 * Timer used for responding to timeouts and operation cancellation.
	 */
	private final IProgressAwareTimer mProgressTimer;
	/**
	 * The resulting possible reduced buechi automaton.
	 */
	private INestedWordAutomaton<LETTER, STATE> mResult;
	/**
	 * The object that computes the SCCs of a given buechi automaton.
	 */
	private SccComputation<Vertex<LETTER, STATE>, StronglyConnectedComponent<Vertex<LETTER, STATE>>> mSccComp;
	/**
	 * The state factory used for creating states.
	 */
	private final IStateFactory<STATE> mStateFactory;
	/**
	 * If the simulation calculation should be optimized using SCC, Strongly
	 * Connected Components.
	 */
	private boolean mUseSCCs;
	/**
	 * Comparator that compares two given vertices by their progress measure
	 * whereas a higher measure gets favored before a smaller.<br/>
	 * This is used to implement the @link {@link #mWorkingList working list} as
	 * a priority queue that first works vertices with high measures.
	 */
	private final VertexPmReverseComparator<LETTER, STATE> mVertexComp;
	/**
	 * The internal working list of the simulation that, in general, gets
	 * initiated with vertices that have priority 1. It contains vertices that
	 * benefit from a progress measure update of its neighbors and therefore
	 * they need to be updated itself.<br/>
	 * The list is implemented as priority queue that first works vertices with
	 * the highest progress measure.
	 */
	private PriorityQueue<Vertex<LETTER, STATE>> mWorkingList;

	/**
	 * Creates a new simulation that initiates all needed data structures and
	 * fields.
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
	 * @param simType
	 *            Type of the simulation implementing.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public ASimulation(final IProgressAwareTimer progressTimer, final ILogger logger, final boolean useSCCs,
			final IStateFactory<STATE> stateFactory, final ESimulationType simType)
					throws AutomataOperationCanceledException {
		mProgressTimer = progressTimer;
		mLogger = logger;
		mUseSCCs = useSCCs;
		mStateFactory = stateFactory;
		mVertexComp = new VertexPmReverseComparator<>();

		mSccComp = null;

		mPerformance = new SimulationPerformance(simType, useSCCs);
	}

	/**
	 * Starts the simulation that calculates the corresponding progress measures
	 * to all vertices of the underlying game graph. After that it uses that
	 * information to possible reduce the inputed buechi automaton and finally
	 * assigns the result which then can be accessed by {@link #getResult()}.
	 * 
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public void doSimulation() throws AutomataOperationCanceledException {
		mPerformance.startTimeMeasure(ETimeMeasure.OVERALL);
		mPerformance.startTimeMeasure(ETimeMeasure.SIMULATION_ONLY);

		if (mUseSCCs) { // calculate reduction with SCC
			mPerformance.startTimeMeasure(ETimeMeasure.BUILD_SCC);
			final DefaultStronglyConnectedComponentFactory<Vertex<LETTER, STATE>> sccFactory = new DefaultStronglyConnectedComponentFactory<>();
			final GameGraphSuccessorProvider<LETTER, STATE> succProvider = new GameGraphSuccessorProvider<>(
					getGameGraph());
			mSccComp = new SccComputation<>(mLogger, succProvider, sccFactory, getGameGraph().getSize(),
					getGameGraph().getVertices());

			final Iterator<StronglyConnectedComponent<Vertex<LETTER, STATE>>> iter = new LinkedList<StronglyConnectedComponent<Vertex<LETTER, STATE>>>(
					mSccComp.getSCCs()).iterator();
			mPerformance.stopTimeMeasure(ETimeMeasure.BUILD_SCC);
			int amountOfSCCs = 0;
			while (iter.hasNext()) {
				final StronglyConnectedComponent<Vertex<LETTER, STATE>> scc = iter.next();
				iter.remove();
				efficientLiftingAlgorithm(calculateInfinityOfSCC(scc), scc.getNodes());
				amountOfSCCs++;
			}
			mPerformance.setCountingMeasure(ECountingMeasure.SCCS, amountOfSCCs);
		} else { // calculate reduction w/o SCCs
			efficientLiftingAlgorithm(getGameGraph().getGlobalInfinity(), null);
			mPerformance.addTimeMeasureValue(ETimeMeasure.BUILD_SCC, SimulationPerformance.NO_TIME_RESULT);
			mPerformance.setCountingMeasure(ECountingMeasure.SCCS, SimulationPerformance.NO_COUNTING_RESULT);
		}
		simulationHook();
		mPerformance.stopTimeMeasure(ETimeMeasure.SIMULATION_ONLY);
		mResult = getGameGraph().generateAutomatonFromGraph();

		long duration = mPerformance.stopTimeMeasure(ETimeMeasure.OVERALL);
		// Add time building of the graph took to the overall time since this
		// happens outside of simulation
		final long durationGraph = mPerformance.getTimeMeasureResult(ETimeMeasure.BUILD_GRAPH,
				EMultipleDataOption.ADDITIVE);
		if (durationGraph != SimulationPerformance.NO_TIME_RESULT) {
			duration += durationGraph;
			mPerformance.addTimeMeasureValue(ETimeMeasure.OVERALL, durationGraph);
		}

		retrieveGeneralAutomataPerformance();

		mLogger.info((this.mUseSCCs ? "SCC version" : "nonSCC version") + " took " + duration + " milliseconds.");
	}

	/**
	 * Gets the resulting possible reduced buechi automaton.
	 * 
	 * @return The resulting possible reduced buechi automaton.
	 */
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}

	/**
	 * Gets the performance of the simulation.
	 * 
	 * @return The performance of the simulation.
	 */
	public SimulationPerformance getSimulationPerformance() {
		return mPerformance;
	}

	/**
	 * Gets t state factory used for creating states.
	 * 
	 * @return The state factory used for creating states.
	 */
	public IStateFactory<STATE> getStateFactory() {
		return mStateFactory;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		final StringBuilder result = new StringBuilder();
		final String lineSeparator = System.lineSeparator();
		// Header
		result.append("SimulationResults sr = (");

		// Properties
		result.append(lineSeparator + "\tuseSCCs = " + isUsingSCCs());
		result.append(lineSeparator + "\tglobalInfinity = " + getGameGraph().getGlobalInfinity());
		if (getResult() != null) {
			result.append(lineSeparator + "\tbuechi size after = " + getResult().size() + " states");
		}

		// Progress Measure
		result.append(lineSeparator + "\tprogress measure = {");
		for (final SpoilerVertex<LETTER, STATE> vertex : getGameGraph().getSpoilerVertices()) {
			int localInfinity = getGameGraph().getGlobalInfinity();
			if (isUsingSCCs()) {
				for (final StronglyConnectedComponent<Vertex<LETTER, STATE>> scc : getSccComp().getSCCs()) {
					if (scc.getNodes().contains(vertex)) {
						localInfinity = calculateInfinityOfSCC(scc);
					}
				}
			}
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + "), pm:"
					+ vertex.getPM(null, getGameGraph().getGlobalInfinity()) + " of " + localInfinity + ">");
		}
		for (final DuplicatorVertex<LETTER, STATE> vertex : getGameGraph().getDuplicatorVertices()) {
			int localInfinity = getGameGraph().getGlobalInfinity();
			if (isUsingSCCs()) {
				for (final StronglyConnectedComponent<Vertex<LETTER, STATE>> scc : getSccComp().getSCCs()) {
					if (scc.getNodes().contains(vertex)) {
						localInfinity = calculateInfinityOfSCC(scc);
					}
				}
			}
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + ", " + vertex.getLetter()
					+ "), pm:" + vertex.getPM(null, getGameGraph().getGlobalInfinity()) + " of " + localInfinity + ">");
		}
		result.append(lineSeparator + "\t},");

		// Best Neighbor Measure
		result.append(lineSeparator + "\tbest neighbor measure = {");
		for (final SpoilerVertex<LETTER, STATE> vertex : getGameGraph().getSpoilerVertices()) {
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + "), bnm:"
					+ vertex.getBEff() + ">");
		}
		for (final DuplicatorVertex<LETTER, STATE> vertex : getGameGraph().getDuplicatorVertices()) {
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + ", " + vertex.getLetter()
					+ "), bnm:" + vertex.getBEff() + ">");
		}
		result.append(lineSeparator + "\t},");

		// Neighbor counter
		result.append(lineSeparator + "\tneighbor counter = {");
		for (final SpoilerVertex<LETTER, STATE> vertex : getGameGraph().getSpoilerVertices()) {
			result.append(
					lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + "), nc:" + vertex.getC() + ">");
		}
		for (final DuplicatorVertex<LETTER, STATE> vertex : getGameGraph().getDuplicatorVertices()) {
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + ", " + vertex.getLetter()
					+ "), nc:" + vertex.getC() + ">");
		}
		result.append(lineSeparator + "\t},");

		// Footer
		result.append(lineSeparator + ");");

		return result.toString();
	}

	/**
	 * Adds a given vertex to the working list and updates its own working list
	 * flag.
	 * 
	 * @param vertex
	 *            Vertex to add
	 */
	protected void addVertexToWorkingList(final Vertex<LETTER, STATE> vertex) {
		mWorkingList.add(vertex);
		vertex.setInWL(true);
	}

	/**
	 * Calculates the best neighbor measure for a given vertex based on its
	 * local infinity and its containing SCC.<br/>
	 * <br/>
	 * 
	 * If the vertex has no successors the corresponding player looses,
	 * <i>infinity</i> is returned for a {@link DuplicatorVertex} and 0 for a
	 * {@link SpoilerVertex}.<br/>
	 * For a {@link DuplicatorVertex} the minimal progress measure of its
	 * successor is returned, maximal for a {@link SpoilerVertex}.<br/>
	 * The returned value then gets decreased based on the priority of the given
	 * vertex.
	 * 
	 * @param vertex
	 *            The given vertex to calculate for
	 * @param localInfinity
	 *            The local infinity in the containing SCC or global infinity if
	 *            not used
	 * @param scc
	 *            The containing SCC or <tt>null</tt> if not used
	 * @return The best neighbor measure of the vertex
	 */
	protected int calcBestNghbMeasure(final Vertex<LETTER, STATE> vertex, final int localInfinity,
			final Set<Vertex<LETTER, STATE>> scc) {
		final AGameGraph<LETTER, STATE> gameGraph = getGameGraph();
		final boolean isDuplicatorVertex = vertex.isDuplicatorVertex();

		// Compute of there is a push-over successor with a progress measure of
		// infinity, we need to consider those successors.
		boolean considerPushOverEdges = false;
		HashSet<Vertex<LETTER, STATE>> considerablePushOverSuccessors = null;
		if (gameGraph.hasPushOverSuccessors(vertex)) {
			for (final Vertex<LETTER, STATE> pushOverSucc : gameGraph.getPushOverSuccessors(vertex)) {
				if (pushOverSucc.getPM(scc, gameGraph.getGlobalInfinity()) == gameGraph.getGlobalInfinity()) {
					if (considerablePushOverSuccessors == null) {
						considerablePushOverSuccessors = new HashSet<>();
						considerPushOverEdges = true;
					}
					considerablePushOverSuccessors.add(pushOverSucc);
				}
			}
		}

		// If there are no successors nor considerable push-over successors,
		// the corresponding player looses
		if (!gameGraph.hasSuccessors(vertex) && !considerPushOverEdges) {
			if (isDuplicatorVertex) {
				return gameGraph.getGlobalInfinity();
			} else {
				return 0;
			}
		}

		// Initiate the known optimum, big for duplicator and small for spoiler
		int optimum;
		if (isDuplicatorVertex) {
			optimum = gameGraph.getGlobalInfinity();
		} else {
			optimum = 0;
		}

		// The optimum is the minimal progress measure of its successors for
		// Duplicator and maximal for Spoiler
		Set<Vertex<LETTER, STATE>> successorsToConsider = gameGraph.getSuccessors(vertex);
		// If vertex reached infinity, propagate this over
		// the push-over edges.
		if (considerPushOverEdges) {
			// Care for concurrent modification exception
			successorsToConsider = new HashSet<Vertex<LETTER, STATE>>(successorsToConsider);
			successorsToConsider.addAll(considerablePushOverSuccessors);
		}
		for (final Vertex<LETTER, STATE> succ : successorsToConsider) {
			final int progressMeasure = succ.getPM(scc, gameGraph.getGlobalInfinity());
			if (isDuplicatorVertex) {
				if (progressMeasure < optimum) {
					optimum = progressMeasure;
				}
			} else {
				if (progressMeasure > optimum) {
					optimum = progressMeasure;
				}
			}
		}

		// Decrease the optimum based on the priority
		return decreaseVector(gameGraph.getPriority(vertex), optimum, localInfinity);
	}

	/**
	 * Calculates the number of successors a vertex has that represent the best
	 * choice for it to go at.<br/>
	 * This is represented by the best neighbor measure of the vertex.
	 * 
	 * @param vertex
	 *            The vertex to calculate for
	 * @param localInfinity
	 *            The local infinity in the containing SCC or global infinity if
	 *            not used
	 * @param scc
	 *            The containing SCC or <tt>null</tt> if not used
	 * @return The neighbor counter of the vertex
	 */
	protected int calcNghbCounter(final Vertex<LETTER, STATE> vertex, final int localInfinity,
			final Set<Vertex<LETTER, STATE>> scc) {
		final AGameGraph<LETTER, STATE> gameGraph = getGameGraph();

		// Compute of there is a push-over successor with a progress measure of
		// infinity, we need to consider those successors.
		boolean considerPushOverEdges = false;
		HashSet<Vertex<LETTER, STATE>> considerablePushOverSuccessors = null;
		if (gameGraph.hasPushOverSuccessors(vertex)) {
			for (final Vertex<LETTER, STATE> pushOverSucc : gameGraph.getPushOverSuccessors(vertex)) {
				if (pushOverSucc.getPM(scc, gameGraph.getGlobalInfinity()) == gameGraph.getGlobalInfinity()) {
					if (considerablePushOverSuccessors == null) {
						considerablePushOverSuccessors = new HashSet<>();
						considerPushOverEdges = true;
					}
					considerablePushOverSuccessors.add(pushOverSucc);
				}
			}
		}

		// If there are no successors nor considerable push-over successors,
		// we have zero best neighbors
		if (!gameGraph.hasSuccessors(vertex) && !considerPushOverEdges) {
			return 0;
		}

		// Count the number of successors that have the best
		// neighbor measure from the perspective of the vertex and its priority
		int counter = 0;
		Set<Vertex<LETTER, STATE>> successorsToConsider = gameGraph.getSuccessors(vertex);
		// If vertex reached infinity, propagate this over
		// the push-over edges.
		if (considerPushOverEdges) {
			// Care for concurrent modification exception
			successorsToConsider = new HashSet<Vertex<LETTER, STATE>>(successorsToConsider);
			successorsToConsider.addAll(considerablePushOverSuccessors);
		}
		for (final Vertex<LETTER, STATE> succ : successorsToConsider) {
			if (decreaseVector(gameGraph.getPriority(vertex), succ.getPM(scc, gameGraph.getGlobalInfinity()),
					localInfinity) == vertex.getBEff()) {
				counter++;
			}
		}
		return counter;
	}

	/**
	 * Calculates the local infinity bound of a given SCC. Which is the number
	 * of vertices in the SCC that have priority 1, plus one.<br/>
	 * In contrast to the {@link AGameGraph#getGlobalInfinity() global infinity
	 * of a game graph} this can be used to locally optimize the simulation
	 * calculation of a single SCC. This is because we can already be sure that
	 * we can visit the corresponding vertices infinite times after visiting
	 * them the local bound often.
	 * 
	 * @param scc
	 *            The SCC to calculate the local infinity for
	 * @return A, for the SCC, local optimal upper bound for infinity which is
	 *         the number of vertices in the SCC that have priority 1, plus one.
	 */
	protected int calculateInfinityOfSCC(final StronglyConnectedComponent<Vertex<LETTER, STATE>> scc) {
		int localInfinity = 0;
		for (final Vertex<LETTER, STATE> vertex : scc.getNodes()) {
			if (getGameGraph().getPriority(vertex) == 1) {
				localInfinity++;
			}
		}
		localInfinity++;
		return localInfinity;
	}

	/**
	 * Creates and sets a new working list.
	 */
	protected void createWorkingList() {
		mWorkingList = new PriorityQueue<>(mVertexComp);
	}

	/**
	 * Decreases a given number based on a given index and a local infinity.
	 * <br/>
	 * The global infinity bound gets returned if the number has reached the
	 * local infinity bound. The number itself gets returned if the index is not
	 * zero and 0 if it is zero.
	 * 
	 * @param index
	 *            The index to reduce to
	 * @param vector
	 *            The number to reduce
	 * @param localInfinity
	 *            The local infinity in the containing SCC or global infinity if
	 *            not used
	 * @return Global infinity if reached local infinity, the inputed number if
	 *         index is not zero and 0 if it is.
	 */
	protected int decreaseVector(final int index, final int vector, final int localInfinity) {
		// Always return global infinity if greater than local infinity
		if (vector >= localInfinity) {
			return getGameGraph().getGlobalInfinity();
		}
		if (index == 0) {
			return 0;
		} else {
			return vector;
		}
	}

	/**
	 * The actual simulation calculation algorithm which simulates the
	 * corresponding game defined by the type of {@link AGameGraph}.<br/>
	 * When finished the progress measures of given vertices determine a
	 * simulation relation that is used for reducing buechi automata.<br/>
	 * For a given vertex (q0, q1) we shall say q1 simulates q0 if its progress
	 * measure did not reach infinity.
	 * 
	 * @param localInfinity
	 *            The local infinity in the containing SCC or global infinity if
	 *            not used
	 * @param scc
	 *            The containing SCC or <tt>null</tt> if not used
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	protected void efficientLiftingAlgorithm(final int localInfinity, final Set<Vertex<LETTER, STATE>> scc)
			throws AutomataOperationCanceledException {
		final AGameGraph<LETTER, STATE> game = getGameGraph();
		final int globalInfinity = game.getGlobalInfinity();

		// Initialize working list and the C value of all vertices
		createWorkingList();
		if (mUseSCCs) {
			for (final Vertex<LETTER, STATE> v : scc) {
				initWorkingListAndCWithVertex(v, localInfinity, scc);
			}
		} else {
			for (final DuplicatorVertex<LETTER, STATE> v : game.getDuplicatorVertices()) {
				initWorkingListAndCWithVertex(v, localInfinity, scc);
			}
			for (final SpoilerVertex<LETTER, STATE> v : game.getSpoilerVertices()) {
				initWorkingListAndCWithVertex(v, localInfinity, scc);
			}
		}

		// Work through the working list until its empty
		while (!mWorkingList.isEmpty()) {
			mPerformance.increaseCountingMeasure(ECountingMeasure.SIMULATION_STEPS);

			// Poll the current working vertex
			final Vertex<LETTER, STATE> v = pollVertexFromWorkingList();

			// Remember old progress measure of the working vertex
			final int t = v.getPM(scc, globalInfinity);

			// Update values of the working vertex
			v.setBEff(calcBestNghbMeasure(v, localInfinity, scc));
			v.setC(calcNghbCounter(v, localInfinity, scc));
			v.setPM(increaseVector(getGameGraph().getPriority(v), v.getBEff(), localInfinity));

			// Work through its predecessors and possibly add them
			// to the working list since they may be interested in
			// the changes of the working vertex
			final boolean considerPushOverPredecessors = v.getPM(scc, globalInfinity) == globalInfinity
					&& game.hasPushOverPredecessors(v);
			if (!game.hasPredecessors(v) && !considerPushOverPredecessors) {
				continue;
			}
			Set<Vertex<LETTER, STATE>> predecessorsToConsider = game.getPredecessors(v);
			// If vertex reached infinity, propagate this over the push-over
			// edges.
			if (considerPushOverPredecessors) {
				// Care for concurrent modification exception
				if (predecessorsToConsider != null) {
					predecessorsToConsider = new HashSet<Vertex<LETTER, STATE>>(predecessorsToConsider);
				} else {
					predecessorsToConsider = new HashSet<Vertex<LETTER, STATE>>();
				}
				// TODO There is a problem with push-over edges not being
				// considered in the SCC optimization.
				predecessorsToConsider.addAll(game.getPushOverPredecessors(v));
			}
			for (final Vertex<LETTER, STATE> w : predecessorsToConsider) {
				if (mUseSCCs && !scc.contains(w)) {
					continue;
				}

				// If the working vertex has increased its progress
				// measure from the perspective of the predecessor and
				// its priority
				if (!w.isInWL() && decreaseVector(getGameGraph().getPriority(w), v.getPM(scc, globalInfinity),
						localInfinity) > w.getBEff()) {
					// A Duplicator vertex is only interested in an increased
					// progress measure if the working vertex was its
					// best choice previously and it has no better
					// alternative now
					if (w.isDuplicatorVertex()
							&& decreaseVector(getGameGraph().getPriority(w), t, localInfinity) == w.getBEff()) {
						if (w.getC() == 1) {
							// It has no better alternative,
							// adding to working list
							addVertexToWorkingList(w);
						}
						if (w.getC() > 1) {
							// It has a better alternative, reducing number of
							// neighbors that represent the best choice for the
							// predecessor
							w.setC(w.getC() - 1);
						}
					} else if (w.isSpoilerVertex()) {
						// A Spoiler vertex is always interested in an increased
						// progress measure
						addVertexToWorkingList(w);
					}
				}
			}

			// If operation was canceled, for example from the
			// Ultimate framework
			if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
				mLogger.debug("Stopped in efficientLiftingAlgorithm");
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}
	}

	/**
	 * Gets the {@link AGameGraph} used for this simulation.
	 * 
	 * @return The {@link AGameGraph} used for this simulation.
	 */
	protected abstract AGameGraph<LETTER, STATE> getGameGraph();

	/**
	 * Gets the logger used by the Ultimate framework.
	 * 
	 * @return The logger used by the Ultimate framework.
	 */
	protected ILogger getLogger() {
		return mLogger;
	}

	/**
	 * Gets the timer used for responding to timeouts and operation
	 * cancellation.
	 * 
	 * @return The timer used for responding to timeouts and operation
	 *         cancellation.
	 */
	protected IProgressAwareTimer getProgressTimer() {
		return mProgressTimer;
	}

	/**
	 * Gets the object that is used for computing the SCCs of a given buechi
	 * automaton.
	 * 
	 * @return The object that is used for computing the SCCs of a given buechi
	 *         automaton.
	 */
	protected SccComputation<Vertex<LETTER, STATE>, StronglyConnectedComponent<Vertex<LETTER, STATE>>> getSccComp() {
		return mSccComp;
	}

	/**
	 * Gets the current working list of the simulation.
	 * 
	 * @return The current working list of the simulation.
	 */
	protected PriorityQueue<Vertex<LETTER, STATE>> getWorkingList() {
		return mWorkingList;
	}

	/**
	 * Increases a given number by using a given index and a local infinity.
	 * <br/>
	 * Returning the global infinity if number has reached the local infinity
	 * bound, a decreased vector for a index that is not one.<br/>
	 * For a index of one it increases the given number and returns it or global
	 * infinity if reached the local infinity bound.
	 * 
	 * @param index
	 *            The given index to increase from
	 * @param vector
	 *            The number to increase
	 * @param localInfinity
	 *            The local infinity in the containing SCC or global infinity if
	 *            not used
	 * @return Global infinity if reached local infinity, the inputed number if
	 *         index is two, 0 if it is zero and increased by one if the index
	 *         it is one.
	 */
	protected int increaseVector(final int index, final int vector, final int localInfinity) {
		// Always return global infinity if greater than local infinity
		if (vector >= localInfinity) {
			return getGameGraph().getGlobalInfinity();
		}
		if (index == 1) {
			final int tempVector = vector + 1;
			// Always return global infinity if greater than local infinity
			if (tempVector == localInfinity) {
				return getGameGraph().getGlobalInfinity();
			}
			return tempVector;
		} else {
			return decreaseVector(index, vector, localInfinity);
		}
	}

	/**
	 * Initializes a given vertex for the current simulation calculation by
	 * possibly adding it to the working list and initializing its values.<br/>
	 * Used by {@link #initSimulation(int, Set)}.
	 * 
	 * @param vertex
	 *            Vertex to initialize
	 * @param localInfinity
	 *            The local infinity bound of the used SCC or global infinity if
	 *            not used
	 * @param scc
	 *            The currently for simulation used SCC or <tt>null</tt> if not
	 *            used
	 */
	protected void initWorkingListAndCWithVertex(final Vertex<LETTER, STATE> vertex, final int localInfinity,
			final Set<Vertex<LETTER, STATE>> scc) {
		final boolean isDeadEnd = !getGameGraph().hasSuccessors(vertex);

		// check if an update would change progress measure
		// this happens if
		// * a successor (from a possibly different SCC) has progress measure
		// (global) infinity,
		// * this vertex is a dead end duplicator vertex, or
		// * this vertex has priority 1.
		//
		final boolean doesChangeWithUpdate = vertex.getPM(scc, getGameGraph().getGlobalInfinity()) != update(vertex,
				localInfinity, scc);

		// Possibly add vertex to working list
		if (isDeadEnd || doesChangeWithUpdate) {
			addVertexToWorkingList(vertex);
		}

		// Initialize C value of vertex
		if (mUseSCCs) {
			vertex.setC(calcNghbCounter(vertex, localInfinity, scc));
		} else {
			if (getGameGraph().hasSuccessors(vertex)) {
				vertex.setC(getGameGraph().getSuccessors(vertex).size());
			} else {
				vertex.setC(0);
			}

		}
	}

	/**
	 * If the simulation calculation gets optimized by using SCC, Strongly
	 * Connected Components.
	 * 
	 * @return True if the simulation calculation gets optimized by using SCC,
	 *         false if not.
	 */
	protected boolean isUsingSCCs() {
		return mUseSCCs;
	}

	/**
	 * Retrieves and removes the head of the working list. Also updates the
	 * working list flag of the vertex.
	 * 
	 * @return The head of the working list, or <tt>null</tt> if it is empty.
	 */
	protected Vertex<LETTER, STATE> pollVertexFromWorkingList() {
		final Vertex<LETTER, STATE> polledVertex = mWorkingList.poll();
		if (polledVertex != null) {
			polledVertex.setInWL(false);
		}
		return polledVertex;
	}

	/**
	 * Retrieves general performance data of the input and output automaton.
	 * Saves the data in the current internal performance object.
	 */
	protected void retrieveGeneralAutomataPerformance() {
		final AGameGraph<LETTER, STATE> graph = getGameGraph();
		final AutomataLibraryServices services = graph.getServices();
		final INestedWordAutomaton<LETTER, STATE> input = graph.getAutomaton();

		// Input automaton
		final Analyze<LETTER, STATE> inputAnalyzer = new Analyze<>(services, input, true);
		final int inputStates = inputAnalyzer.getNumberOfStates();
		final int inputTransitions = inputAnalyzer.getNumberOfTransitions(ESymbolType.TOTAL);
		mPerformance.setCountingMeasure(ECountingMeasure.BUCHI_STATES, inputStates);
		mPerformance.setCountingMeasure(ECountingMeasure.BUCHI_NONDETERMINISTIC_STATES,
				inputAnalyzer.getNumberOfNondeterministicStates());

		mPerformance.setCountingMeasure(ECountingMeasure.BUCHI_ALPHABET_SIZE,
				inputAnalyzer.getNumberOfSymbols(ESymbolType.TOTAL));
		mPerformance.setCountingMeasure(ECountingMeasure.BUCHI_TRANSITIONS, inputTransitions);
		mPerformance.setCountingMeasure(ECountingMeasure.BUCHI_TRANSITION_DENSITY_MILLION,
				(int) Math.round(inputAnalyzer.getTransitionDensity(ESymbolType.TOTAL) * 1_000_000));

		// Output automaton
		if (mResult != null) {
			final Analyze<LETTER, STATE> outputAnalyzer = new Analyze<>(services, mResult, true);
			final int outputStates = outputAnalyzer.getNumberOfStates();
			final int outputTransitions = outputAnalyzer.getNumberOfTransitions(ESymbolType.TOTAL);
			mPerformance.setCountingMeasure(ECountingMeasure.RESULT_STATES, outputStates);
			mPerformance.setCountingMeasure(ECountingMeasure.RESULT_NONDETERMINISTIC_STATES,
					outputAnalyzer.getNumberOfNondeterministicStates());

			mPerformance.setCountingMeasure(ECountingMeasure.RESULT_ALPHABET_SIZE,
					outputAnalyzer.getNumberOfSymbols(ESymbolType.TOTAL));
			mPerformance.setCountingMeasure(ECountingMeasure.RESULT_TRANSITIONS, outputTransitions);
			mPerformance.setCountingMeasure(ECountingMeasure.RESULT_TRANSITION_DENSITY_MILLION,
					(int) Math.round(outputAnalyzer.getTransitionDensity(ESymbolType.TOTAL) * 1_000_000));

			// General metrics
			mPerformance.setCountingMeasure(ECountingMeasure.GAMEGRAPH_VERTICES, graph.getSize());
			mPerformance.setCountingMeasure(ECountingMeasure.GAMEGRAPH_EDGES, graph.getAmountOfEdges());

			mPerformance.setCountingMeasure(ECountingMeasure.GLOBAL_INFINITY, graph.getGlobalInfinity());
			mPerformance.setCountingMeasure(ECountingMeasure.REMOVED_STATES, inputStates - outputStates);
			mPerformance.setCountingMeasure(ECountingMeasure.REMOVED_TRANSITIONS, inputTransitions - outputTransitions);
		}
	}

	/**
	 * Sets the result of the simulation calculation, a possible reduced buechi
	 * automaton.
	 * 
	 * @param result
	 *            The result of the simulation calculation, a possible reduced
	 *            buechi automaton.
	 */
	protected void setResult(final INestedWordAutomaton<LETTER, STATE> result) {
		mResult = result;
	}

	/**
	 * Sets the object that is used for computing the SCCs of a given buechi
	 * automaton.
	 * 
	 * @param sccComp
	 *            The object to set.
	 */
	protected void setSccComp(
			final SccComputation<Vertex<LETTER, STATE>, StronglyConnectedComponent<Vertex<LETTER, STATE>>> sccComp) {
		mSccComp = sccComp;
	}

	/**
	 * Sets if the simulation calculation should be optimized using SCC,
	 * Strongly Connected Components or not.
	 * 
	 * @param useSCCs
	 *            True if the simulation calculation gets optimized by using
	 *            SCC, false if not.
	 */
	protected void setUseSCCs(final boolean useSCCs) {
		mUseSCCs = useSCCs;
	}

	/**
	 * Gets called after the simulation was run but before the resulting
	 * automaton gets generated. Provides a hook for manipulating simulation
	 * results.
	 * 
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	protected void simulationHook() throws AutomataOperationCanceledException {
		// The default implementation is to do nothing
	}

	/**
	 * Calculates the progress measure of a given vertex by trying to increase
	 * it, based on its best neighbor measure and priority.<br/>
	 * If the returned value has increased the vertex can make a better move
	 * than in its previous run and should be updated.
	 * 
	 * @param v
	 *            The vertex to update
	 * @param localInfinity
	 *            The local infinity in the containing SCC or global infinity if
	 *            not used
	 * @param scc
	 *            The containing SCC or <tt>null</tt> if not used
	 * @return The possible increased progress measure
	 */
	protected int update(final Vertex<LETTER, STATE> v, final int localInfinity, final Set<Vertex<LETTER, STATE>> scc) {
		return increaseVector(getGameGraph().getPriority(v), calcBestNghbMeasure(v, localInfinity, scc), localInfinity);
	}
}
