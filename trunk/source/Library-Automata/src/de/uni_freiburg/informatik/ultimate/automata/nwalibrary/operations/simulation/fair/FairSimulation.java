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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.fair;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.ASimulation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.ESimulationType;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.GameGraphChanges;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.GameGraphSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.performance.ECountingMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.performance.EMultipleDataOption;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.performance.ETimeMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.performance.SimulationPerformance;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Quad;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;
import de.uni_freiburg.informatik.ultimate.util.scc.DefaultStronglyConnectedComponentFactory;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * Simulation that realizes <b>fair simulation</b> for reduction of a given
 * buechi automaton.<br/>
 * Once started, results can then be get by using {@link #getResult()}.<br/>
 * <br/>
 * 
 * For more information on the type of simulation see {@link FairGameGraph}.
 * <br/>
 * <br/>
 * 
 * The algorithm runs in <b>O(n^4 * k^2)</b> time and <b>O(n * k)</b> space
 * where n is the amount of states and k the amount of transitions from the
 * inputed automaton.<br/>
 * The algorithm is based on the paper: <i>Fair simulation minimization<i> by
 * <i>Gurumurthy, Bloem and Somenzi</i>.
 * 
 * @author Daniel Tischner
 * 
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public class FairSimulation<LETTER, STATE> extends ASimulation<LETTER, STATE> {

	/**
	 * Saves a change on the <i>BEff value</i> of a given vertex in the current
	 * {@link GameGraphChanges} object if there currently is no such value
	 * stored.
	 * 
	 * @param vertex
	 *            Vertex to save change
	 * @param oldValue
	 *            Value to save
	 * @param changes
	 *            Changes object to store change in
	 */
	private static <LETTER, STATE> void saveBEffChange(Vertex<LETTER, STATE> vertex, int oldValue,
			GameGraphChanges<LETTER, STATE> changes) {
		if (changes != null && oldValue != vertex.getBEff() && !changes.hasBEffEntry(vertex)) {
			changes.rememberBEffVertex(vertex, oldValue);
		}
	}

	/**
	 * Saves a change on the <i>C value</i> of a given vertex in the current
	 * {@link GameGraphChanges} object if there currently is no such value
	 * stored.
	 * 
	 * @param vertex
	 *            Vertex to save change
	 * @param oldValue
	 *            Value to save
	 * @param changes
	 *            Changes object to store change in
	 */
	private static <LETTER, STATE> void saveCChange(Vertex<LETTER, STATE> vertex, int oldValue,
			GameGraphChanges<LETTER, STATE> changes) {
		if (changes != null && oldValue != vertex.getC() && !changes.hasCEntry(vertex)) {
			changes.rememberCVertex(vertex, oldValue);
		}
	}

	/**
	 * Saves a change on the <i>Progress measure value</i> of a given vertex in
	 * the current {@link GameGraphChanges} object if there currently is no such
	 * value stored.
	 * 
	 * @param vertex
	 *            Vertex to save change
	 * @param oldValue
	 *            Value to save
	 * @param changes
	 *            Changes object to store change in
	 */
	private static <LETTER, STATE> void savePmChange(Vertex<LETTER, STATE> vertex, int oldValue,
			GameGraphChanges<LETTER, STATE> changes) {
		if (changes != null && oldValue != vertex.getPM(null, 0) && !changes.hasPmEntry(vertex)) {
			changes.rememberPmVertex(vertex, oldValue);
		}
	}

	/**
	 * If the simulation process itself should log detailed debugging
	 * information.
	 */
	private final boolean debugSimulation = false;
	/**
	 * Amount of SCCs of the initial game graph version.
	 */
	private int mAmountOfSCCs;
	/**
	 * True if currently attempting to do changes on the game graph, false if
	 * not. Used to tell {@link #efficientLiftingAlgorithm(int, Set)} to re use
	 * information of previous simulation runs and to store information about
	 * changes in order to be able to undo them.
	 */
	private boolean mAttemptingChanges;
	/**
	 * The game graph changes object that is currently used to store information
	 * about made changes. Used by {@link #efficientLiftingAlgorithm(int, Set)}
	 * to store its changes since it can not access it by another way because of
	 * the interface. Assign <tt>null</tt> to indicate that changes should not
	 * be stored.
	 */
	private GameGraphChanges<LETTER, STATE> mCurrentChanges;
	/**
	 * Game graph that is used for simulation calculation.
	 */
	private final FairGameGraph<LETTER, STATE> mGame;
	/**
	 * Copy of {@link AGameGraph#getGlobalInfinity()} for faster access.
	 */
	private int mGlobalInfinity;
	/**
	 * The logger used by the Ultimate framework.
	 */
	private final ILogger mLogger;
	/**
	 * Stores all currently known {@link SpoilerVertex} objects that indicate
	 * simulation is not possible and are non trivial. This are vertices with a
	 * progress measure that reached infinity and where q1 is not equals q2 for
	 * the representation (q1, q2) because these are trivial simulations.<br/>
	 * The set is used to abort the simulation early whenever a previous
	 * possible simulation gets removed due to a game graph change.
	 */
	private Set<SpoilerVertex<LETTER, STATE>> mNotSimulatingNonTrivialVertices;
	/**
	 * Contains all vertices that are currently poked from a neighbor SCC,
	 * Strongly Connected Component, if used.<br/>
	 * Poked vertices need to be added to the working list and calculate their
	 * update by ignoring the bounds of its own SCC as soon as its their turn
	 * because a successor of a neighboring SCC has reached infinity.
	 */
	private HashSet<Vertex<LETTER, STATE>> mpokedFromNeighborSCC;
	/**
	 * A collection of sets which contains states of the buechi automaton that
	 * may be merge-able. States which are not in the same set are definitely
	 * not merge-able which is used as an optimization for the simulation.
	 */
	private final Map<STATE, Set<STATE>> mPossibleEquivalentClasses;

	/**
	 * True if the simulation was aborted early because its already known that
	 * the underlying language did change, false if not.
	 */
	private boolean mSimulationWasAborted;

	/**
	 * Creates a new fair simulation with a given fair game graph that tries to
	 * reduce the given buechi automaton using <b>fair simulation</b>.<br/>
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
	 *            A collection of sets which contains states of the buechi
	 *            automaton that may be merge-able. States which are not in the
	 *            same set are definitely not merge-able which is used as an
	 *            optimization for the simulation
	 * @param game
	 *            The fair game graph to use for simulation.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public FairSimulation(final IProgressAwareTimer progressTimer, final ILogger logger, final boolean useSCCs,
			final StateFactory<STATE> stateFactory, final Collection<Set<STATE>> possibleEquivalentClasses,
			final FairGameGraph<LETTER, STATE> game) throws AutomataOperationCanceledException {
		super(progressTimer, logger, useSCCs, stateFactory, ESimulationType.FAIR);

		mLogger = getLogger();
		mPossibleEquivalentClasses = processEquivalenceClasses(possibleEquivalentClasses);
		mpokedFromNeighborSCC = null;
		mNotSimulatingNonTrivialVertices = new HashSet<>();
		mCurrentChanges = null;

		mGame = game;
		mGame.setSimulationPerformance(super.getSimulationPerformance());

		mAttemptingChanges = false;
		mSimulationWasAborted = false;
		mAmountOfSCCs = 0;
	}

	/**
	 * Creates a new fair simulation that tries to reduce the given buechi
	 * automaton using <b>fair simulation</b>.<br/>
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
	 *            The fair game graph to use for simulation.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public FairSimulation(final IProgressAwareTimer progressTimer, final ILogger logger, final boolean useSCCs,
			final StateFactory<STATE> stateFactory, final FairGameGraph<LETTER, STATE> game)
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
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Fair Game Graph has " + mGame.getSize() + " vertices.");
		}
		mGlobalInfinity = mGame.getGlobalInfinity();

		final SimulationPerformance performance = super.getSimulationPerformance();
		performance.startTimeMeasure(ETimeMeasure.OVERALL);
		performance.startTimeMeasure(ETimeMeasure.SIMULATION_ONLY);

		// First simulation
		mLogger.debug("Starting first simulation...");
		doSingleSimulation(null);
		mLogger.debug("Ending first simulation.");

		// Deactivate the usage of SCCs for the following simulations since the
		// overhead of using SCCs is only worth it if simulation does not
		// terminate as quickly as it will do now.
		if (!isUsingSCCs()) {
			performance.addTimeMeasureValue(ETimeMeasure.BUILD_SCC, SimulationPerformance.NO_TIME_RESULT);
			performance.setCountingMeasure(ECountingMeasure.SCCS, SimulationPerformance.NO_COUNTING_RESULT);
		}
		boolean disabledSCCUsage = false;
		if (isUsingSCCs()) {
			setUseSCCs(false);
			disabledSCCUsage = true;
			performance.setCountingMeasure(ECountingMeasure.SCCS, mAmountOfSCCs);
		}
		performance.setCountingMeasure(ECountingMeasure.GLOBAL_INFINITY, mGlobalInfinity);

		// Merge states
		mAttemptingChanges = true;
		final Set<SpoilerVertex<LETTER, STATE>> mergeCandidates = mergeCandidates();
		final Set<SpoilerVertex<LETTER, STATE>> noTransitionCandidates = new HashSet<>();

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Size of merge candidates: " + mergeCandidates.size());
		}

		for (final SpoilerVertex<LETTER, STATE> mergeCandidate : mergeCandidates) {
			final STATE leftState = mergeCandidate.getQ0();
			final STATE rightState = mergeCandidate.getQ1();

			// Attempt merge
			final FairGameGraphChanges<LETTER, STATE> changes = attemptMerge(leftState, rightState);
			// Undo if language changed, else do not consider
			// pair for transition removal
			if (changes != null) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Attempted merge for " + leftState + " and " + rightState
							+ " was not successful, undoing...");
				}

				mGame.undoChanges(changes);
				performance.increaseCountingMeasure(ECountingMeasure.FAILED_MERGE_ATTEMPTS);
			} else {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Attempted merge for " + leftState + " and " + rightState + " was successful.");
				}
				// Pass merge to game graph
				mGame.markMergeable(leftState, rightState);

				// Pair and mirrored pair are no candidates
				// for transition removal
				noTransitionCandidates.add(mergeCandidate);
				final SpoilerVertex<LETTER, STATE> mirroredCandidate = mGame.getSpoilerVertex(rightState, leftState, false);
				if (mirroredCandidate != null) {
					noTransitionCandidates.add(mirroredCandidate);
				}
			}

			// If operation was canceled, for example from the
			// Ultimate framework
			if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
				mLogger.debug("Stopped in doSimulation/attempting merges");
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}

		// Remove redundant transitions
		final HashSet<Quad<STATE, LETTER, STATE, STATE>> transitionCandidates = transitionCandidates(noTransitionCandidates);

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Size of transition candidates: " + transitionCandidates.size());
		}

		for (final Quad<STATE, LETTER, STATE, STATE> transitionCandidate : transitionCandidates) {
			final STATE src = transitionCandidate.getFirst();
			final LETTER a = transitionCandidate.getSecond();
			final STATE dest = transitionCandidate.getThird();
			final STATE invoker = transitionCandidate.getFourth();

			// Attempt transition removal
			final FairGameGraphChanges<LETTER, STATE> changes = attemptTransitionRemoval(src, a, dest, invoker);
			// Undo if language changed, else add transition for removal
			if (changes != null) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Attempted transition removal for " + src + " -" + a + "-> " + dest
							+ " was not successful, undoing...");
				}

				mGame.undoChanges(changes);
				performance.increaseCountingMeasure(ECountingMeasure.FAILED_TRANSREMOVE_ATTEMPTS);
			} else {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(
							"Attempted transition removal for " + src + " -" + a + "-> " + dest + " was successful.");
				}
				// Pass removal to game graph
				mGame.markRemoveableTransition(src, a, dest);
			}

			// If operation was canceled, for example from the
			// Ultimate framework
			if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
				mLogger.debug("Stopped in doSimulation/attempting transition removal");
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}

		// Re-enable the usage
		if (disabledSCCUsage) {
			setUseSCCs(true);
		}

		performance.stopTimeMeasure(ETimeMeasure.SIMULATION_ONLY);

		// Generate the resulting automata
		mLogger.debug("Generating the result automaton...");
		setResult(mGame.generateAutomatonFromGraph());

		long duration = performance.stopTimeMeasure(ETimeMeasure.OVERALL);
		// Add time building of the graph took to the overall time since this
		// happens outside of simulation
		final long durationGraph = performance.getTimeMeasureResult(ETimeMeasure.BUILD_GRAPH, EMultipleDataOption.ADDITIVE);
		if (durationGraph != SimulationPerformance.NO_TIME_RESULT) {
			duration += durationGraph;
			performance.addTimeMeasureValue(ETimeMeasure.OVERALL, durationGraph);
		}
		performance.setCountingMeasure(ECountingMeasure.GAMEGRAPH_VERTICES, mGame.getSize());

		mLogger.info((isUsingSCCs() ? "SCC version" : "nonSCC version") + " took " + duration + " milliseconds and "
				+ performance.getCountingMeasureResult(ECountingMeasure.SIMULATION_STEPS) + " simulation steps.");
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
		result.append("FairSimulationResults fsr = (");

		// Properties
		result.append(lineSeparator + "\tuseSCCs = " + isUsingSCCs());
		result.append(lineSeparator + "\tglobalInfinity = " + mGlobalInfinity);
		result.append(lineSeparator + "\tstepCounter = "
				+ getSimulationPerformance().getCountingMeasureResult(ECountingMeasure.SIMULATION_STEPS));
		result.append(lineSeparator + "\tbuechi size before = " + mGame.getAutomatonSize() + " states");
		if (getResult() != null) {
			result.append(lineSeparator + "\tbuechi size after = " + getResult().size() + " states");
		}

		// Progress Measure
		result.append(lineSeparator + "\tprogress measure = {");
		for (final SpoilerVertex<LETTER, STATE> vertex : mGame.getSpoilerVertices()) {
			int localInfinity = mGlobalInfinity;
			if (isUsingSCCs()) {
				for (final StronglyConnectedComponent<Vertex<LETTER, STATE>> scc : getSccComp().getSCCs()) {
					if (scc.getNodes().contains(vertex)) {
						localInfinity = calculateInfinityOfSCC(scc);
					}
				}
			}
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + "), pm:"
					+ vertex.getPM(null, mGlobalInfinity) + " of " + localInfinity + ">");
		}
		for (final DuplicatorVertex<LETTER, STATE> vertex : mGame.getDuplicatorVertices()) {
			int localInfinity = mGlobalInfinity;
			if (isUsingSCCs()) {
				for (final StronglyConnectedComponent<Vertex<LETTER, STATE>> scc : getSccComp().getSCCs()) {
					if (scc.getNodes().contains(vertex)) {
						localInfinity = calculateInfinityOfSCC(scc);
					}
				}
			}
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + ", " + vertex.getLetter()
					+ "), pm:" + vertex.getPM(null, mGlobalInfinity) + " of " + localInfinity + ">");
		}
		result.append(lineSeparator + "\t},");

		// Best Neighbor Measure
		result.append(lineSeparator + "\tbest neighbor measure = {");
		for (final SpoilerVertex<LETTER, STATE> vertex : mGame.getSpoilerVertices()) {
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + "), bnm:"
					+ vertex.getBEff() + ">");
		}
		for (final DuplicatorVertex<LETTER, STATE> vertex : mGame.getDuplicatorVertices()) {
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + ", " + vertex.getLetter()
					+ "), bnm:" + vertex.getBEff() + ">");
		}
		result.append(lineSeparator + "\t},");

		// Neighbor counter
		result.append(lineSeparator + "\tneighbor counter = {");
		for (final SpoilerVertex<LETTER, STATE> vertex : mGame.getSpoilerVertices()) {
			result.append(
					lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + "), nc:" + vertex.getC() + ">");
		}
		for (final DuplicatorVertex<LETTER, STATE> vertex : mGame.getDuplicatorVertices()) {
			result.append(lineSeparator + "\t\t<(" + vertex.getQ0() + ", " + vertex.getQ1() + ", " + vertex.getLetter()
					+ "), nc:" + vertex.getC() + ">");
		}
		result.append(lineSeparator + "\t},");

		// Footer
		result.append(lineSeparator + ");");

		return result.toString();
	}

	/**
	 * Does a single simulation calculation run. After it has finished the
	 * progress measure of all game graph vertices can be used to determine a
	 * simulation relation used for buechi reduction.<br/>
	 * Can also be used to validate a attempted change, if simulation did not
	 * get aborted the change is valid.
	 * 
	 * @param changes
	 *            Object to store made changes in, <tt>null</tt> if changes
	 *            should not get stored
	 * @return False if simulation was aborted because the underlying language
	 *         changed, true if not.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	private boolean doSingleSimulation(final GameGraphChanges<LETTER, STATE> changes)
			throws AutomataOperationCanceledException {
		if (isUsingSCCs()) {
			mpokedFromNeighborSCC = new HashSet<>();
			getSimulationPerformance().startTimeMeasure(ETimeMeasure.BUILD_SCC);
			final DefaultStronglyConnectedComponentFactory<Vertex<LETTER, STATE>> sccFactory = new DefaultStronglyConnectedComponentFactory<>();
			final GameGraphSuccessorProvider<LETTER, STATE> succProvider = new GameGraphSuccessorProvider<>(mGame);
			setSccComp(new SccComputation<Vertex<LETTER, STATE>, StronglyConnectedComponent<Vertex<LETTER, STATE>>>(
					mLogger, succProvider, sccFactory, mGame.getSize(), mGame.getVertices()));

			final Iterator<StronglyConnectedComponent<Vertex<LETTER, STATE>>> iter = new LinkedList<StronglyConnectedComponent<Vertex<LETTER, STATE>>>(
					getSccComp().getSCCs()).iterator();
			getSimulationPerformance().stopTimeMeasure(ETimeMeasure.BUILD_SCC);
			while (iter.hasNext()) {
				final StronglyConnectedComponent<Vertex<LETTER, STATE>> scc = iter.next();
				iter.remove();

				final int infinityOfSCC = calculateInfinityOfSCC(scc);

				mCurrentChanges = changes;
				efficientLiftingAlgorithm(infinityOfSCC, scc.getNodes());
				if (changes == null) {
					mAmountOfSCCs++;
				}
				if (mSimulationWasAborted) {
					return false;
				}
			}
		} else {
			mCurrentChanges = changes;
			efficientLiftingAlgorithm(mGlobalInfinity, null);
			if (mSimulationWasAborted) {
				return false;
			}
		}

		return true;
	}

	/**
	 * Initializes the simulation by adding the correct vertices to the working
	 * list and initializing their corresponding values.
	 * 
	 * @param localInfinity
	 *            The local infinity bound of the used SCC or global infinity if
	 *            not used
	 * @param scc
	 *            The currently for simulation used SCC or <tt>null</tt> if not
	 *            used
	 */
	private void initSimulation(final int localInfinity, final Set<Vertex<LETTER, STATE>> scc) {
		mSimulationWasAborted = false;
		createWorkingList();
		// Do not forget to reset the working list flag of all vertices to false
		// This is needed since a simulation can be aborted
		// before working all vertices
		if (isUsingSCCs()) {
			for (final Vertex<LETTER, STATE> vertex : scc) {
				initWorkingListAndCWithVertex(vertex, localInfinity, scc);
			}
		} else {
			for (final SpoilerVertex<LETTER, STATE> spoilerVertex : mGame.getSpoilerVertices()) {
				initWorkingListAndCWithVertex(spoilerVertex, localInfinity, scc);
			}
			for (final DuplicatorVertex<LETTER, STATE> duplicatorVertex : mGame.getDuplicatorVertices()) {
				initWorkingListAndCWithVertex(duplicatorVertex, localInfinity, scc);
			}
		}
	}

	/**
	 * Returns {@link SpoilerVertex} object that define states <b>(q0, q1)</b>
	 * which are candidates for merge.<br/>
	 * <br/>
	 * To be more precise, <b>(q0, q1)</b> if <b>q1 fair simulates q0</b> and
	 * <b>q0 fair simulates q1</b> which is indicated by a progress measure less
	 * than global infinity. Such states may can be merged with not changing the
	 * language.
	 * 
	 * @return Buechi states that are candidates for merge.
	 */
	private Set<SpoilerVertex<LETTER, STATE>> mergeCandidates() {
		final Set<SpoilerVertex<LETTER, STATE>> mergeCandidates = new HashSet<>();
		final Set<SpoilerVertex<LETTER, STATE>> spoilerVertices = mGame.getSpoilerVertices();
		final Set<SpoilerVertex<LETTER, STATE>> workedPairs = new HashSet<>();
		for (final SpoilerVertex<LETTER, STATE> vertex : spoilerVertices) {
			if (vertex.getPM(null, mGlobalInfinity) < mGlobalInfinity) {
				// Skip vertex if it is a trivial simulation
				if (vertex.getQ0().equals(vertex.getQ1())) {
					continue;
				}
				// Found a one-directed fair simulating pair
				final boolean pairIsNew = workedPairs.add(vertex);

				if (pairIsNew && workedPairs.contains(mGame.getSpoilerVertex(vertex.getQ1(), vertex.getQ0(), false))) {
					// Found a two-directed fair simulating pair
					mergeCandidates.add(vertex);
				}
			}
		}
		return mergeCandidates;
	}

	/**
	 * Processes a given collection of possible equivalent classes into a data
	 * structure that has a faster access for single states.
	 * 
	 * @param possibleEquivalentClasses
	 *            Collection to process
	 * @return Data structure with a fast access for state to its equivalent
	 *         class
	 */
	private Map<STATE, Set<STATE>> processEquivalenceClasses(final Collection<Set<STATE>> possibleEquivalentClasses) {
		Map<STATE, Set<STATE>> result;
		if (possibleEquivalentClasses.isEmpty()) {
			result = Collections.emptyMap();
		} else {
			result = new HashMap<>();
		}

		for (final Set<STATE> possibleEquivalentClass : possibleEquivalentClasses) {
			for (final STATE state : possibleEquivalentClass) {
				result.put(state, possibleEquivalentClass);
			}
		}

		return result;
	}

	/**
	 * Returns buechi transitions that are candidates for removal.<br/>
	 * <br/>
	 * To be more precise, transitions <b>q1 -a-> q2</b> where <b>q1 -a-> q3</b>
	 * exists and <b>q3 fair simulates q2</b>. Such transitions may be redundant
	 * and not change the language if removed.
	 * 
	 * @param exclusiveSet
	 *            Set of {@link SpoilerVertex} objects <b>(q2, q3)</b> that
	 *            define simulations that should not get considered for
	 *            candidate generation. In general this are vertices that get
	 *            merged, such transitions would get removed in the merging
	 *            process anyway.
	 * @return Buechi transitions that are candidates for removal and the
	 *         corresponding simulating state <i>q3</i>.
	 */
	private HashSet<Quad<STATE, LETTER, STATE, STATE>> transitionCandidates(
			final Set<SpoilerVertex<LETTER, STATE>> exclusiveSet) {
		final HashSet<Quad<STATE, LETTER, STATE, STATE>> transitionCandidates = new HashSet<>();
		final Set<SpoilerVertex<LETTER, STATE>> spoilerVertices = mGame.getSpoilerVertices();
		for (final SpoilerVertex<LETTER, STATE> vertex : spoilerVertices) {
			if (vertex.getPM(null, mGlobalInfinity) < mGlobalInfinity && !exclusiveSet.contains(vertex)) {
				// Skip vertex if it is a trivial simulation
				if (vertex.getQ0().equals(vertex.getQ1())) {
					continue;
				}

				// Searching for transition
				// q1 -a-> q2 where q1 -a-> q3 and q3 simulating q2
				final STATE simulatingState = vertex.getQ1();
				final STATE simulatedState = vertex.getQ0();
				for (final IncomingInternalTransition<LETTER, STATE> predTrans : mGame.getAutomaton()
						.internalPredecessors(simulatingState)) {
					final STATE src = predTrans.getPred();
					final LETTER a = predTrans.getLetter();
					final STATE dest = simulatedState;
					final Triple<STATE, LETTER, STATE> transition = new Triple<>(src, a, dest);
					if (mGame.hasBuechiTransition(transition)) {
						transitionCandidates.add(new Quad<>(src, a, dest, simulatingState));
					}
				}
			}
		}
		return transitionCandidates;
	}

	/**
	 * Validates a given change by re running a single simulation calculation
	 * and comparing its results to the previous.<br/>
	 * If the change is valid <tt>null</tt> gets returned, if not an extended
	 * fair game graph changes object gets returned that includes the previous
	 * changes and also the changes made in the simulation calculation used for
	 * verification.
	 * 
	 * @param changes
	 *            Made changes to validate
	 * @return A game graph changes object that has all made changes stored if
	 *         the attempted change is not valid or <tt>null</tt> if it is
	 *         valid. Can be used to undo changes by using
	 *         {@link AGameGraph#undoChanges(GameGraphChanges)}.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	private FairGameGraphChanges<LETTER, STATE> validateChange(FairGameGraphChanges<LETTER, STATE> changes)
			throws AutomataOperationCanceledException {
		// Only do simulation if there actually was a change
		boolean wasSuccessful = true;
		if (changes != null) {
			wasSuccessful = doSingleSimulation(changes);
		}

		// Discard changes if language did not change
		// so that they can not be undone.
		if (wasSuccessful) {
			changes = null;
		}

		return changes;
	}

	/**
	 * Attempts the simulated merge of two given buechi states and returns
	 * whether the change is valid or not.
	 * 
	 * @param firstState
	 *            First state to merge
	 * @param secondState
	 *            Second state to merge
	 * @return A game graph changes object that has all made changes stored if
	 *         the attempted change is not valid or <tt>null</tt> if it is
	 *         valid. Can be used to undo changes by using
	 *         {@link AGameGraph#undoChanges(GameGraphChanges)}.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	protected FairGameGraphChanges<LETTER, STATE> attemptMerge(final STATE firstState, final STATE secondState)
			throws AutomataOperationCanceledException {
		// Optimize the attempted merge if we have information about equivalence
		// classes of the states
		if (!mPossibleEquivalentClasses.isEmpty()) {
			final Set<STATE> equivalenceClass = mPossibleEquivalentClasses.get(firstState);
			// If the states are not in the same equivalence class we already
			// know that the merge can not be possible
			if (equivalenceClass != null && !equivalenceClass.contains(secondState)) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("\tAttempted merge for " + firstState + " and " + secondState
							+ " is clearly not possible since they are in different equivalence classes.");
				}

				return new FairGameGraphChanges<>();
			}
		}

		// If both states are already in the same equivalence class the merge is
		// guaranteed to success.
		// This often happens if both states already can be merged with a third
		// state, then they obviously also can be merged.
		if (mGame.areInSameEquivalenceClasses(firstState, secondState)) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("\tAttempted merge for " + firstState + " and " + secondState
						+ " is clearly possible since they already are in the same equivalence class.");
			}
			return null;
		}

		final FairGameGraphChanges<LETTER, STATE> changes = mGame.equalizeBuechiStates(firstState, secondState);

		return validateChange(changes);
	}

	/**
	 * Attempts the simulated removal of an buechi transition and returns
	 * whether the change is valid or not.
	 * 
	 * @param src
	 *            Source of the transition
	 * @param a
	 *            Letter of the transition
	 * @param dest
	 *            Destination of the transition
	 * @param invoker
	 *            State that invoked the transition removal. In general this is
	 *            the state that simulates the transition.
	 * @return A game graph changes object that has all made changes stored if
	 *         the attempted change is not valid or <tt>null</tt> if it is
	 *         valid. Can be used to undo changes by using
	 *         {@link AGameGraph#undoChanges(GameGraphChanges)}.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	protected FairGameGraphChanges<LETTER, STATE> attemptTransitionRemoval(final STATE src, final LETTER a,
			final STATE dest, final STATE invoker) throws AutomataOperationCanceledException {
		final FairGameGraphChanges<LETTER, STATE> changes = mGame.removeBuechiTransition(src, a, dest);

		return validateChange(changes);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.ASimulation#efficientLiftingAlgorithm(int, java.util.Set)
	 */
	@Override
	protected void efficientLiftingAlgorithm(final int localInfinity, final Set<Vertex<LETTER, STATE>> scc)
			throws AutomataOperationCanceledException {
		final SimulationPerformance performance = super.getSimulationPerformance();
		if (debugSimulation) {
			mLogger.debug("Lifting SCC: " + scc);
		}

		// Initialize working list and the C value of the correct vertices
		initSimulation(localInfinity, scc);

		if (debugSimulation) {
			mLogger.debug("WL: " + getWorkingList());
		}

		// Work through the working list until its empty
		while (!getWorkingList().isEmpty()) {
			performance.increaseCountingMeasure(ECountingMeasure.SIMULATION_STEPS);

			// Poll the current working vertex
			final Vertex<LETTER, STATE> workingVertex = pollVertexFromWorkingList();

			if (debugSimulation) {
				mLogger.debug("\tWorking with: " + workingVertex);
			}

			// Ignore bounds of own SCC if vertex was poked
			Set<Vertex<LETTER, STATE>> usedSCCForNeighborCalculation = scc;
			if (isUsingSCCs() && mpokedFromNeighborSCC.contains(workingVertex)) {
				usedSCCForNeighborCalculation = null;
				if (debugSimulation) {
					mLogger.debug("\t\tVertex was poked.");
				}
			}

			// Remember old progress measure of the working vertex
			final int oldProgressMeasure = workingVertex.getPM(scc, mGlobalInfinity);

			// Update values of the working vertex
			final int oldBEff = workingVertex.getBEff();
			workingVertex.setBEff(calcBestNghbMeasure(workingVertex, localInfinity, usedSCCForNeighborCalculation));
			saveBEffChange(workingVertex, oldBEff, mCurrentChanges);

			if (debugSimulation) {
				mLogger.debug("\t\tUpdated BEff: " + oldBEff + " -> " + workingVertex.getBEff());
			}

			final int oldC = workingVertex.getC();
			workingVertex.setC(calcNghbCounter(workingVertex, localInfinity, usedSCCForNeighborCalculation));
			saveCChange(workingVertex, oldC, mCurrentChanges);

			if (debugSimulation) {
				mLogger.debug("\t\tUpdated C: " + oldC + " -> " + workingVertex.getC());
			}

			final int currentProgressMeasure = increaseVector(mGame.getPriority(workingVertex), workingVertex.getBEff(),
					localInfinity);
			workingVertex.setPM(currentProgressMeasure);
			savePmChange(workingVertex, oldProgressMeasure, mCurrentChanges);

			if (debugSimulation) {
				mLogger.debug("\t\tUpdated PM: " + oldProgressMeasure + " -> " + currentProgressMeasure);
			}

			// If vertex now defines a non trivial non possible simulation
			if (currentProgressMeasure >= mGlobalInfinity) {
				if (workingVertex.isSpoilerVertex() && !workingVertex.getQ0().equals(workingVertex.getQ1())) {
					final boolean wasAdded = mNotSimulatingNonTrivialVertices
							.add((SpoilerVertex<LETTER, STATE>) workingVertex);
					if (mAttemptingChanges && wasAdded) {
						// Abort simulation since progress measure
						// has changed on a non trivial vertex
						// which indicates language change
						mNotSimulatingNonTrivialVertices.remove(workingVertex);
						mSimulationWasAborted = true;

						if (debugSimulation) {
							mLogger.debug("\t\tAborting simulation since " + workingVertex + " reached infinity.");
						}
						return;
					}
				}
			}

			// Skip updating predecessors if there are no
			final boolean considerPushOverPredecessors = workingVertex.getPM(scc, mGlobalInfinity) == mGlobalInfinity && mGame.hasPushOverPredecessors(workingVertex);
			final Set<Vertex<LETTER, STATE>> predVertices = mGame.getPredecessors(workingVertex);
			if ((predVertices == null || predVertices.isEmpty()) && !considerPushOverPredecessors) {
				continue;
			}

			// Work through its predecessors and possibly add them
			// to the working list since they may be interested in
			// the changes of the working vertex
			Set<Vertex<LETTER, STATE>> predecessorsToConsider = predVertices;
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
				predecessorsToConsider.addAll(mGame.getPushOverPredecessors(workingVertex));
			}
			for (final Vertex<LETTER, STATE> pred : predecessorsToConsider) {
				if (debugSimulation) {
					mLogger.debug("\t\tWorking pred: " + pred);
				}

				if (pred.isInWL()) {
					// Skip predecessor if already in working list
					continue;
				}

				// If vertex has newly reached localInfinity and predecessor,
				// which is a 1-distance neighbor of SCC, is interested
				boolean pokePossible = false;
				if (isUsingSCCs() && !scc.contains(pred)) {
					final boolean hasNewlyReachedInfinity = currentProgressMeasure >= localInfinity
							&& oldProgressMeasure < localInfinity;
					pokePossible = hasNewlyReachedInfinity && !mpokedFromNeighborSCC.contains(pred);

					if (debugSimulation) {
						mLogger.debug("\t\t\tPoke possible for pred: " + pred);
					}
					if (!pokePossible) {
						// Do not further look at predecessor outside SCC if
						// poke not possible
						continue;
					}
				}

				// If the working vertex has increased its progress
				// measure from the perspective of the predecessor and
				// its priority
				if (decreaseVector(mGame.getPriority(pred), workingVertex.getPM(scc, mGlobalInfinity),
						localInfinity) > pred.getBEff()) {

					// A Duplicator vertex is only interested in an increased
					// progress measure if the working vertex was its
					// best choice previously and it has no better
					// alternative now
					if (pred.isDuplicatorVertex() && (decreaseVector(mGame.getPriority(pred), oldProgressMeasure,
							localInfinity) == pred.getBEff() || (pokePossible && pred.getBEff() == 0))) {

						// If trying to use a vertex outside of the SCC make
						// sure the neighbor counter was initialized
						// before accessing it
						if (pokePossible) {
							if (pred.getC() == 0) {
								final int oldPredC = pred.getC();
								pred.setC(mGame.getSuccessors(pred).size());
								saveCChange(pred, oldPredC, mCurrentChanges);
							}
						}

						if (pred.getC() == 1) {
							// It has no better alternative,
							// adding to working list or poking
							if (pokePossible) {
								mpokedFromNeighborSCC.add(pred);

								if (debugSimulation) {
									mLogger.debug("\t\t\tPred has no better alternative, poking.");
								}
							} else {
								addVertexToWorkingList(pred);

								if (debugSimulation) {
									mLogger.debug("\t\t\tPred has no better alternative, adding.");
								}
							}
						} else if (pred.getC() > 1) {
							// It has a better alternative, reducing number of
							// neighbors that represent the best choice for the
							// predecessor
							final int oldPredC = pred.getC();
							pred.setC(pred.getC() - 1);
							saveCChange(pred, oldPredC, mCurrentChanges);

							if (debugSimulation) {
								mLogger.debug("\t\t\tPred has a better alternative.");
							}
						}
					} else if (pred.isSpoilerVertex()) {
						// A Spoiler vertex is always interested in an increased
						// progress measure,
						// adding to working list or poking
						if (pokePossible) {
							mpokedFromNeighborSCC.add(pred);

							if (debugSimulation) {
								mLogger.debug("\t\t\tPred is spoiler, poking.");
							}
						} else {
							addVertexToWorkingList(pred);

							if (debugSimulation) {
								mLogger.debug("\t\t\tPred is spoiler, adding.");
							}
						}
					}
				}
			}

			// Update poked set if worked a poked vertex
			if (isUsingSCCs() && mpokedFromNeighborSCC.contains(workingVertex)) {
				mpokedFromNeighborSCC.remove(workingVertex);
			}

			// If operation was canceled, for example from the
			// Ultimate framework
			if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
				mLogger.debug("Stopped in efficientLiftingAlgorithm");
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.ASimulation#getGameGraph()
	 */
	@Override
	protected AGameGraph<LETTER, STATE> getGameGraph() {
		return mGame;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.ASimulation#initWorkingListAndCWithVertex(de.uni_freiburg.
	 * informatik.ultimate.automata.nwalibrary.operations.buchiReduction.
	 * vertices.Vertex, int, java.util.Set)
	 */
	@Override
	protected void initWorkingListAndCWithVertex(final Vertex<LETTER, STATE> vertex, final int localInfinity,
			final Set<Vertex<LETTER, STATE>> scc) {
		// Small note for debugging: If simulation calculates a wrong result
		// this, in most cases, is because there are important vertices missing
		// in the working list. Cross check by adding 'true' to the if-clause
		// which adds all vertices to the working list (inefficient but result
		// could then be correct).
		final boolean isDeadEnd = !mGame.hasSuccessors(vertex);
		final boolean hasPriorityOne = mGame.getPriority(vertex) == 1;
		final boolean isPokedVertex = isUsingSCCs() && mpokedFromNeighborSCC.contains(vertex);
		final boolean isNonTrivialAddedVertex = mAttemptingChanges && mCurrentChanges != null
				&& mCurrentChanges.isAddedVertex(vertex) && mGame.getPriority(vertex) != 0;
		final boolean isVertexInvolvedInEdgeChanges = mAttemptingChanges && mCurrentChanges != null
				&& mCurrentChanges.isVertexInvolvedInEdgeChanges(vertex);

		// Possibly add vertex to working list
		if (isDeadEnd || hasPriorityOne || isPokedVertex || isNonTrivialAddedVertex || isVertexInvolvedInEdgeChanges) {
			addVertexToWorkingList(vertex);
		} else {
			// Reset working list flag of vertex since it can be true from an
			// previous simulation abort
			vertex.setInWL(false);
		}

		// Possibly initialize C value of vertex
		if (isUsingSCCs()) {
			Set<Vertex<LETTER, STATE>> usedSCCForNeighborCalculation = scc;
			// Ignore bounds of own SCC if vertex was poked
			if (mpokedFromNeighborSCC.contains(vertex)) {
				usedSCCForNeighborCalculation = null;
			}
			final int oldC = vertex.getC();
			vertex.setC(calcNghbCounter(vertex, localInfinity, usedSCCForNeighborCalculation));
			saveCChange(vertex, oldC, mCurrentChanges);
		} else if (!isDeadEnd) {
			final boolean isFirstRun = !mAttemptingChanges;
			final boolean wasNotInitialized = vertex.getC() == 0;

			if (isFirstRun || wasNotInitialized) {
				final int oldC = vertex.getC();
				vertex.setC(mGame.getSuccessors(vertex).size());
				saveCChange(vertex, oldC, mCurrentChanges);
			}
		}
	}
}