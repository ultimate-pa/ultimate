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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Set;
import java.util.function.BiPredicate;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonFilteredStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Determinize;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizationStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaMaxSat2;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaPmaxSat;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaPmaxSatDirect;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ASimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.GameGraphChanges;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.SimulationOrMinimizationType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.fair.FairGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance.CountingMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance.SimulationPerformance;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance.TimeMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.LoopDetector;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.NwaSimulationUtil;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.SearchElement;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.TransitionType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.GameDoubleDeckerSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.GameFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.GameSpecialSinkState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.GameSpoilerNwaVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.IGameLetter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.IGameState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.summarycomputationgraph.GameCallReturnSummary;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.summarycomputationgraph.SummaryComputation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.util.HashRelationBackedSetOfPairs;
import de.uni_freiburg.informatik.ultimate.automata.util.PartitionBackedSetOfPairs;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UniqueQueue;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Hep;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Quin;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Generates double decker game graphs based on nwa automaton. Supports different types of simulation types.
 *
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 * @param <LETTER>
 *            Letter class of nwa automaton
 * @param <STATE>
 *            State class of nwa automaton
 */
public final class NwaGameGraphGeneration<LETTER, STATE> {

	/**
	 * The priority of Duplicator vertices, it is a constant.
	 */
	public static final int DUPLICATOR_PRIORITY = 2;
	/**
	 * Data structure that allows a fast access to {@link DuplicatorVertex} objects by using their representation:<br/>
	 * <b>(Up state of spoiler or q0, up state of duplicator or q1, letter spoiler used before, bit, type of transition,
	 * summarize edge, sink)</b>.
	 */
	private final HashMap<Hep<STATE, STATE, LETTER, Boolean, TransitionType, SummarizeEdge<LETTER, STATE>, IWinningSink<LETTER, STATE>>, DuplicatorVertex<LETTER, STATE>> mAutomatonStatesToGraphDuplicatorVertex;
	/**
	 * Data structure that allows a fast access to {@link SpoilerVertex} objects by using their representation:<br/>
	 * <b>(Up state of spoiler or q0, up state of duplicator or q1, bit, summarize edge, sink)</b>.
	 */
	private final HashMap<Quin<STATE, STATE, Boolean, SummarizeEdge<LETTER, STATE>, IWinningSink<LETTER, STATE>>, SpoilerVertex<LETTER, STATE>> mAutomatonStatesToGraphSpoilerVertex;

	/**
	 * Auxiliary game state, is used at summarize edge computation for pointing to dead-end return vertices.
	 */
	private final GameSpecialSinkState mAuxiliaryGameState;
	/**
	 * Provides a fast access to all Spoiler vertices that are directly losing for Duplicator, if he moves in. The set
	 * is only used if the simulation type is direct simulation.
	 */
	private final HashSet<SpoilerNwaVertex<LETTER, STATE>> mDuplicatorDirectlyLosesInSpoiler;

	/**
	 * Data structure of all duplicator vertices that have the transition type {@link TransitionType#RETURN}. They are
	 * used for summarize edge generation.
	 */
	private final HashSet<DuplicatorNwaVertex<LETTER, STATE>> mDuplicatorReturningVertices;
	/**
	 * Instance of a Duplicator winning sink, <tt>null</tt> if not used.
	 */
	private DuplicatorWinningSink<LETTER, STATE> mDuplicatorWinningSink;
	/**
	 * Map of all winning sinks of the graph. Provides a fast access via the sink entry.
	 */
	private final HashMap<Vertex<LETTER, STATE>, IWinningSink<LETTER, STATE>> mEntryToSink;
	/**
	 * Game graph to generate a double decker nwa graph for.
	 */
	private final AGameGraph<LETTER, STATE> mGameGraph;
	/**
	 * ILogger of the Ultimate framework.
	 */
	private final ILogger mLogger;
	/**
	 * The underlying nwa automaton, as double decker automaton, from which the game graph gets generated.
	 */
	private final IDoubleDeckerAutomaton<LETTER, STATE> mNwa;
	/**
	 * A collection of sets which contains states of the an automaton that may be merge-able. States which are not in
	 * the same set are definitely not merge-able which is used as an optimization for the game graph.
	 */
	private final Iterable<Set<STATE>> mPossibleEquivalenceClasses;
	/**
	 * Data structure of all duplicator vertices that may end up being a dead end and are not using a return transition.
	 */
	private final HashSet<DuplicatorNwaVertex<LETTER, STATE>> mPossibleNonReturnDuplicatorDeadEnd;
	/**
	 * Data structure of all spoiler vertices that may end up being a dead end, because they can not take a
	 * return-transition due to their down state.
	 */
	private final HashSet<SpoilerNwaVertex<LETTER, STATE>> mPossibleSpoilerDeadEnd;
	/**
	 * Timer used for responding to timeouts and operation cancellation.
	 */
	private final IProgressAwareTimer mProgressTimer;
	/**
	 * Object that stores all changes made for removing return vertices and their edges. It includes the removed
	 * returning vertex, its out- and in-going edges and generated push-over edges.
	 */
	private final GameGraphChanges<LETTER, STATE> mRemovedReturnBridges;
	/**
	 * If the game graph should be restricted to the initial partition, given by the parameter
	 * <tt>possibleEquivalenceClasses</tt>. If <tt>true</tt> only vertices that represent state combinations which
	 * possibly are simulating get generated, all other will be rejected. If <tt>false</tt> also vertices that are
	 * reachable by the initial partition get generated.
	 */
	private final boolean mRestrictGraphToInitPart;
	/**
	 * Service provider of Ultimate framework.
	 */
	private final AutomataLibraryServices mServices;
	/**
	 * Performance logging for this object.
	 */
	private final SimulationPerformance mSimulationPerformance;
	/**
	 * Type of the simulation to use.
	 */
	private final SimulationOrMinimizationType mSimulationType;
	/**
	 * Instance of a Spoiler winning sink, <tt>null</tt> if not used.
	 */
	private SpoilerWinningSink<LETTER, STATE> mSpoilerWinningSink;
	/**
	 * Instance of an extended Spoiler winning sink, <tt>null</tt> if not used.
	 */
	private SpoilerWinningSinkExtended<LETTER, STATE> mSpoilerWinningSinkExtended;
	/**
	 * Map of all summarize edges of the graph. Provides a fast access via source and destinations of the edge.
	 */
	private final NestedMap2<SpoilerNwaVertex<LETTER, STATE>, Pair<STATE, Set<Pair<STATE, Boolean>>>, SummarizeEdge<LETTER, STATE>> mSrcDestToSummarizeEdges;
	/**
	 * If the game graph should use push-over edges between successors and predecessors of return-invoking Duplicator
	 * vertices. If set to <tt>true</tt>, push-over edges will be generated.
	 */
	private final boolean mUsePushOverEdges;

	/**
	 * Creates a new generation object that modifies a given graph using a given nwa automaton and a desired simulation
	 * method.
	 *
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param progressTimer
	 *            Timer used for responding to timeouts and operation cancellation.
	 * @param logger
	 *            ILogger of the Ultimate framework.
	 * @param nwa
	 *            The underlying nwa automaton from which the game graph gets generated.
	 * @param gameGraph
	 *            Game graph that should get modified by this object
	 * @param simulationType
	 *            Simulation method to use for graph generation. Supported types are
	 *            {@link SimulationOrMinimizationType#DIRECT DIRECT}, {@link SimulationOrMinimizationType#DELAYED
	 *            DELAYED} and {@link SimulationOrMinimizationType#FAIR FAIR}.
	 * @param possibleEquivalenceClasses
	 *            A collection of sets which contains states of an automaton that may be merge-able. States which are
	 *            not in the same set are definitely not merge-able which is used as an optimization for the game graph
	 * @param restrictGraphToInitPart
	 *            If the game graph should be restricted to the initial partition, given by the parameter
	 *            <tt>possibleEquivalenceClasses</tt>. If <tt>true</tt> only vertices that represent state combinations
	 *            which possibly are simulating get generated, all other will be rejected. If <tt>false</tt> also
	 *            vertices that are reachable by the initial partition get generated.
	 */
	public NwaGameGraphGeneration(final AutomataLibraryServices services, final IProgressAwareTimer progressTimer,
			final ILogger logger, final IDoubleDeckerAutomaton<LETTER, STATE> nwa,
			final AGameGraph<LETTER, STATE> gameGraph, final SimulationOrMinimizationType simulationType,
			final Iterable<Set<STATE>> possibleEquivalenceClasses, final boolean restrictGraphToInitPart) {
		mServices = services;
		mNwa = nwa;
		mAutomatonStatesToGraphDuplicatorVertex = new HashMap<>();
		mAutomatonStatesToGraphSpoilerVertex = new HashMap<>();
		mDuplicatorReturningVertices = new HashSet<>();
		mPossibleSpoilerDeadEnd = new HashSet<>();
		mPossibleNonReturnDuplicatorDeadEnd = new HashSet<>();
		mDuplicatorDirectlyLosesInSpoiler = new HashSet<>();
		mSrcDestToSummarizeEdges = new NestedMap2<>();
		mEntryToSink = new HashMap<>();
		mRemovedReturnBridges = new GameGraphChanges<>();
		mAuxiliaryGameState = new GameSpecialSinkState();
		mLogger = logger;
		mProgressTimer = progressTimer;
		mGameGraph = gameGraph;
		mSimulationType = simulationType;
		mUsePushOverEdges = false;

		mSpoilerWinningSink = null;
		mSpoilerWinningSinkExtended = null;
		mDuplicatorWinningSink = null;

		mSimulationPerformance = new SimulationPerformance(simulationType, false);

		mPossibleEquivalenceClasses = possibleEquivalenceClasses;
		mRestrictGraphToInitPart = restrictGraphToInitPart;
	}

	/**
	 * Clears all internal data structures of this object.
	 */
	public void clear() {
		mAutomatonStatesToGraphDuplicatorVertex.clear();
		mAutomatonStatesToGraphSpoilerVertex.clear();
		mPossibleSpoilerDeadEnd.clear();
		mPossibleNonReturnDuplicatorDeadEnd.clear();
		mDuplicatorReturningVertices.clear();
		mEntryToSink.clear();
		mSrcDestToSummarizeEdges.clear();
		mDuplicatorDirectlyLosesInSpoiler.clear();
	}

	/**
	 * Computes the priorities of all previous generated summarize edges.
	 * <p>
	 * Throws an IllegalStateException if computing summarize edge priorities could not be done because a live lock
	 * occurred.
	 * 
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate framework.
	 */
	public void computeSummarizeEdgePriorities() throws AutomataOperationCanceledException {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Computing priorities of summarize edges.");
		}

		final Queue<SearchElement<LETTER, STATE>> searchQueue = new UniqueQueue<>();
		final NestedMap3<Vertex<LETTER, STATE>, SummarizeEdge<LETTER, STATE>, Pair<STATE, Boolean>, Integer> vertexToSubSummarizeToSearchPriority =
				new NestedMap3<>();
		final LoopDetector<LETTER, STATE> loopDetector = new LoopDetector<>(mGameGraph, mLogger, mProgressTimer);

		// Add starting elements
		for (final Triple<SpoilerNwaVertex<LETTER, STATE>, Pair<STATE, Set<Pair<STATE, Boolean>>>, SummarizeEdge<LETTER, STATE>> summarizeEdgeEntry : mSrcDestToSummarizeEdges
				.entrySet()) {
			final SummarizeEdge<LETTER, STATE> summarizeEdge = summarizeEdgeEntry.getThird();
			// In direct simulation every edge will have a priority of zero,
			// since nearly every vertex has a priority of zero.
			if (mSimulationType == SimulationOrMinimizationType.DIRECT) {
				// Do not add something to the queue and finish
				// the method by that
				summarizeEdge.setAllPriorities(0);
			} else {
				final Vertex<LETTER, STATE> edgeSource = summarizeEdge.getSource();
				for (final Pair<STATE, Boolean> duplicatorChoiceEntry : summarizeEdge.getDuplicatorChoices()) {
					// We are now iterating every sub-summarize edge
					// Find out all SpoilerInvoker and create search elements
					for (final SpoilerNwaVertex<LETTER, STATE> spoilerInvoker : summarizeEdge
							.getSpoilerInvokers(duplicatorChoiceEntry)) {
						final SearchElement<LETTER, STATE> searchElement = new SearchElement<>(spoilerInvoker,
								edgeSource, null, summarizeEdge, duplicatorChoiceEntry, spoilerInvoker);
						searchQueue.add(searchElement);
					}
				}
			}
		}

		// Start the search
		while (!searchQueue.isEmpty()) {
			final SearchElement<LETTER, STATE> searchElement = searchQueue.poll();
			final Vertex<LETTER, STATE> searchVertex = searchElement.getVertex();
			final Vertex<LETTER, STATE> searchTarget = searchElement.getTarget();
			final SummarizeEdge<LETTER, STATE> searchSummarizeEdge = searchElement.getSummarizeEdge();
			final Pair<STATE, Boolean> searchDuplicatorChoice = searchElement.getDuplicatorChoice();
			final Vertex<LETTER, STATE> searchOrigin = searchElement.getOrigin();
			final Vertex<LETTER, STATE> searchHistory = searchElement.getHistory();

			boolean isSearchVertexDuplicatorNwa = false;
			DuplicatorNwaVertex<LETTER, STATE> searchVertexAsDuplicatorNwa = null;
			if (searchVertex instanceof DuplicatorNwaVertex) {
				searchVertexAsDuplicatorNwa = (DuplicatorNwaVertex<LETTER, STATE>) searchVertex;
				isSearchVertexDuplicatorNwa = true;
			}
			// Calculate search priority of element by using the priorities of
			// successors
			int optimalSuccPriority = SummarizeEdge.NO_PRIORITY;
			int optimalNonLoopSuccPriority = SummarizeEdge.NO_PRIORITY;
			int optimalLoopSuccPriority = SummarizeEdge.NO_PRIORITY;
			final boolean isSpoiler = searchVertex.isSpoilerVertex();
			int optimalValue;
			int worstValue;
			if (isSpoiler) {
				optimalValue = 1;
				worstValue = 0;
			} else {
				optimalValue = 0;
				worstValue = 1;
			}
			// We first use priorities of non-loop successors. If the computed
			// search priority is not the worst value, we also take loop
			// successors into account.
			final Set<Vertex<LETTER, STATE>> successors = mGameGraph.getSuccessors(searchVertex);
			if (successors != null) {
				for (Vertex<LETTER, STATE> succ : successors) {
					int succPriority = SummarizeEdge.NO_PRIORITY;
					// Reject successor if it is null
					if (succ == null) {
						continue;
					}
					if (succ instanceof DuplicatorNwaVertex<?, ?>) {
						// Successor is duplicator vertex
						final DuplicatorNwaVertex<LETTER, STATE> succAsDuplicatorNwa =
								(DuplicatorNwaVertex<LETTER, STATE>) succ;
						final TransitionType transitionType = succAsDuplicatorNwa.getTransitionType();
						// We will reject successor if it has no search priority
						// yet. This may indicate that the successor is
						// not capable of reaching the destination of
						// the summarize edge, which priority currently
						// shall be computed. If it, however, is capable
						// of that, he may force an update on the
						// current vertex later anyway. At this time the
						// successor will also have a search priority.
						if (transitionType == TransitionType.RETURN || transitionType == TransitionType.SINK
								|| transitionType == TransitionType.SUMMARIZE_EXIT) {
							// Ignore return and special edges
							continue;
						} else if (transitionType == TransitionType.SUMMARIZE_ENTRY) {
							// Use min(summarizeEdgePriority,
							// summarizeEdgeDestinationPriority) as priority
							// candidate
							final SummarizeEdge<LETTER, STATE> summarizeEdge = succAsDuplicatorNwa.getSummarizeEdge();

							// Ignore the summarize edge if it does not belong
							// to the history vertex
							if (!summarizeEdge.getDestinations().contains(searchHistory)) {
								continue;
							}

							// Determine the choice of Duplicator via the
							// history element
							final STATE duplicatorChoiceHistory = searchHistory.getQ1();
							final boolean choiceBitHistory = searchHistory.isB();
							final Pair<STATE, Boolean> choiceHistory =
									new Pair<>(duplicatorChoiceHistory, choiceBitHistory);
							final Vertex<LETTER, STATE> destination = summarizeEdge.getDestination(choiceHistory);
							int summarizeEdgePriority = summarizeEdge.getPriority(choiceHistory);
							if (summarizeEdgePriority == SummarizeEdge.NO_PRIORITY) {
								// If summarize edge has no priority yet, use
								// the neutral element 2.
								summarizeEdgePriority = 2;
							}
							final Integer destinationSearchPriority = vertexToSubSummarizeToSearchPriority
									.get(destination, searchSummarizeEdge, searchDuplicatorChoice);
							if (destinationSearchPriority == null
									|| destinationSearchPriority == SummarizeEdge.NO_PRIORITY) {
								continue;
							}
							succPriority = Math.min(summarizeEdgePriority, destinationSearchPriority);
							// Change successor to destination. This
							// represents following the summarize edge instead
							// of using the fake vertices, which are used to
							// model the summarize edge.
							succ = destination;
						} else {
							final Integer succSearchPriority = vertexToSubSummarizeToSearchPriority.get(succ,
									searchSummarizeEdge, searchDuplicatorChoice);
							if (succSearchPriority == null || succSearchPriority == SummarizeEdge.NO_PRIORITY) {
								continue;
							}
							succPriority = succSearchPriority;
						}
					} else {
						// Successor is spoiler vertex
						if (isSearchVertexDuplicatorNwa) {
							final TransitionType transitionType = searchVertexAsDuplicatorNwa.getTransitionType();
							if (transitionType == TransitionType.RETURN || transitionType == TransitionType.SINK
									|| transitionType == TransitionType.SUMMARIZE_ENTRY
									|| transitionType == TransitionType.SUMMARIZE_EXIT) {
								// Ignore return and special edges
								break;
							}
							final Integer succSearchPriority = vertexToSubSummarizeToSearchPriority.get(succ,
									searchSummarizeEdge, searchDuplicatorChoice);
							if (succSearchPriority == null || succSearchPriority == SummarizeEdge.NO_PRIORITY) {
								continue;
							}
							succPriority = succSearchPriority;
						}
					}
					// Evaluate the priority of the current successor
					// Differentiate between non-loop and loop vertices
					if (!loopDetector.isLoopVertex(succ, searchOrigin, searchVertex)) {
						// Search for the optimal value under all successors.
						// If that is not present try to increase to 2 until
						// optimal value is reached.
						if (optimalNonLoopSuccPriority != optimalValue) {
							if (succPriority > optimalNonLoopSuccPriority) {
								optimalNonLoopSuccPriority = succPriority;
							}
							if (succPriority == optimalValue) {
								optimalNonLoopSuccPriority = succPriority;
								// Break since the optimal value is found, it
								// can not get better anymore.
								break;
							}
						}
					} else {
						if (mLogger.isDebugEnabled()) {
							mLogger.debug("\t\tSuccessor is loop vertex: " + succ);
						}
						if (optimalLoopSuccPriority != optimalValue) {
							if (succPriority > optimalLoopSuccPriority) {
								optimalLoopSuccPriority = succPriority;
							}
							if (succPriority == optimalValue) {
								optimalLoopSuccPriority = succPriority;
								// Do not break, it may be possible that loop
								// priorities get not involved in priority
								// computation.
							}
						}
					}
					// If operation was canceled, for example from the
					// Ultimate framework
					if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
						mLogger.debug("Stopped in computeSummarizeEdgePriorties/successors");
						throw new AutomataOperationCanceledException(this.getClass());
					}
				}
				// If the current optimal non-loop successor priority is not
				// the worst value, also take loop vertices into account.
				if (optimalNonLoopSuccPriority == worstValue) {
					// If non-loop vertices all have the worst value, we must
					// not take loop vertices into account.
					optimalSuccPriority = worstValue;
					mLogger.debug("\t\tWe do not use loop succesors for priority computation.");
				} else if (optimalNonLoopSuccPriority == SummarizeEdge.NO_PRIORITY) {
					// If value unknown, take the other value.
					optimalSuccPriority = optimalLoopSuccPriority;
				} else if (optimalLoopSuccPriority == SummarizeEdge.NO_PRIORITY) {
					// If value unknown, take the other value.
					optimalSuccPriority = optimalNonLoopSuccPriority;
				} else if (optimalLoopSuccPriority == worstValue) {
					// If value is the worst, take the other value.
					optimalSuccPriority = optimalNonLoopSuccPriority;
				} else if (optimalNonLoopSuccPriority == optimalValue || optimalLoopSuccPriority == optimalValue) {
					// If one has the optimal value, take it.
					optimalSuccPriority = optimalValue;
				} else {
					// In this case both values are 2.
					optimalSuccPriority = 2;
				}
			}
			// Vertex is forced to select the minimum from the optimal
			// successor priority and its own priority
			int searchPriority;
			final int searchVertexPriority = searchVertex.getPriority();
			if (optimalSuccPriority != SummarizeEdge.NO_PRIORITY) {
				searchPriority = Math.min(optimalSuccPriority, searchVertexPriority);
			} else {
				searchPriority = searchVertexPriority;
			}
			// Put the search priority for the vertex and decide whether to
			// continue the search for this element
			final Integer previousSearchPriorityValue = vertexToSubSummarizeToSearchPriority.put(searchVertex,
					searchSummarizeEdge, searchDuplicatorChoice, searchPriority);
			boolean continueSearch = false;
			// Continue search if a search priority is new for the
			// vertex or if values have changed.
			// The search will converge to a fix point since min-method
			// is monotone and the set of priorities is bounded.
			if (previousSearchPriorityValue == null || previousSearchPriorityValue != searchPriority) {
				continueSearch = true;
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("\tSetting '" + searchPriority + "' for: " + searchElement);
				}
				// If search element is a duplicator vertex that uses a call
				// transition, then update the priority of the corresponding
				// summarize edges, if existent and possibly stop the search for
				// this element.
				if (isSearchVertexDuplicatorNwa) {
					final TransitionType transitionType = searchVertexAsDuplicatorNwa.getTransitionType();
					if (transitionType == TransitionType.CALL) {
						// Search for the target under its predecessors
						final Set<Vertex<LETTER, STATE>> predecessors = mGameGraph.getPredecessors(searchVertex);
						if (predecessors != null && predecessors.contains(searchTarget)) {
							// If found, set the priority and abort the current
							// search
							searchSummarizeEdge.setPriority(searchDuplicatorChoice, searchPriority);
							continueSearch = false;
						}
					}
				}
			}

			// If search should be continued, add predecessors to the queue
			if (continueSearch) {
				final Set<Vertex<LETTER, STATE>> predecessors = mGameGraph.getPredecessors(searchVertex);
				if (predecessors != null) {
					for (final Vertex<LETTER, STATE> pred : predecessors) {
						// Reject predecessor if it is null
						if (pred == null) {
							continue;
						}
						if (pred instanceof DuplicatorNwaVertex) {
							// Predecessor is duplicator vertex
							final DuplicatorNwaVertex<LETTER, STATE> predAsDuplicatorNwa =
									(DuplicatorNwaVertex<LETTER, STATE>) pred;
							final TransitionType transitionType = predAsDuplicatorNwa.getTransitionType();
							if (transitionType == TransitionType.RETURN || transitionType == TransitionType.SINK
									|| transitionType == TransitionType.SUMMARIZE_ENTRY) {
								// Ignore return and special edges
								continue;
							} else if (transitionType == TransitionType.SUMMARIZE_EXIT) {
								// Follow summarize edge to the source and use
								// this vertex
								final Vertex<LETTER, STATE> source = predAsDuplicatorNwa.getSummarizeEdge().getSource();
								searchQueue.add(new SearchElement<>(source, searchTarget, searchVertex,
										searchSummarizeEdge, searchDuplicatorChoice, searchOrigin));
							} else {
								// Create a search element
								searchQueue.add(new SearchElement<>(pred, searchTarget, searchVertex,
										searchSummarizeEdge, searchDuplicatorChoice, searchOrigin));
							}
						} else {
							// Predecessor is spoiler vertex
							if (isSearchVertexDuplicatorNwa) {
								final TransitionType transitionType = searchVertexAsDuplicatorNwa.getTransitionType();
								if (transitionType == TransitionType.RETURN || transitionType == TransitionType.SINK
										|| transitionType == TransitionType.SUMMARIZE_ENTRY
										|| transitionType == TransitionType.SUMMARIZE_EXIT) {
									// Ignore return and special edges
									break;
								}
								// Create a search element
								searchQueue.add(new SearchElement<>(pred, searchTarget, searchVertex,
										searchSummarizeEdge, searchDuplicatorChoice, searchOrigin));
							}
						}
						// If operation was canceled, for example from the
						// Ultimate framework
						if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
							mLogger.debug("Stopped in computeSummarizeEdgePriorties/predecessors");
							throw new AutomataOperationCanceledException(this.getClass());
						}
					}
				}
			}
		}
	}

	/**
	 * Generates a possible reduced nwa automaton by using the current state of the game graph that may hold
	 * information, usable for reduction, generated by an {@link ASimulation}.
	 *
	 * @param useFinalStateConstraints
	 *            true iff accepting states should not be merged with non-accepting states
	 * @return A possible reduced nwa automaton
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate framework.
	 */
	public INestedWordAutomaton<LETTER, STATE> generateAutomatonFromGraph(final boolean useFinalStateConstraints)
			throws AutomataOperationCanceledException {
		// At this point we may validate the correctness of the simulation
		// results
		assert (NwaSimulationUtil.areNwaSimulationResultsCorrect(mGameGraph, mNwa, mSimulationType,
				new NwaSimulationUtil.BinaryRelationPredicateFromPartition<>(mPossibleEquivalenceClasses),
				mLogger)) : "The computed simulation results are incorrect.";

		final FairGameGraph<LETTER, STATE> fairGraph = castGraphToFairGameGraph();

		// By default, we assume that there are merge-able states.
		final boolean areThereMergeableStates = true;
		// By default, we assume that there are no remove-able transitions.
		// Since only fair simulation is capable of such.
		boolean areThereRemoveableTransitions = false;
		List<Triple<STATE, LETTER, STATE>> transitionsToRemove = null;
		if (fairGraph != null) {
			// For fair simulation, we know which transitions
			// need to be removed.
			transitionsToRemove = fairGraph.getTransitionsToRemove();
			areThereRemoveableTransitions = transitionsToRemove != null && !transitionsToRemove.isEmpty();
		}

		// TODO Christian 2017-01-27 somehow need a state factory here
		final IMinimizationStateFactory<STATE> stateFactory = (IMinimizationStateFactory<STATE>) mNwa.getStateFactory();
		INestedWordAutomaton<LETTER, STATE> result = null;

		// Merge states
		if (areThereMergeableStates) {
			// Equivalence class that holds all state classes
			// with their representatives
			UnionFind<STATE> equivalenceClasses;

			// For other simulation types, we set it up now.
			// Determine which states to merge
			equivalenceClasses = new UnionFind<>();
			for (final STATE state : mNwa.getStates()) {
				equivalenceClasses.makeEquivalenceClass(state);
			}
			// A pair q0, q1 is similar (regarding matched return words) if
			// q1 simulates q0.
			final HashRelation<STATE, STATE> similarStates = new HashRelation<>();
			for (final SpoilerVertex<LETTER, STATE> v : mGameGraph.getSpoilerVertices()) {

				// All the states we need are from Spoiler
				boolean considerVertex = true;
				final STATE state1 = v.getQ0();
				final STATE state2 = v.getQ1();

				// Ignore special cases
				if (state1 == null || state2 == null) {
					continue;
				}

				// For delayed simulation we need to choose between the
				// vertex with bit set to true or false
				if (mSimulationType == SimulationOrMinimizationType.DELAYED) {
					if (v.isB()) {
						considerVertex = mNwa.isFinal(state1) && !mNwa.isFinal(state2);
					} else {
						considerVertex = !mNwa.isFinal(state1) || mNwa.isFinal(state2);
					}
				}
				if (considerVertex) {
					if (v.getPM(null, mGameGraph.getGlobalInfinity()) < mGameGraph.getGlobalInfinity()) {
						similarStates.addPair(state1, state2);
					}
				}
			}
			// Mark states for merge if they simulate each other
			for (final STATE state1 : similarStates.getDomain()) {
				for (final STATE state2 : similarStates.getImage(state1)) {
					// Only merge if simulation holds in both directions and
					// we did not exclude the pair from merge
					if (similarStates.containsPair(state2, state1)) {
						equivalenceClasses.union(state1, state2);
					}
				}
			}

			if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
				mLogger.debug("Stopped in generateBuchiAutomatonFromGraph/equivalenceClasses");
				throw new AutomataOperationCanceledException(this.getClass());
			}

			final Collection<Set<STATE>> equivalenceClassesAsCollection = equivalenceClasses.getAllEquivalenceClasses();
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("Offering the following merges for MaxSat: " + equivalenceClassesAsCollection);
			}

			// Use a Max-Sat-Solver that minimizes the automaton based on
			// our simulation results
			mSimulationPerformance.startTimeMeasure(TimeMeasure.SOLVE_MAX_SAT);
			final BiPredicate<STATE, STATE> finalNonfinalConstraint = useFinalStateConstraints
					? new MinimizeNwaMaxSat2.TrueBiPredicate<>()
					: new MinimizeNwaMaxSat2.RelationBackedBiPredicate<>(new HashRelationBackedSetOfPairs<>());
			final MinimizeNwaPmaxSat<LETTER, STATE> minimizer = new MinimizeNwaPmaxSatDirect<>(mServices, stateFactory, mNwa,
					new PartitionBackedSetOfPairs<>(equivalenceClassesAsCollection),
					new MinimizeNwaMaxSat2.Settings<STATE>()
							.setFinalNonfinalConstraintPredicate(finalNonfinalConstraint));
			mSimulationPerformance.stopTimeMeasure(TimeMeasure.SOLVE_MAX_SAT);
			result = new RemoveUnreachable<>(mServices, minimizer.getResult()).getResult();
		} else {
			// If there are no merge-able states simply
			// copy the inputed automaton
			final NestedWordAutomaton<LETTER, STATE> resultAsChangeableAutomaton = new NestedWordAutomaton<>(mServices,
					mNwa.getVpAlphabet(), stateFactory);
			for (final STATE state : mNwa.getStates()) {
				// Copy states
				final boolean isInitial = mNwa.isInitial(state);
				final boolean isFinal = mNwa.isFinal(state);
				resultAsChangeableAutomaton.addState(isInitial, isFinal, state);

				// Copy transitions
				for (final OutgoingInternalTransition<LETTER, STATE> internalTrans : mNwa.internalSuccessors(state)) {
					resultAsChangeableAutomaton.addInternalTransition(state, internalTrans.getLetter(),
							internalTrans.getSucc());
				}
				for (final OutgoingCallTransition<LETTER, STATE> callTrans : mNwa.callSuccessors(state)) {
					resultAsChangeableAutomaton.addCallTransition(state, callTrans.getLetter(), callTrans.getSucc());
				}
				for (final OutgoingReturnTransition<LETTER, STATE> returnTrans : mNwa.returnSuccessors(state)) {
					resultAsChangeableAutomaton.addReturnTransition(state, returnTrans.getHierPred(),
							returnTrans.getLetter(), returnTrans.getSucc());
				}

				if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
					mLogger.debug("Stopped in generateBuchiAutomatonFromGraph/copying");
					throw new AutomataOperationCanceledException(this.getClass());
				}
			}
			result = resultAsChangeableAutomaton;
		}

		// If operation was canceled, for example from the
		// Ultimate framework
		if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
			mLogger.debug("Stopped in generateBuchiAutomatonFromGraph/states and transitions added");
			throw new AutomataOperationCanceledException(this.getClass());
		}

		// Remove unreachable states which can occur due to transition removal
		if (areThereRemoveableTransitions) {
			final INestedWordAutomaton<LETTER, STATE> nwaReachableStates =
					new RemoveUnreachable<>(mServices, result).getResult();
			return nwaReachableStates;
		}
		return result;
	}

	/**
	 * Generates the game graph out of an original nwa automaton. The graph represents a game, see {@link AGameGraph}.
	 *
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate framework.
	 */
	public void generateGameGraphFromAutomaton() throws AutomataOperationCanceledException {
		mSimulationPerformance.startTimeMeasure(TimeMeasure.BUILD_GRAPH);

		generateGraphBase();
		patchGraph();

		mSimulationPerformance.startTimeMeasure(TimeMeasure.GENERATE_SUMMARIZE_EDGES);
		generateSummarizeEdges();
		mSimulationPerformance.stopTimeMeasure(TimeMeasure.GENERATE_SUMMARIZE_EDGES);

		mSimulationPerformance.startTimeMeasure(TimeMeasure.COMPUTE_SUMMARIZE_EDGE_PRIORITIES);
		computeSummarizeEdgePriorities();
		mSimulationPerformance.stopTimeMeasure(TimeMeasure.COMPUTE_SUMMARIZE_EDGE_PRIORITIES);

		clear();

		mSimulationPerformance.stopTimeMeasure(TimeMeasure.BUILD_GRAPH);
	}

	/**
	 * Generates the vertices and regular of the game graph from the input automaton.
	 *
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate framework.
	 */
	public void generateGraphBase() throws AutomataOperationCanceledException {
		mLogger.debug("Generating graph base.");
		final int duplicatorPriority = DUPLICATOR_PRIORITY;

		// We generate the graph on the fly by starting with all initial
		// reachable states first
		final Queue<Vertex<LETTER, STATE>> workingList = new LinkedList<>();
		for (final Set<STATE> possibleEquivalenceClass : mPossibleEquivalenceClasses) {
			for (final STATE leftState : possibleEquivalenceClass) {
				for (final STATE rightState : possibleEquivalenceClass) {
					// Generate initial Spoiler vertices (leftState, rightState)
					final int priority = calculatePriority(leftState, rightState);

					// In delayed simulation we always generate the vertex with
					// priority zero. Conditionally we also add a vertex with
					// priority one.
					if (mSimulationType == SimulationOrMinimizationType.DELAYED) {
						final Vertex<LETTER, STATE> initialVertex =
								addSpoilerVertexHelper(0, false, leftState, rightState);
						if (initialVertex != null) {
							workingList.add(initialVertex);
						}
					} else {
						final Vertex<LETTER, STATE> initialVertex =
								addSpoilerVertexHelper(priority, false, leftState, rightState);
						if (initialVertex != null) {
							workingList.add(initialVertex);
						}
					}

					// In delayed simulation we may also add a vertex with
					// priority one that has the bit set to true.
					if (mSimulationType == SimulationOrMinimizationType.DELAYED) {
						if (priority == 1) {
							final Vertex<LETTER, STATE> initialVertex =
									addSpoilerVertexHelper(1, true, leftState, rightState);
							if (initialVertex != null) {
								workingList.add(initialVertex);
							}
						}
					}

					// If operation was canceled, for example from the
					// Ultimate framework
					if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
						mLogger.debug("Stopped in generateGameGraphFromAutomaton/generating initial vertices");
						throw new AutomataOperationCanceledException(this.getClass());
					}
				}
			}
		}

		// Next we process the queue until all reachable vertices of the game
		// graph are generated
		while (!workingList.isEmpty()) {
			final Vertex<LETTER, STATE> workingVertex = workingList.poll();
			// If the vertex already has successors then we already processed it
			if (mGameGraph.hasSuccessors(workingVertex)) {
				continue;
			}
			if (workingVertex instanceof SpoilerNwaVertex<?, ?>) {
				// Working with a Spoiler vertex
				final SpoilerNwaVertex<LETTER, STATE> spoilerVertex = (SpoilerNwaVertex<LETTER, STATE>) workingVertex;
				final STATE leftState = spoilerVertex.getQ0();
				final STATE rightState = spoilerVertex.getQ1();

				// Vertices and edges generated by internal transitions
				for (final OutgoingInternalTransition<LETTER, STATE> trans : mNwa.internalSuccessors(leftState)) {
					boolean bitForDestination = spoilerVertex.isB();

					final STATE edgeDest = trans.getSucc();
					final LETTER letter = trans.getLetter();

					// Spoiler edges q0 -a-> q2 : (q0, q1) -> (q2, q1, a)
					final Vertex<LETTER, STATE> spoilerSrc = spoilerVertex;

					// In delayed simulation the destination needs to have
					// the bit set to true if Spoilers destination is final,
					// else we use the same as the source has.
					if (mSimulationType == SimulationOrMinimizationType.DELAYED && mNwa.isFinal(edgeDest)) {
						bitForDestination = true;
					}
					Vertex<LETTER, STATE> duplicatorDest = getDuplicatorVertex(edgeDest, rightState, letter,
							bitForDestination, TransitionType.INTERNAL, null, null);
					// Generate Duplicator vertices (q2, q1, a) if not existent
					if (duplicatorDest == null) {
						duplicatorDest = addDuplicatorVertexHelper(duplicatorPriority, bitForDestination, edgeDest,
								rightState, letter, TransitionType.INTERNAL);
						if (duplicatorDest != null) {
							workingList.add(duplicatorDest);
						}
					}

					// Add the edge
					if (duplicatorDest != null) {
						addEdge(spoilerSrc, duplicatorDest);
					}

					// If operation was canceled, for example from the
					// Ultimate framework
					if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
						mLogger.debug("Stopped in generateGameGraphFromAutomaton/generating spoiler internal edges");
						throw new AutomataOperationCanceledException(this.getClass());
					}
				}

				// Vertices and edges generated by call transitions
				for (final OutgoingCallTransition<LETTER, STATE> trans : mNwa.callSuccessors(leftState)) {
					boolean bitForDestination = spoilerVertex.isB();

					final STATE edgeDest = trans.getSucc();
					final LETTER letter = trans.getLetter();

					// Spoiler edges q0 -c-> q2 : (q0, q1) -> (q2, q1, c)
					final Vertex<LETTER, STATE> spoilerSrc = spoilerVertex;

					// In delayed simulation the destination needs to have
					// the bit set to true if Spoilers destination is final,
					// else we use the same as the source has.
					if (mSimulationType == SimulationOrMinimizationType.DELAYED && mNwa.isFinal(edgeDest)) {
						bitForDestination = true;
					}
					Vertex<LETTER, STATE> duplicatorDest = getDuplicatorVertex(edgeDest, rightState, letter,
							bitForDestination, TransitionType.CALL, null, null);
					// Generate Duplicator vertices (q2, q1, c) if not existent
					if (duplicatorDest == null) {
						duplicatorDest = addDuplicatorVertexHelper(duplicatorPriority, bitForDestination, edgeDest,
								rightState, letter, TransitionType.CALL);
						if (duplicatorDest != null) {
							workingList.add(duplicatorDest);
						}
					}

					// Add the edge
					if (duplicatorDest != null) {
						addEdge(spoilerSrc, duplicatorDest);
					}

					// If operation was canceled, for example from the
					// Ultimate framework
					if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
						mLogger.debug("Stopped in generateGameGraphFromAutomaton/generating spoiler call edges");
						throw new AutomataOperationCanceledException(this.getClass());
					}
				}

				// Vertices and edges generated by return transitions
				for (final OutgoingReturnTransition<LETTER, STATE> trans : mNwa.returnSuccessors(leftState)) {
					boolean bitForDestination = spoilerVertex.isB();

					final STATE edgeDest = trans.getSucc();
					final LETTER letter = trans.getLetter();

					// Spoiler edges q0 -r/q3-> q2 : (q0, q1) -> (q2, q1, r/q3)
					final Vertex<LETTER, STATE> spoilerSrc = spoilerVertex;

					// In delayed simulation the destination needs to have
					// the bit set to true if Spoilers destination is final,
					// else we use the same as the source has.
					if (mSimulationType == SimulationOrMinimizationType.DELAYED && mNwa.isFinal(edgeDest)) {
						bitForDestination = true;
					}
					Vertex<LETTER, STATE> duplicatorDest = getDuplicatorVertex(edgeDest, rightState, letter,
							bitForDestination, TransitionType.RETURN, null, null);
					// Generate Duplicator vertices (q2, q1, r) if not existent
					if (duplicatorDest == null) {
						duplicatorDest = addDuplicatorVertexHelper(duplicatorPriority, bitForDestination, edgeDest,
								rightState, letter, TransitionType.RETURN);
						if (duplicatorDest != null) {
							workingList.add(duplicatorDest);
						}
					}

					// Add the edge
					if (duplicatorDest != null) {
						addEdge(spoilerSrc, duplicatorDest);
					}

					// If operation was canceled, for example from the
					// Ultimate framework
					if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
						mLogger.debug("Stopped in generateGameGraphFromAutomaton/generating spoiler return edges");
						throw new AutomataOperationCanceledException(this.getClass());
					}
				}
			} else if (workingVertex instanceof DuplicatorNwaVertex<?, ?>) {
				// Working with a Duplicator vertex
				final DuplicatorNwaVertex<LETTER, STATE> duplicatorVertex =
						(DuplicatorNwaVertex<LETTER, STATE>) workingVertex;
				final STATE leftState = duplicatorVertex.getQ0();
				final STATE rightState = duplicatorVertex.getQ1();
				final LETTER letter = duplicatorVertex.getLetter();
				final TransitionType transType = duplicatorVertex.getTransitionType();

				// Vertices and edges generated by internal transitions
				if (transType == TransitionType.INTERNAL) {
					for (final OutgoingInternalTransition<LETTER, STATE> trans : mNwa.internalSuccessors(rightState,
							letter)) {
						boolean bitForDestination = duplicatorVertex.isB();

						final STATE edgeDest = trans.getSucc();

						// Duplicator edges q1 -a-> q2 : (q0, q1, a) -> (q0, q2)
						final Vertex<LETTER, STATE> duplicatorSrc = duplicatorVertex;

						// In delayed simulation the destination needs to have
						// the bit set to false if Duplicators destination
						// is final
						if (mSimulationType == SimulationOrMinimizationType.DELAYED && mNwa.isFinal(edgeDest)) {
							bitForDestination = false;
						}
						Vertex<LETTER, STATE> spoilerDest =
								getSpoilerVertex(leftState, edgeDest, bitForDestination, null, null);
						if (spoilerDest == null) {
							if (mRestrictGraphToInitPart) {
								// If Spoiler vertex is not existent at this
								// point, then it is non-simulating since its
								// states are in different equivalence classes.
								// Spoiler wins if going to this vertex, so we
								// add a SpoilerWinningSink
								addSpoilerWinningSink(duplicatorVertex);
							} else {
								// Generate Spoiler vertices (q0, q2) if not
								// existent
								final int priority = calculatePriority(leftState, edgeDest);
								spoilerDest = addSpoilerVertexHelper(priority, bitForDestination, leftState, edgeDest);
								if (spoilerDest != null) {
									workingList.add(spoilerDest);
								}
							}
						}

						// Add the edge
						if (spoilerDest != null) {
							addEdge(duplicatorSrc, spoilerDest);
						}

						// If operation was canceled, for example from the
						// Ultimate framework
						if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
							mLogger.debug(
									"Stopped in generateGameGraphFromAutomaton/generating duplicator internal edges");
							throw new AutomataOperationCanceledException(this.getClass());
						}
					}
				}

				// Vertices and edges generated by call transitions
				if (transType == TransitionType.CALL) {
					for (final OutgoingCallTransition<LETTER, STATE> trans : mNwa.callSuccessors(rightState, letter)) {
						boolean bitForDestination = duplicatorVertex.isB();

						final STATE edgeDest = trans.getSucc();

						// Duplicator edges q1 -c-> q2 : (q0, q1, c) -> (q0, q2)
						final Vertex<LETTER, STATE> duplicatorSrc = duplicatorVertex;

						// In delayed simulation the destination needs to have
						// the bit set to false if Duplicators destination
						// is final
						if (mSimulationType == SimulationOrMinimizationType.DELAYED && mNwa.isFinal(edgeDest)) {
							bitForDestination = false;
						}
						Vertex<LETTER, STATE> spoilerDest =
								getSpoilerVertex(leftState, edgeDest, bitForDestination, null, null);
						if (spoilerDest == null) {
							if (mRestrictGraphToInitPart) {
								// If Spoiler vertex is not existent at this
								// point, then it is non-simulating since its
								// states are in different equivalence classes.
								// Spoiler wins if going to this vertex, so we
								// add a SpoilerWinningSink
								addSpoilerWinningSink(duplicatorVertex);
							} else {
								// Generate Spoiler vertices (q0, q2) if not
								// existent
								final int priority = calculatePriority(leftState, edgeDest);
								spoilerDest = addSpoilerVertexHelper(priority, bitForDestination, leftState, edgeDest);
								if (spoilerDest != null) {
									workingList.add(spoilerDest);
								}
							}
						}

						// Add the edge
						if (spoilerDest != null) {
							addEdge(duplicatorSrc, spoilerDest);
						}

						// If operation was canceled, for example from the
						// Ultimate framework
						if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
							mLogger.debug("Stopped in generateGameGraphFromAutomaton/generating duplicator call edges");
							throw new AutomataOperationCanceledException(this.getClass());
						}
					}
				}

				// Vertices and edges generated by return transitions
				if (transType == TransitionType.RETURN) {
					for (final OutgoingReturnTransition<LETTER, STATE> trans : mNwa.returnSuccessors(rightState,
							letter)) {
						boolean bitForDestination = duplicatorVertex.isB();

						final STATE edgeDest = trans.getSucc();

						// Duplicator edges q1 -r/q3-> q2 : (q0, q1, r/q3) ->
						// (q0, q2)
						final Vertex<LETTER, STATE> duplicatorSrc = duplicatorVertex;

						// In delayed simulation the destination needs to have
						// the bit set to false if Duplicators destination
						// is final
						if (mSimulationType == SimulationOrMinimizationType.DELAYED && mNwa.isFinal(edgeDest)) {
							bitForDestination = false;
						}
						Vertex<LETTER, STATE> spoilerDest =
								getSpoilerVertex(leftState, edgeDest, bitForDestination, null, null);
						if (spoilerDest == null) {
							if (mRestrictGraphToInitPart) {
								// If Spoiler vertex is not existent at this
								// point, then it is non-simulating since its
								// states are in different equivalence classes.
								// Spoiler wins if going to this vertex, so we
								// add a SpoilerWinningSink
								addSpoilerWinningSink(duplicatorVertex);
							} else {
								// Generate Spoiler vertices (q0, q2) if not
								// existent
								final int priority = calculatePriority(leftState, edgeDest);
								spoilerDest = addSpoilerVertexHelper(priority, bitForDestination, leftState, edgeDest);
								if (spoilerDest != null) {
									workingList.add(spoilerDest);
								}
							}
						}

						// Add the edge
						if (spoilerDest != null) {
							addEdge(duplicatorSrc, spoilerDest);
						}

						// If operation was canceled, for example from the
						// Ultimate framework
						if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
							mLogger.debug(
									"Stopped in generateGameGraphFromAutomaton/generating duplicator return edges");
							throw new AutomataOperationCanceledException(this.getClass());
						}
					}
				}
			}
		}

		// Increase by one, global infinity is amount of priority one + 1
		mGameGraph.increaseGlobalInfinity();
	}

	/**
	 * Generates the regular edges of the game graph from the input automaton.
	 *
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate framework.
	 * @deprecated The operation does not support the usage of an initial partition, use {@link #generateGraphBase()}
	 *             instead.
	 */
	@Deprecated
	public void generateRegularEdges() throws AutomataOperationCanceledException {
		mLogger.debug("Generating regular edges.");
		for (final STATE edgeDest : mNwa.getStates()) {
			// Edges generated by internal transitions
			for (final IncomingInternalTransition<LETTER, STATE> trans : mNwa.internalPredecessors(edgeDest)) {
				for (final STATE fixState : mNwa.getStates()) {
					// Duplicator edges q1 -a-> q2 : (x, q1, a) -> (x, q2)
					Vertex<LETTER, STATE> duplicatorSrc = getDuplicatorVertex(fixState, trans.getPred(),
							trans.getLetter(), false, TransitionType.INTERNAL, null, null);
					Vertex<LETTER, STATE> spoilerDest = getSpoilerVertex(fixState, edgeDest, false, null, null);
					if (duplicatorSrc != null && spoilerDest != null) {
						addEdge(duplicatorSrc, spoilerDest);
					}

					// For delayed simulation we also need to account for
					// source vertices with the bit set to true
					if (mSimulationType == SimulationOrMinimizationType.DELAYED) {
						duplicatorSrc = getDuplicatorVertex(fixState, trans.getPred(), trans.getLetter(), true,
								TransitionType.INTERNAL, null, null);
						spoilerDest = getSpoilerVertex(fixState, edgeDest, true, null, null);
						if (duplicatorSrc != null) {
							// The destination needs to have
							// the bit set to false if Duplicators destination
							// is final
							if (mNwa.isFinal(edgeDest)) {
								spoilerDest = getSpoilerVertex(fixState, edgeDest, false, null, null);
							}
							if (spoilerDest != null) {
								addEdge(duplicatorSrc, spoilerDest);
							}
						}
					}

					// Spoiler edges q1 -a-> q2 : (q1, x) -> (q2, x, a)
					Vertex<LETTER, STATE> spoilerSrc = getSpoilerVertex(trans.getPred(), fixState, false, null, null);
					Vertex<LETTER, STATE> duplicatorDest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(),
							false, TransitionType.INTERNAL, null, null);
					if (spoilerSrc != null) {
						// In delayed simulation the destination needs to have
						// the bit set to true if Spoilers destination is final
						if (mSimulationType == SimulationOrMinimizationType.DELAYED && mNwa.isFinal(edgeDest)) {
							duplicatorDest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), true,
									TransitionType.INTERNAL, null, null);
						}
						if (duplicatorDest != null) {
							addEdge(spoilerSrc, duplicatorDest);
						}
					}

					// For delayed simulation we also need to account for
					// source vertices with the bit set to true
					if (mSimulationType == SimulationOrMinimizationType.DELAYED) {
						spoilerSrc = getSpoilerVertex(trans.getPred(), fixState, true, null, null);
						duplicatorDest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), true,
								TransitionType.INTERNAL, null, null);
						// If the Spoiler source does exist, we connect it
						if (spoilerSrc != null && duplicatorDest != null) {
							addEdge(spoilerSrc, duplicatorDest);
						}
					}

					// If operation was canceled, for example from the
					// Ultimate framework
					if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
						mLogger.debug("Stopped in generateGameGraphFromAutomaton/generating internal edges");
						throw new AutomataOperationCanceledException(this.getClass());
					}
				}

				// Add the processed transition to the internal field, if using
				// fair simulation
				addAutomatonTransitionToInternalField(new Triple<>(trans.getPred(), trans.getLetter(), edgeDest));
			}

			// Edges generated by call transitions
			for (final IncomingCallTransition<LETTER, STATE> trans : mNwa.callPredecessors(edgeDest)) {
				// Calling is possible regardless of the stack
				for (final STATE fixState : mNwa.getStates()) {
					// Duplicator edges q1 -c-> q2 : (x, q1, c) -> (x, q2)
					Vertex<LETTER, STATE> duplicatorSrc = getDuplicatorVertex(fixState, trans.getPred(),
							trans.getLetter(), false, TransitionType.CALL, null, null);
					Vertex<LETTER, STATE> spoilerDest = getSpoilerVertex(fixState, edgeDest, false, null, null);
					if (duplicatorSrc != null && spoilerDest != null) {
						addEdge(duplicatorSrc, spoilerDest);
					}

					// For delayed simulation we also need to account for
					// source vertices with the bit set to true
					if (mSimulationType == SimulationOrMinimizationType.DELAYED) {
						duplicatorSrc = getDuplicatorVertex(fixState, trans.getPred(), trans.getLetter(), true,
								TransitionType.CALL, null, null);
						spoilerDest = getSpoilerVertex(fixState, edgeDest, true, null, null);
						if (duplicatorSrc != null) {
							// The destination needs to have the bit set to
							// false if Duplicators destination is final
							if (mNwa.isFinal(edgeDest)) {
								spoilerDest = getSpoilerVertex(fixState, edgeDest, false, null, null);
							}
							if (spoilerDest != null) {
								addEdge(duplicatorSrc, spoilerDest);
							}
						}
					}

					// Spoiler edges q1 -c-> q2 : (q1, x) -> (q2, x, c)
					Vertex<LETTER, STATE> spoilerSrc = getSpoilerVertex(trans.getPred(), fixState, false, null, null);
					Vertex<LETTER, STATE> duplicatorDest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(),
							false, TransitionType.CALL, null, null);
					if (spoilerSrc != null) {
						// In delayed simulation the destination needs to have
						// the bit set to true if Spoilers destination is final
						if (mSimulationType == SimulationOrMinimizationType.DELAYED && mNwa.isFinal(edgeDest)) {
							duplicatorDest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), true,
									TransitionType.CALL, null, null);
						}
						if (duplicatorDest != null) {
							addEdge(spoilerSrc, duplicatorDest);
						}
					}

					// For delayed simulation we also need to account for
					// source vertices with the bit set to true
					if (mSimulationType == SimulationOrMinimizationType.DELAYED) {
						spoilerSrc = getSpoilerVertex(trans.getPred(), fixState, true, null, null);
						duplicatorDest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), true,
								TransitionType.CALL, null, null);
						// If the Spoiler source does exist, we connect it
						if (spoilerSrc != null && duplicatorDest != null) {
							addEdge(spoilerSrc, duplicatorDest);
						}
					}

					// If operation was canceled, for example from the
					// Ultimate framework
					if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
						mLogger.debug("Stopped in generateGameGraphFromAutomaton/generating call edges");
						throw new AutomataOperationCanceledException(this.getClass());
					}
				}

				// TODO Find a way that buechi transitions support nwa
				// transitions, call and return with hierPred
				// getBuechiTransitions().add(new Triple<>(trans.getPred(),
				// trans.getLetter(), edgeDest));
			}

			// Edges generated by return transitions
			for (final IncomingReturnTransition<LETTER, STATE> trans : mNwa.returnPredecessors(edgeDest)) {
				for (final STATE fixState : mNwa.getStates()) {
					// Duplicator edges q1 -r/q0-> q2 : (x, q1, r/q0) -> (x, q2)
					Vertex<LETTER, STATE> duplicatorSrc = getDuplicatorVertex(fixState, trans.getLinPred(),
							trans.getLetter(), false, TransitionType.RETURN, null, null);
					Vertex<LETTER, STATE> spoilerDest = getSpoilerVertex(fixState, edgeDest, false, null, null);
					if (duplicatorSrc != null && spoilerDest != null) {
						addEdge(duplicatorSrc, spoilerDest);
					}

					// For delayed simulation we also need to account for
					// source vertices with the bit set to true
					if (mSimulationType == SimulationOrMinimizationType.DELAYED) {
						duplicatorSrc = getDuplicatorVertex(fixState, trans.getLinPred(), trans.getLetter(), true,
								TransitionType.RETURN, null, null);
						spoilerDest = getSpoilerVertex(fixState, edgeDest, true, null, null);
						if (duplicatorSrc != null) {
							// The destination needs to have the bit set to
							// false if Duplicators destination is final
							if (mNwa.isFinal(edgeDest)) {
								spoilerDest = getSpoilerVertex(fixState, edgeDest, false, null, null);
							}
							if (spoilerDest != null) {
								addEdge(duplicatorSrc, spoilerDest);
							}
						}
					}

					// Spoiler edges q1 -r/q0-> q2 : (q1, x) -> (q2, x, r/q0)
					Vertex<LETTER, STATE> spoilerSrc =
							getSpoilerVertex(trans.getLinPred(), fixState, false, null, null);
					Vertex<LETTER, STATE> duplicatorDest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(),
							false, TransitionType.RETURN, null, null);
					if (spoilerSrc != null) {
						// In delayed simulation the destination needs to have
						// the bit set to true if Spoilers destination is final
						if (mSimulationType == SimulationOrMinimizationType.DELAYED && mNwa.isFinal(edgeDest)) {
							duplicatorDest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), true,
									TransitionType.RETURN, null, null);
						}
						if (duplicatorDest != null) {
							addEdge(spoilerSrc, duplicatorDest);
						}
					}

					// For delayed simulation we also need to account for
					// vertices with the bit set to true
					if (mSimulationType == SimulationOrMinimizationType.DELAYED) {
						spoilerSrc = getSpoilerVertex(trans.getLinPred(), fixState, true, null, null);
						duplicatorDest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), true,
								TransitionType.RETURN, null, null);
						// If the Spoiler source does exist, we connect it
						if (spoilerSrc != null && duplicatorDest != null) {
							addEdge(spoilerSrc, duplicatorDest);
						}
					}

					// If operation was canceled, for example from the
					// Ultimate framework
					if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
						mLogger.debug("Stopped in generateGameGraphFromAutomaton/generating return edges");
						throw new AutomataOperationCanceledException(this.getClass());
					}
				}

				// TODO Find a way that buechi transitions support nwa
				// transitions, call and return with hierPred
				// getBuechiTransitions().add(new Triple<>(trans.getPred(),
				// trans.getLetter(), edgeDest));
			}
		}
	}

	/**
	 * Generates the summarize edges of the game graph from the input automaton.
	 *
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate framework.
	 */
	public void generateSummarizeEdges() throws AutomataOperationCanceledException {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Generating summarize edges.");
		}
		// Create the game automaton, we will use it for summarize computation
		final INwaOutgoingLetterAndTransitionProvider<IGameLetter<LETTER, STATE>, IGameState> gameAutomaton = createGameAutomaton();
		final NestedWordAutomatonReachableStates<IGameLetter<LETTER, STATE>, IGameState> gameAutomatonWithSummaries =
				new RemoveUnreachable<>(mServices, gameAutomaton).getResult();

		final boolean backwardSummaryComputation = false;
		if (backwardSummaryComputation) {
			final SummaryComputation<LETTER, STATE> sc =
					new SummaryComputation<>(mServices, gameAutomatonWithSummaries, mNwa);
			for (final IGameState gameState : sc.getNeedSpoilerWinningSink()) {
				final SpoilerNwaVertex<LETTER, STATE> src =
						((GameSpoilerNwaVertex<LETTER, STATE>) gameState).getSpoilerNwaVertex();
				addSpoilerWinningSinkExtended(src);
			}

			for (final GameCallReturnSummary<STATE> game : sc.getGameSummaries()) {
				if (sc.getNeedSpoilerWinningSink().contains(game.getSummarySource())) {
					// we already added a winning sink,
					// no need to add another summary
					continue;
				}

				final SpoilerNwaVertex<LETTER, STATE> src =
						((GameSpoilerNwaVertex<LETTER, STATE>) game.getSummarySource()).getSpoilerNwaVertex();
				final STATE spoilerChoice = game.getSpoilerDestinationState();
				final Set<Pair<STATE, Boolean>> duplicatorChoices = new HashSet<>();
				final Map<Pair<STATE, Boolean>, Integer> duplicatorChoice2Priority = new HashMap<>();
				for (final Entry<IGameState, Integer> entry : game.getDuplicatorResponses().entrySet()) {
					final SpoilerNwaVertex<LETTER, STATE> duplicatorChoice =
							((GameSpoilerNwaVertex<LETTER, STATE>) entry.getKey()).getSpoilerNwaVertex();
					duplicatorChoices.add(new Pair<>(duplicatorChoice.getQ1(), duplicatorChoice.isB()));
					duplicatorChoice2Priority.put(new Pair<>(duplicatorChoice.getQ1(), duplicatorChoice.isB()),
							entry.getValue());
				}
				addSummarizeEdge(src, spoilerChoice, duplicatorChoices);
				final SummarizeEdge<LETTER, STATE> summaryEdge =
						mSrcDestToSummarizeEdges.get(src, new Pair<>(spoilerChoice, duplicatorChoices));
				for (final Entry<Pair<STATE, Boolean>, Integer> entry : duplicatorChoice2Priority.entrySet()) {
					summaryEdge.setPriority(entry.getKey(), entry.getValue());
				}

			}
		} else {

			// Retrieve all single summary edge sources
			final Set<IGameState> summarySources = new HashSet<>();
			for (final SpoilerVertex<LETTER, STATE> spoilerVertex : mGameGraph.getSpoilerVertices()) {
				if (!(spoilerVertex instanceof SpoilerNwaVertex<?, ?>)) {
					continue;
				}
				final SpoilerNwaVertex<LETTER, STATE> spoilerNwaVertex =
						(SpoilerNwaVertex<LETTER, STATE>) spoilerVertex;
				final GameSpoilerNwaVertex<LETTER, STATE> gameNwaVertex = new GameSpoilerNwaVertex<>(spoilerNwaVertex);

				final Iterable<SummaryReturnTransition<IGameLetter<LETTER, STATE>, IGameState>> summariesOfSource =
						gameAutomatonWithSummaries.summarySuccessors(gameNwaVertex);
				if (summariesOfSource.iterator().hasNext()) {
					summarySources.add(gameNwaVertex);
				}

				// If operation was canceled, for example from the
				// Ultimate framework
				if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
					mLogger.debug("Stopped in generateSummarizeEdges/all summary sources");
					throw new AutomataOperationCanceledException(this.getClass());
				}
			}
			// Retrieve the merged summary edges for the game graph that start
			// at the given source.
			// We make all summarySources the only initial game states and
			// determinize the automaton.
			// TODO Only enable this for testing purpose!
			// This test is extremely expensive.
			final boolean alreadyWasDeterministic =
					!new IsDeterministic<>(mServices, gameAutomatonWithSummaries).hasNondeterministicTransitions();
			if (alreadyWasDeterministic) {
				mSimulationPerformance.setCountingMeasure(CountingMeasure.ALREADY_WAS_DETERMINISTIC, 1);
			}

			final IDeterminizeStateFactory<IGameState> stateFactory =
					(IDeterminizeStateFactory<IGameState>) gameAutomatonWithSummaries.getStateFactory();
			// Determinizing is very expensive, it is the dominant part of the
			// whole algorithm
			final INwaOutgoingLetterAndTransitionProvider<IGameLetter<LETTER, STATE>, IGameState> determinizedGameAutomaton =
					new Determinize<>(mServices, stateFactory, gameAutomatonWithSummaries, summarySources).getResult();
			mSimulationPerformance.setCountingMeasure(CountingMeasure.DETERMINIZED_GAME_AUTOMATON_STATES,
					determinizedGameAutomaton.size());
			final NestedWordAutomatonReachableStates<IGameLetter<LETTER, STATE>, IGameState> gameAutomatonWithMergedSummaries =
					new RemoveUnreachable<>(mServices, determinizedGameAutomaton).getResult();
			final IGameState emptyStackState = gameAutomatonWithMergedSummaries.getEmptyStackState();

			// The initial game states are the source of
			// the summary edges we are interested in
			for (final IGameState mergedSummarySourceAsGameState : gameAutomatonWithMergedSummaries
					.getInitialStates()) {
				if (!(mergedSummarySourceAsGameState instanceof GameDoubleDeckerSet)) {
					throw new IllegalStateException(
							"Expected cast to be possible, something seems to be wrong with the game graph.");
				}
				final GameDoubleDeckerSet mergedSummarySourceDDSet =
						(GameDoubleDeckerSet) mergedSummarySourceAsGameState;

				// We are only interested in sources where the down state is the
				// empty stack symbol
				final Set<IGameState> mergedSummarySourceUpStates =
						mergedSummarySourceDDSet.getUpStates(emptyStackState);
				if (mergedSummarySourceUpStates.size() > 1) {
					throw new IllegalStateException(
							"Expected only one up state after determizing the game automaton at summary sources.");
				}
				final IGameState mergedSummarySourceUpStateAsGameState = mergedSummarySourceUpStates.iterator().next();
				if (!(mergedSummarySourceUpStateAsGameState instanceof GameSpoilerNwaVertex<?, ?>)) {
					throw new IllegalStateException(
							"Expected cast to be possible, something seems to be wrong with the game graph.");
				}
				@SuppressWarnings("unchecked")
				final SpoilerNwaVertex<LETTER, STATE> mergedSummarySource =
						((GameSpoilerNwaVertex<LETTER, STATE>) mergedSummarySourceUpStateAsGameState)
								.getSpoilerNwaVertex();

				final Map<STATE, Set<Pair<STATE, Boolean>>> spoilerToDuplicatorChoices = new HashMap<>();
				boolean hasSinkWinningForSpoiler = false;
				boolean hasSinkWinningForDuplicator = false;
				boolean runsInDuplicatorDeadEnd = false;
				// Collect all summarize edges
				for (final SummaryReturnTransition<IGameLetter<LETTER, STATE>, IGameState> summary : gameAutomatonWithMergedSummaries
						.summarySuccessors(mergedSummarySourceAsGameState)) {
					final IGameState summaryDestinationAsGameState = summary.getSucc();
					final GameDoubleDeckerSet summaryDestinationAsDD =
							(GameDoubleDeckerSet) summaryDestinationAsGameState;
					final Set<IGameState> summaryDestinationUpStates =
							summaryDestinationAsDD.getUpStates(emptyStackState);

					// If the destination up states are null, then the
					// destination
					// is empty. This is the case if the source is not total,
					// because Determinize makes the automaton total. We can
					// just
					// ignore this event and continue.
					if (summaryDestinationUpStates == null) {
						continue;
					}
					// If this summarize edge only points to one destination,
					// which
					// means Duplicator has no other possibility than this, and
					// it
					// is the auxiliary state, then Duplicator runs in a dead
					// end
					// and can not evade.
					if (summaryDestinationUpStates.size() == 1) {
						final IGameState summaryDestinationUpState = summaryDestinationUpStates.iterator().next();
						if (summaryDestinationUpState.equals(mAuxiliaryGameState)) {
							runsInDuplicatorDeadEnd = true;
							// Continue as there are no other destinations to
							// consider
							continue;
						}
					}
					for (final IGameState summaryDestinationUpState : summaryDestinationUpStates) {
						// If an up state represents Duplicator running in a
						// dead-end but there also are other up states,
						// Duplicator
						// will evade, thus ignoring this up state. If there
						// would
						// be no other up states, we would already have
						// continued
						// before.
						if (summaryDestinationUpState.equals(mAuxiliaryGameState)) {
							continue;
						}

						@SuppressWarnings("unchecked")
						final SpoilerNwaVertex<LETTER, STATE> summaryDestination =
								((GameSpoilerNwaVertex<LETTER, STATE>) summaryDestinationUpState).getSpoilerNwaVertex();
						// Add the summary to Duplicators choices for this
						// merged summary
						final IWinningSink<LETTER, STATE> sinkTarget = summaryDestination.getSink();
						if (sinkTarget == null) {
							// Target is no sink
							final STATE spoilerTarget = summaryDestination.getQ0();
							final STATE duplicatorTarget = summaryDestination.getQ1();
							final boolean bitTarget = summaryDestination.isB();
							if (!spoilerToDuplicatorChoices.containsKey(spoilerTarget)) {
								spoilerToDuplicatorChoices.put(spoilerTarget, new LinkedHashSet<>());
							}
							final Set<Pair<STATE, Boolean>> choices = spoilerToDuplicatorChoices.get(spoilerTarget);
							choices.add(new Pair<>(duplicatorTarget, bitTarget));
							spoilerToDuplicatorChoices.put(spoilerTarget, choices);
						} else {
							// Target is a sink, put it in a separate container
							if (sinkTarget.isWinningForSpoiler()) {
								hasSinkWinningForSpoiler = true;
							} else {
								hasSinkWinningForDuplicator = true;
							}
						}
					}

					// If operation was canceled, for example from the
					// Ultimate framework
					if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
						mLogger.debug("Stopped in generateSummarizeEdges/each summary");
						throw new AutomataOperationCanceledException(this.getClass());
					}
				}
				// Patch the source to a winning sink for Spoiler
				if (runsInDuplicatorDeadEnd) {
					addSpoilerWinningSinkExtended(mergedSummarySource);
				}
				// Create and add the merged summaries
				if (hasSinkWinningForSpoiler) {
					// If there is a winning sink for Spoiler, no other
					// summaries
					// are needed.
					addSpoilerWinningSinkExtended(mergedSummarySource);
				} else {
					for (final Entry<STATE, Set<Pair<STATE, Boolean>>> choiceEntry : spoilerToDuplicatorChoices
							.entrySet()) {
						final STATE spoilerChoice = choiceEntry.getKey();
						addSummarizeEdge(mergedSummarySource, spoilerChoice, choiceEntry.getValue());
					}
					// If no summarize edges where added, we are forced to add
					// the
					// winning sink for Duplicator, if it was present.
					if (spoilerToDuplicatorChoices.isEmpty() && hasSinkWinningForDuplicator) {
						addDuplicatorWinningSink(mergedSummarySource);
					}
				}
			}
		}

		// Delete all return vertices
		for (final DuplicatorNwaVertex<LETTER, STATE> returnVertex : mDuplicatorReturningVertices) {
			final Set<Vertex<LETTER, STATE>> successors = mGameGraph.getSuccessors(returnVertex);
			List<Vertex<LETTER, STATE>> successorsToProcess = null;
			if (successors != null) {
				// Care for concurrentModifcationException
				successorsToProcess = new LinkedList<>(successors);
				for (final Vertex<LETTER, STATE> succ : successorsToProcess) {
					mGameGraph.removeEdge(returnVertex, succ);
					mRemovedReturnBridges.removedEdge(returnVertex, succ);
				}
			}
			final Set<Vertex<LETTER, STATE>> predecessors = mGameGraph.getPredecessors(returnVertex);
			List<Vertex<LETTER, STATE>> predecessorsToProcess = null;
			if (predecessors != null) {
				// Care for concurrentModifcationException
				predecessorsToProcess = new LinkedList<>(predecessors);
				for (final Vertex<LETTER, STATE> pred : predecessorsToProcess) {
					mGameGraph.removeEdge(pred, returnVertex);
					mRemovedReturnBridges.removedEdge(pred, returnVertex);
					// Care for dead end spoiler vertices because they are not
					// allowed in a legal game graph.
					// They need to form a legal instant win for Duplicator.
					if (!mGameGraph.hasSuccessors(pred) && pred instanceof SpoilerNwaVertex<?, ?>) {
						final SpoilerNwaVertex<LETTER, STATE> predAsNwa = (SpoilerNwaVertex<LETTER, STATE>) pred;
						// If we are in delayed simulation and the bit is set to
						// true, Spoiler is winning
						if (mSimulationType.equals(SimulationOrMinimizationType.DELAYED) && predAsNwa.isB()) {
							// TODO We do not distinguish cases, we also
							// add a DuplicatorWinningSink. However, the exact
							// behavior needs to be verified.
							addDuplicatorWinningSink(predAsNwa);
							// addSpoilerWinningSinkExtended(predAsNwa);
						} else {
							addDuplicatorWinningSink(predAsNwa);
						}
					}
				}
			}
			// Remove not reachable vertex
			removeDuplicatorVertex(returnVertex);
			mRemovedReturnBridges.removedVertex(returnVertex);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("\tRemoved duplicatorReturn: " + returnVertex);
			}

			// Add push-over edges that are generated by the return vertex
			if (mUsePushOverEdges && successorsToProcess != null && predecessorsToProcess != null) {
				for (final Vertex<LETTER, STATE> succ : successorsToProcess) {
					for (final Vertex<LETTER, STATE> pred : predecessorsToProcess) {
						mGameGraph.addPushOverEdge(pred, succ);
						mRemovedReturnBridges.addedPushOverEdge(pred, succ);
						if (mLogger.isDebugEnabled()) {
							mLogger.debug("\tAdded pushOver: " + pred + " -> " + succ);
						}
					}
				}
			}

			// If operation was canceled, for example from the
			// Ultimate framework
			if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
				mLogger.debug("Stopped in generateSummarizeEdges/delete return vertices");
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}
	}

	/**
	 * Generates the vertices of the game graph from the input automaton.
	 *
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate framework.
	 * @deprecated The operation does not support the usage of an initial partition, use {@link #generateGraphBase()}
	 *             instead.
	 */
	@Deprecated
	public void generateVertices() throws AutomataOperationCanceledException {
		mLogger.debug("Generating vertices.");
		final int duplicatorPriority = DUPLICATOR_PRIORITY;

		for (final STATE leftState : mNwa.getStates()) {
			for (final STATE rightState : mNwa.getStates()) {
				// Generate Spoiler vertices (leftState, rightState)
				final int priority = calculatePriority(leftState, rightState);

				// In delayed simulation we always generate the vertex with
				// priority zero. Conditionally we also add a vertex with
				// priority one.
				if (mSimulationType == SimulationOrMinimizationType.DELAYED) {
					addSpoilerVertexHelper(0, false, leftState, rightState);
				} else {
					addSpoilerVertexHelper(priority, false, leftState, rightState);
				}

				// In delayed simulation we may also add a vertex with
				// priority one that has the bit set to true.
				if (mSimulationType == SimulationOrMinimizationType.DELAYED) {
					if (priority == 1) {
						addSpoilerVertexHelper(1, true, leftState, rightState);
					}
				}

				// Generate Duplicator vertices (leftState, rightState, letter)
				// Vertices generated by internal transitions
				for (final LETTER letter : mNwa.lettersInternalIncoming(leftState)) {
					addDuplicatorVertexHelper(duplicatorPriority, false, leftState, rightState, letter,
							TransitionType.INTERNAL);
					if (mSimulationType == SimulationOrMinimizationType.DELAYED) {
						addDuplicatorVertexHelper(duplicatorPriority, true, leftState, rightState, letter,
								TransitionType.INTERNAL);
					}
				}
				// Vertices generated by call transitions
				for (final LETTER letter : mNwa.lettersCallIncoming(leftState)) {
					addDuplicatorVertexHelper(duplicatorPriority, false, leftState, rightState, letter,
							TransitionType.CALL);
					if (mSimulationType == SimulationOrMinimizationType.DELAYED) {
						addDuplicatorVertexHelper(duplicatorPriority, true, leftState, rightState, letter,
								TransitionType.CALL);
					}
				}
				// Vertices generated by return transitions
				for (final IncomingReturnTransition<LETTER, STATE> transition : mNwa.returnPredecessors(leftState)) {
					// Only create vertex if the return transition is
					// possible to go from here.
					// That is when in (q0, q1) -> (q2, q1, r/q3),
					// q0 has q3 as down state
					if (hasDownState(transition.getLinPred(), transition.getHierPred())) {
						addDuplicatorVertexHelper(duplicatorPriority, false, leftState, rightState,
								transition.getLetter(), TransitionType.RETURN);
						if (mSimulationType == SimulationOrMinimizationType.DELAYED) {
							addDuplicatorVertexHelper(duplicatorPriority, true, leftState, rightState,
									transition.getLetter(), TransitionType.RETURN);
						}
					}
				}

				// If operation was canceled, for example from the
				// Ultimate framework
				if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
					mLogger.debug("Stopped in generateGameGraphFromAutomaton/generating vertices");
					throw new AutomataOperationCanceledException(this.getClass());
				}
			}
		}

		// Increase by one, global infinity is amount of priority one + 1
		mGameGraph.increaseGlobalInfinity();
	}

	/**
	 * Gets a Duplicator vertex by its signature.
	 *
	 * @param q0
	 *            Left state
	 * @param q1
	 *            Right state
	 * @param a
	 *            Used letter
	 * @param bit
	 *            Extra bit of the vertex
	 * @param transType
	 *            Type of the transition
	 * @param summarizeEdge
	 *            Summarize edge the vertex belongs to if the transition is of type
	 *            {@link TransitionType#SUMMARIZE_ENTRY} or {@link TransitionType#SUMMARIZE_EXIT}. Use <tt>null</tt> if
	 *            that is not the case.
	 * @param sink
	 *            Sink the vertex belongs to if the transition is of type {@link TransitionType#SINK}. Use <tt>null</tt>
	 *            if that is not the case.
	 * @return The duplicator vertex associated to the given signature. See
	 *         {@link #getDuplicatorVertex(Object, Object, Object, boolean)}.
	 */
	public DuplicatorVertex<LETTER, STATE> getDuplicatorVertex(final STATE q0, final STATE q1, final LETTER a,
			final boolean bit, final TransitionType transType, final SummarizeEdge<LETTER, STATE> summarizeEdge,
			final DuplicatorWinningSink<LETTER, STATE> sink) {
		return mAutomatonStatesToGraphDuplicatorVertex.get(new Hep<>(q0, q1, a, bit, transType, summarizeEdge, sink));
	}

	/**
	 * Gets the changes that where made for removing return vertices and their edges. It includes the removed returning
	 * vertex, its out- and in-going edges and generated push-over edges.
	 *
	 * @return The changes that where made for removing return vertices and their edges.
	 */
	public GameGraphChanges<LETTER, STATE> getRemovedReturnBridgesChanges() {
		return mRemovedReturnBridges;
	}

	/**
	 * Gets the performance log of this object.
	 *
	 * @return Performance log of this object
	 */
	public SimulationPerformance getSimulationPerformance() {
		return mSimulationPerformance;
	}

	/**
	 * Gets a Spoiler vertex by its signature. See {@link #getSpoilerVertex(Object, Object, boolean)}.
	 *
	 * @param q0
	 *            Left state
	 * @param q1
	 *            Right state
	 * @param bit
	 *            Extra bit of the vertex
	 * @param summarizeEdge
	 *            Summarize edge the vertex belongs to. Use <tt>null</tt> if the vertex does not belong to one. This is
	 *            used for special vertices that are used to represent a summary edge correctly for a valid game graph.
	 * @param sink
	 *            Sink the vertex belongs to. Use <tt>null</tt> if the vertex does not belong to one. This is used for
	 *            special vertices that are used to represent a sink correctly for a valid game graph.
	 * @return The spoiler vertex associated to the given signature. See
	 *         {@link #getSpoilerVertex(Object, Object, boolean)}.
	 */
	public SpoilerVertex<LETTER, STATE> getSpoilerVertex(final STATE q0, final STATE q1, final boolean bit,
			final SummarizeEdge<LETTER, STATE> summarizeEdge, final DuplicatorWinningSink<LETTER, STATE> sink) {
		return mAutomatonStatesToGraphSpoilerVertex.get(new Quin<>(q0, q1, bit, summarizeEdge, sink));
	}

	/**
	 * Transforms dead ending Spoiler/Duplicator vertices into instant wins for Duplicator/Spoiler by adding a
	 * Duplicator/Spoiler-Winning-Sink. Such vertices may occur if they can not use a return-transition due to their
	 * down state and if no other transitions are available.<br/>
	 * <br/>
	 * In direct simulation it correctly takes care of spoiler vertices that are directly loosing for Duplicator. Such
	 * vertices need to form a legal win for Spoiler though they are dead-ends.
	 *
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate framework.
	 */
	public void patchGraph() throws AutomataOperationCanceledException {
		// Patch Spoiler vertices that are directly losing for Duplicator in
		// direct simulation
		for (final SpoilerNwaVertex<LETTER, STATE> spoilerVertex : mDuplicatorDirectlyLosesInSpoiler) {
			// Patch the vertex into an instant win for Spoiler
			addSpoilerWinningSinkExtended(spoilerVertex);

			if (mLogger.isDebugEnabled()) {
				mLogger.debug("\tPatched directly losing: " + spoilerVertex);
			}
			if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
				mLogger.debug("Stopped in generateBuchiAutomatonFromGraph/patchDeadEnds");
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}

		// We do not need this data structure anymore
		mDuplicatorDirectlyLosesInSpoiler.clear();

		// Patch Spoiler dead ends
		for (final SpoilerNwaVertex<LETTER, STATE> possibleDeadEnd : mPossibleSpoilerDeadEnd) {
			// Do not take a look at the vertex if it is no dead end. This is
			// possible if the vertex has other alternatives than the
			// return-transition, which it can not use.
			if (mGameGraph.hasSuccessors(possibleDeadEnd)) {
				continue;
			}

			// Patch the dead end into an instant win for Duplicator
			addDuplicatorWinningSink(possibleDeadEnd);

			if (mLogger.isDebugEnabled()) {
				mLogger.debug("\tPatched spoiler dead-end: " + possibleDeadEnd);
			}
			if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
				mLogger.debug("Stopped in generateBuchiAutomatonFromGraph/patchDeadEnds");
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}
		// We do not need this data structure anymore
		mPossibleSpoilerDeadEnd.clear();

		// Patch Duplicator non-return dead ends
		for (final DuplicatorNwaVertex<LETTER, STATE> possibleDeadEnd : mPossibleNonReturnDuplicatorDeadEnd) {
			// Do not take a look at the vertex if it is no dead end. This is
			// possible if the vertex has other alternatives than the
			// return-transition, which it can not use.
			if (mGameGraph.hasSuccessors(possibleDeadEnd)) {
				continue;
			}

			// Patch the dead end into an instant win for Spoiler
			addSpoilerWinningSink(possibleDeadEnd);

			if (mLogger.isDebugEnabled()) {
				mLogger.debug("\tPatched duplicator dead-end: " + possibleDeadEnd);
			}
			if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
				mLogger.debug("Stopped in generateBuchiAutomatonFromGraph/patchDeadEnds");
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}
		// We do not need this data structure anymore
		mPossibleNonReturnDuplicatorDeadEnd.clear();
	}

	/**
	 * Adds a given transition to the internal field of buechi transitions, if fair simulation.
	 *
	 * @param transition
	 *            Transition to add
	 */
	private void addAutomatonTransitionToInternalField(final Triple<STATE, LETTER, STATE> transition) {
		final FairGameGraph<LETTER, STATE> fairGraph = castGraphToFairGameGraph();
		if (fairGraph != null) {
			fairGraph.getBuechiTransitions().add(transition);
		}
	}

	/**
	 * Generates and adds the duplicator vertex represented by the arguments. Also possibly adds the vertex to some data
	 * structures.
	 *
	 * @param priority
	 *            Priority of the vertices
	 * @param bit
	 *            Bit of the vertices
	 * @param leftState
	 *            Left state of the vertices
	 * @param rightState
	 *            Right state of the vertices
	 * @param letter
	 *            Letter of the vertices
	 * @param type
	 *            Type of the vertices
	 * @return The generated and added Duplicator vertex or <tt>null</tt> if not created
	 */
	private DuplicatorNwaVertex<LETTER, STATE> addDuplicatorVertexHelper(final int priority, final boolean bit,
			final STATE leftState, final STATE rightState, final LETTER letter, final TransitionType type) {

		// For returning duplicator vertices, it may often be requested to
		// add existent vertices again. This may cause problems, because of
		// that we check it.
		if (type != TransitionType.RETURN
				|| (getDuplicatorVertex(leftState, rightState, letter, bit, type, null, null) == null)) {
			final DuplicatorNwaVertex<LETTER, STATE> duplicatorVertex =
					new DuplicatorNwaVertex<>(priority, bit, leftState, rightState, letter, type);
			addDuplicatorVertex(duplicatorVertex);

			// Memorize vertices that possible end up as dead-ends because they
			// can not take a transition.
			// Such vertices need to form a instant win for Spoiler.
			boolean hasSuccessors = true;
			if (type.equals(TransitionType.INTERNAL)) {
				hasSuccessors = mNwa.internalSuccessors(rightState, letter).iterator().hasNext();
			} else if (type.equals(TransitionType.CALL)) {
				hasSuccessors = mNwa.callSuccessors(rightState, letter).iterator().hasNext();
			} else if (type.equals(TransitionType.RETURN)) {
				hasSuccessors = mNwa.returnSuccessors(rightState, letter).iterator().hasNext();

				// Memorize Duplicator Return vertices, we later need it for
				// summarize edge generation.
				mDuplicatorReturningVertices.add(duplicatorVertex);
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("\tAdded to duplicatorReturningVertices: " + duplicatorVertex);
				}
			}
			if (!hasSuccessors) {
				if (!type.equals(TransitionType.RETURN)) {
					mPossibleNonReturnDuplicatorDeadEnd.add(duplicatorVertex);
					if (mLogger.isDebugEnabled()) {
						mLogger.debug("\tAdded to possibleNonReturnDuplicatorDeadEnd: " + duplicatorVertex);
					}
				}
			}
			return duplicatorVertex;
		}
		return null;
	}

	/**
	 * Creates and adds a duplicator winning sink to the given sink entry. To form a valid edge it creates a pair of two
	 * states after the entry. In detail this will be: <b>sinkEntry -> DuplicatorSink -> SpoilerSink -> DuplicatorSink
	 * -> ...</b>. <br/>
	 * <br/>
	 * The SpoilerSink will have a priority of 0 to form a winning vertex for Duplicator.
	 *
	 * @param sinkEntry
	 *            Entry vertex of the sink
	 */
	private void addDuplicatorWinningSink(final SpoilerNwaVertex<LETTER, STATE> sinkEntry) {
		// Only add if not already existent
		if (mEntryToSink.get(sinkEntry) == null) {
			if (mDuplicatorWinningSink == null) {
				mDuplicatorWinningSink = new DuplicatorWinningSink<>(mGameGraph);
				mDuplicatorWinningSink.addToGraph();
			}

			mEntryToSink.put(sinkEntry, mDuplicatorWinningSink);

			mDuplicatorWinningSink.connectToEntry(sinkEntry);

			if (mLogger.isDebugEnabled()) {
				mLogger.debug("\tAdded to duplicatorWinningSink: " + sinkEntry);
			}
		}
	}

	/**
	 * Adds a given edge to the given game automaton, if not already existent.
	 *
	 * @param src
	 *            Source game state of the edge to add
	 * @param letter
	 *            Letter of the edge to add
	 * @param dest
	 *            Destination game state of the edge to add
	 * @param gameAutomaton
	 *            Game automaton to add to
	 */
	private void addEdgeToGameAutomaton(final IGameState src, final IGameLetter<LETTER, STATE> letter,
			final IGameState dest, final NestedWordAutomaton<IGameLetter<LETTER, STATE>, IGameState> gameAutomaton) {
		final TransitionType transType = letter.getTransitionType();
		if (transType.equals(TransitionType.INTERNAL)) {
			if (!gameAutomaton.containsInternalTransition(src, letter, dest)) {
				gameAutomaton.addInternalTransition(src, letter, dest);
			}
		} else if (transType.equals(TransitionType.CALL)) {
			if (!gameAutomaton.containsCallTransition(src, letter, dest)) {
				gameAutomaton.addCallTransition(src, letter, dest);
			}
		} else {
			throw new IllegalArgumentException(
					"The transition type of the game letter is not supported by this operation.");
		}
	}

	/**
	 * Adds a given return edge to the given game automaton, if not already existent.
	 *
	 * @param src
	 *            Source game state of the edge to add
	 * @param hierPred
	 *            The hierPred of this return edge
	 * @param letter
	 *            Letter of the edge to add
	 * @param dest
	 *            Destination game state of the edge to add
	 * @param gameAutomaton
	 *            Game automaton to add to
	 */
	private void addEdgeToGameAutomaton(final IGameState src, final IGameState hierPred,
			final IGameLetter<LETTER, STATE> letter, final IGameState dest,
			final NestedWordAutomaton<IGameLetter<LETTER, STATE>, IGameState> gameAutomaton) {
		final TransitionType transType = letter.getTransitionType();
		if (transType.equals(TransitionType.RETURN)) {
			if (!gameAutomaton.containsReturnTransition(src, hierPred, letter, dest)) {
				gameAutomaton.addReturnTransition(src, hierPred, letter, dest);
			}
		} else {
			throw new IllegalArgumentException(
					"The transition type of the game letter is not supported by this operation.");
		}
	}

	/**
	 * Adds a given game state to the given game automaton, if not already existent. The state will be initial and not
	 * final.
	 *
	 * @param gameState
	 *            Game state to add
	 * @param gameAutomaton
	 *            Game automaton to add to
	 */
	private void addGameStateToGameAutomaton(final IGameState gameState,
			final NestedWordAutomaton<IGameLetter<LETTER, STATE>, IGameState> gameAutomaton) {
		if (!gameAutomaton.contains(gameState)) {
			gameAutomaton.addState(true, false, gameState);
		}
	}

	/**
	 * Generates and adds the spoiler vertex represented by the arguments. Also increases global infinity bound and
	 * possibly adds the vertex to some data structures.
	 *
	 * @param priority
	 *            Priority of the vertex
	 * @param bit
	 *            Bit of the vertex
	 * @param leftState
	 *            Left state of the vertex
	 * @param rightState
	 *            Right state of the vertex
	 * @return The generated and added Spoiler vertex or <tt>null</tt> if not created
	 */
	private SpoilerNwaVertex<LETTER, STATE> addSpoilerVertexHelper(final int priority, final boolean bit,
			final STATE leftState, final STATE rightState) {
		final SpoilerNwaVertex<LETTER, STATE> spoilerVertex =
				new SpoilerNwaVertex<>(priority, bit, leftState, rightState);
		addSpoilerVertex(spoilerVertex);
		// Increase the infinity bound for every such vertex
		if (priority == 1) {
			mGameGraph.increaseGlobalInfinity();
		}

		// Memorize vertices that possible end up as dead-ends because they
		// can not take a return-transition due to their down state.
		// Such vertices need to form a instant win for Duplicator.
		final boolean hasInternalSuccessors = mNwa.internalSuccessors(leftState).iterator().hasNext();
		final boolean hasCallSuccessors = mNwa.callSuccessors(leftState).iterator().hasNext();
		// Do this in the order of the most unlikely events,
		// reduces computation time
		if (!hasInternalSuccessors) {
			final boolean hasReturnSuccessors = mNwa.returnSuccessors(leftState).iterator().hasNext();
			if (!hasReturnSuccessors) {
				if (!hasCallSuccessors) {
					mPossibleSpoilerDeadEnd.add(spoilerVertex);
					if (mLogger.isDebugEnabled()) {
						mLogger.debug("\tAdded to possibleSpoilerDeadEnd: " + spoilerVertex);
					}
				}
			}
		}
		// Remember the vertex if direct simulation and it is directly losing
		// for Duplicator
		if (mSimulationType.equals(SimulationOrMinimizationType.DIRECT) && doesLoseInDirectSim(leftState, rightState)) {
			mDuplicatorDirectlyLosesInSpoiler.add(spoilerVertex);
		}
		// Remember the vertex if delayed simulation, the right state is final
		// and the bit is set to true
		if (mSimulationType.equals(SimulationOrMinimizationType.DELAYED) && bit && mNwa.isFinal(rightState)) {
			// Such vertices should end up also being dead ends
			mPossibleSpoilerDeadEnd.add(spoilerVertex);
		}

		return spoilerVertex;
	}

	/**
	 * Creates and adds a spoiler winning sink to the given sink entry. To form a valid edge it creates a pair of two
	 * states after the entry. In detail this will be: <b>sinkEntry -> SpoilerSink -> DuplicatorSink -> SpoilerSink ->
	 * ...</b>. <br/>
	 * <br/>
	 * The SpoilerSink will have a priority of 1 to form a winning vertex for Spoiler.
	 *
	 * @param sinkEntry
	 *            Entry vertex of the sink
	 */
	private void addSpoilerWinningSink(final DuplicatorNwaVertex<LETTER, STATE> sinkEntry) {
		// Only add if not already existent
		if (mEntryToSink.get(sinkEntry) == null) {
			if (mSpoilerWinningSink == null) {
				mSpoilerWinningSink = new SpoilerWinningSink<>(mGameGraph);
				mSpoilerWinningSink.addToGraph();
			}

			mEntryToSink.put(sinkEntry, mSpoilerWinningSink);

			mSpoilerWinningSink.connectToEntry(sinkEntry);

			if (mLogger.isDebugEnabled()) {
				mLogger.debug("\tAdded to spoilerWinningSink: " + sinkEntry);
			}
		}
	}

	/**
	 * Creates and adds a spoiler winning sink to the given sink entry. To form a valid edge it creates a pair of two
	 * states after the entry. In detail this will be: <b>sinkEntry -> DuplicatorSink -> SpoilerSink -> DuplicatorSink
	 * -> ...</b>. <br/>
	 * <br/>
	 * The SpoilerSink will have a priority of 1 to form a winning vertex for Spoiler.
	 *
	 * @param sinkEntry
	 *            Entry vertex of the sink
	 */
	private void addSpoilerWinningSinkExtended(final SpoilerNwaVertex<LETTER, STATE> sinkEntry) {
		// Only add if not already existent
		if (mEntryToSink.get(sinkEntry) == null) {
			if (mSpoilerWinningSinkExtended == null) {
				mSpoilerWinningSinkExtended = new SpoilerWinningSinkExtended<>(mGameGraph);
				mSpoilerWinningSinkExtended.addToGraph();
			}

			mEntryToSink.put(sinkEntry, mSpoilerWinningSinkExtended);

			mSpoilerWinningSinkExtended.connectToEntry(sinkEntry);

			if (mLogger.isDebugEnabled()) {
				mLogger.debug("\tAdded to spoilerWinningSinkExtended: " + sinkEntry);
			}
		}
	}

	/**
	 * Creates and adds a summarize edge with given source and destinations. <br/>
	 * <br/>
	 * The sub-summarize edges will have no priority by default, it must be taken care of this afterwards.
	 *
	 * @param src
	 *            Source of the summarize edge
	 * @param spoilerChoice
	 *            The choice Spoiler did take for this summarize edge
	 * @param duplicatorChoices
	 *            Choices Duplicator can make with the bit it leads to, determine the sub-summarize edges
	 */
	private void addSummarizeEdge(final SpoilerNwaVertex<LETTER, STATE> src, final STATE spoilerChoice,
			final Set<Pair<STATE, Boolean>> duplicatorChoices) {
		// Only add if not already existent
		if (mSrcDestToSummarizeEdges.get(src, new Pair<>(spoilerChoice, duplicatorChoices)) == null) {
			final SummarizeEdge<LETTER, STATE> summarizeEdge =
					new SummarizeEdge<>(src, spoilerChoice, duplicatorChoices, this);
			summarizeEdge.addToGameGraph();
			mSrcDestToSummarizeEdges.put(src, new Pair<>(spoilerChoice, duplicatorChoices), summarizeEdge);
			mSimulationPerformance.increaseCountingMeasure(CountingMeasure.SUMMARIZE_EDGES);
			int currentAmountOfSubSummarize =
					mSimulationPerformance.getCountingMeasureResult(CountingMeasure.SUB_SUMMARIZE_EDGES);
			if (currentAmountOfSubSummarize == SimulationPerformance.NO_COUNTING_RESULT) {
				currentAmountOfSubSummarize = 0;
			}
			mSimulationPerformance.setCountingMeasure(CountingMeasure.SUB_SUMMARIZE_EDGES,
					currentAmountOfSubSummarize + duplicatorChoices.size());

			if (mLogger.isDebugEnabled()) {
				mLogger.debug("\tAdded summarizeEdge: " + src + " -" + spoilerChoice + "-> " + duplicatorChoices);
			}
		}
	}

	/**
	 * Calculates the priority of a given {@link SpoilerVertex} by its representation <i>(state spoiler is at, state
	 * duplicator is at)</i>.<br/>
	 * Note that {@link DuplicatorVertex} objects always should have priority of {@link #DUPLICATOR_PRIORITY}.
	 *
	 * @param leftState
	 *            The state spoiler is at
	 * @param rightState
	 *            The state duplicator is at
	 * @return The calculated priority of the given {@link SpoilerVertex} which is 0 if the right state is final, 2 if
	 *         both are final and 1 if only the left state is final.
	 */
	private int calculatePriority(final STATE leftState, final STATE rightState) {
		// In direct simulation, every vertex has zero as priority
		if (mSimulationType == SimulationOrMinimizationType.DIRECT) {
			return 0;
		}

		// In delayed simulation priority zero is always possible, only priority
		// one is conditional. In this case, this method should only return one
		// if possible, else zero.
		if (mSimulationType == SimulationOrMinimizationType.DELAYED) {
			if (!mNwa.isFinal(rightState)) {
				return 1;
			}
			return 0;
		}

		if (mNwa.isFinal(rightState)) {
			return 0;
		} else if (mNwa.isFinal(leftState)) {
			return 1;
		} else {
			return 2;
		}
	}

	/**
	 * Tries to cast the game graph to a fair game graph and returns it.
	 *
	 * @return The graph casted to a fair game graph, <tt>null</tt> if not possible.
	 */
	private FairGameGraph<LETTER, STATE> castGraphToFairGameGraph() {
		FairGameGraph<LETTER, STATE> fairGraph = null;
		if (mGameGraph instanceof FairGameGraph<?, ?>) {
			fairGraph = (FairGameGraph<LETTER, STATE>) mGameGraph;
		}
		return fairGraph;
	}

	/**
	 * Computes all hierPreds for a game automaton, given the source and destination for both players as SpoilerVertex.
	 *
	 * @param src
	 *            Source of both players
	 * @param dest
	 *            Destination of both players
	 * @param returnLetter
	 *            Letter used for returning
	 * @return All hierPreds for a game automaton, given the source and destination for both players as SpoilerVertex.
	 */
	private Iterable<GameSpoilerNwaVertex<LETTER, STATE>> computeAllGameHierPreds(
			final SpoilerVertex<LETTER, STATE> src, final SpoilerVertex<LETTER, STATE> dest,
			final LETTER returnLetter) {
		return computeAllGameHierPreds(src.getQ0(), src.getQ1(), dest.getQ0(), dest.getQ1(), returnLetter);
	}

	/**
	 * Computes all hierPreds for a game automaton, given the source for both players and at least the destination of
	 * Spoiler as SpoilerVertex.
	 *
	 * @param src
	 *            Source of both players
	 * @param spoilerDestination
	 *            Destination of Spoiler
	 * @param returnLetter
	 *            Letter used for returning
	 * @return All hierPreds for a game automaton, given the source for both players and at least the destination of
	 *         Spoiler as SpoilerVertex.
	 */
	private Iterable<GameSpoilerNwaVertex<LETTER, STATE>> computeAllGameHierPreds(
			final SpoilerVertex<LETTER, STATE> src, final STATE spoilerDestination, final LETTER returnLetter) {
		return computeAllGameHierPreds(src.getQ0(), src.getQ1(), spoilerDestination, null, returnLetter);
	}

	/**
	 * Computes all hierPreds for a game automaton, given the source and destination for both players.
	 *
	 * @param spoilerSrc
	 *            Source of Spoiler
	 * @param duplicatorSrc
	 *            Source of Duplicator
	 * @param spoilerDest
	 *            Destination of Spoiler. This value is allowed to be <tt>null</tt>, in this case every down state of
	 *            the source gets considered as SpoilerHierPred.
	 * @param duplicatorDest
	 *            Destination of Duplicator. This value is allowed to be <tt>null</tt>, in this case every down state of
	 *            the source gets considered as DuplicatorHierPred.
	 * @param returnLetter
	 *            Letter used for returning
	 * @return All hierPreds for a game automaton, given the source and destination for both players.
	 */
	private Iterable<GameSpoilerNwaVertex<LETTER, STATE>> computeAllGameHierPreds(final STATE spoilerSrc,
			final STATE duplicatorSrc, final STATE spoilerDest, final STATE duplicatorDest, final LETTER returnLetter) {
		final Set<GameSpoilerNwaVertex<LETTER, STATE>> gameHierPreds = new LinkedHashSet<>();
		final Set<STATE> spoilerHierPreds = new HashSet<>();
		final Set<STATE> duplicatorHierPreds = new HashSet<>();

		// Retrieve hierPred of Spoiler
		if (spoilerDest != null) {
			for (final OutgoingReturnTransition<LETTER, STATE> spoilerReturnTrans : mNwa.returnSuccessors(spoilerSrc,
					returnLetter)) {
				if (spoilerReturnTrans.getSucc().equals(spoilerDest)) {
					spoilerHierPreds.add(spoilerReturnTrans.getHierPred());
				}
			}
		} else {
			// Consider every down state of the source as hierPred
			for (final STATE downState : mNwa.getDownStates(spoilerSrc)) {
				spoilerHierPreds.add(downState);
			}
			spoilerHierPreds.remove(mNwa.getEmptyStackState());
		}

		// Retrieve hierPred of Duplicator
		if (duplicatorDest != null) {
			for (final OutgoingReturnTransition<LETTER, STATE> duplicatorReturnTrans : mNwa
					.returnSuccessors(duplicatorSrc, returnLetter)) {
				if (duplicatorReturnTrans.getSucc().equals(duplicatorDest)) {
					duplicatorHierPreds.add(duplicatorReturnTrans.getHierPred());
				}
			}
		} else {
			// Consider every down state of the source as hierPred
			for (final STATE downState : mNwa.getDownStates(duplicatorSrc)) {
				duplicatorHierPreds.add(downState);
			}
			duplicatorHierPreds.remove(mNwa.getEmptyStackState());
		}

		// Merge both sets
		for (final STATE spoilerHierPred : spoilerHierPreds) {
			for (final STATE duplicatorHierPred : duplicatorHierPreds) {
				SpoilerVertex<LETTER, STATE> representingHierPred =
						getSpoilerVertex(spoilerHierPred, duplicatorHierPred, false, null, null);
				if (representingHierPred != null && representingHierPred instanceof SpoilerNwaVertex<?, ?>) {
					gameHierPreds
							.add(new GameSpoilerNwaVertex<>((SpoilerNwaVertex<LETTER, STATE>) representingHierPred));
				}
				// In delayed simulation we also need to account for the bit set
				// to true
				if (mSimulationType.equals(SimulationOrMinimizationType.DELAYED)) {
					representingHierPred = getSpoilerVertex(spoilerHierPred, duplicatorHierPred, true, null, null);
					if (representingHierPred != null && representingHierPred instanceof SpoilerNwaVertex<?, ?>) {
						gameHierPreds.add(
								new GameSpoilerNwaVertex<>((SpoilerNwaVertex<LETTER, STATE>) representingHierPred));
					}
				}
			}
		}

		return gameHierPreds;
	}

	/**
	 * Creates a game automaton that is used for summarize edge computation. All states are initial and no state will be
	 * final. This can afterwards be changed by using {@link NestedWordAutomatonFilteredStates} as a wrapper.
	 *
	 * @return A game automaton that is used for summarize edge computation
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate framework.
	 */
	private INwaOutgoingLetterAndTransitionProvider<IGameLetter<LETTER, STATE>, IGameState> createGameAutomaton()
			throws AutomataOperationCanceledException {
		final Set<IGameLetter<LETTER, STATE>> internalGameAlphabet = new HashSet<>();
		final Set<IGameLetter<LETTER, STATE>> callGameAlphabet = new HashSet<>();
		final Set<IGameLetter<LETTER, STATE>> returnGameAlphabet = new HashSet<>();
		
		final VpAlphabet<IGameLetter<LETTER, STATE>> gameVpAlphabet = new VpAlphabet<>(internalGameAlphabet, callGameAlphabet, returnGameAlphabet);
		

		final NestedWordAutomaton<IGameLetter<LETTER, STATE>, IGameState> gameAutomaton = new NestedWordAutomaton<>(
				mServices, gameVpAlphabet, new GameFactory());

		// Collect all data by using
		// (spoilerVertex -> duplicatorSucc -> spoilerSucc)
		final List<Pair<SpoilerNwaVertex<LETTER, STATE>, DuplicatorNwaVertex<LETTER, STATE>>> runningInDuplicatorDeadEnd =
				new LinkedList<>();
		for (final SpoilerVertex<LETTER, STATE> spoilerVertex : mGameGraph.getSpoilerVertices()) {
			if (!(spoilerVertex instanceof SpoilerNwaVertex<?, ?>)) {
				continue;
			}
			final SpoilerNwaVertex<LETTER, STATE> spoilerNwaVertex = (SpoilerNwaVertex<LETTER, STATE>) spoilerVertex;

			// As we do not know at this point if spoilerNwaVertex is of
			// relevance, only declare but not create the game vertex
			final boolean wasSourceAlreadyAdded = false;
			GameSpoilerNwaVertex<LETTER, STATE> gameNwaVertex = null;

			final Set<Vertex<LETTER, STATE>> firstSuccessors = mGameGraph.getSuccessors(spoilerNwaVertex);
			if (firstSuccessors == null) {
				// Spoiler dead-end, not possible since patched before.
				continue;
			}
			for (final Vertex<LETTER, STATE> firstSuccessor : firstSuccessors) {
				if (!(firstSuccessor instanceof DuplicatorNwaVertex<?, ?>)) {
					// This should not be possible in a correct game graph.
					continue;
				}
				final DuplicatorNwaVertex<LETTER, STATE> duplicatorNwaSucc =
						(DuplicatorNwaVertex<LETTER, STATE>) firstSuccessor;
				final Set<Vertex<LETTER, STATE>> secondSuccessors = mGameGraph.getSuccessors(duplicatorNwaSucc);
				if (secondSuccessors == null) {
					// Duplicator dead-end, only possible for some return
					// vertices.
					if (duplicatorNwaSucc.getTransitionType().equals(TransitionType.RETURN)) {
						// We later add (spoilerVertex -> duplicatorSucc ->
						// mAuxiliaryGameState) for every corresponding letter
						runningInDuplicatorDeadEnd.add(new Pair<>(spoilerNwaVertex, duplicatorNwaSucc));
						if (mLogger.isDebugEnabled()) {
							mLogger.debug("\tRuns into Duplicator dead end: " + spoilerNwaVertex + " -> "
									+ duplicatorNwaSucc);
						}
					}
					continue;
				}

				// As there are successors, already add some stuff
				final TransitionType transType = duplicatorNwaSucc.getTransitionType();
				final IGameLetter<LETTER, STATE> letter;
				switch (transType) {
					case CALL:
						letter = duplicatorNwaSucc;
						callGameAlphabet.add(letter);
						break;
					case INTERNAL:
						letter = duplicatorNwaSucc;
						internalGameAlphabet.add(letter);
						break;
					case RETURN:
						letter = duplicatorNwaSucc;
						returnGameAlphabet.add(letter);
						break;
					case SINK:
					case SUMMARIZE_ENTRY:
					case SUMMARIZE_EXIT:
						letter = null;
						break;
					default:
						throw new AssertionError("unknown ETransitionType");
				}
				// At this point we know that the source is of relevance, add it
				// if not already done before
				if (!wasSourceAlreadyAdded) {
					gameNwaVertex = new GameSpoilerNwaVertex<>(spoilerNwaVertex);
					addGameStateToGameAutomaton(gameNwaVertex, gameAutomaton);
				}

				for (final Vertex<LETTER, STATE> secondSuccessor : secondSuccessors) {
					if (!(secondSuccessor instanceof SpoilerNwaVertex<?, ?>)) {
						// This should not be possible in a correct game graph.
						continue;
					}
					final SpoilerNwaVertex<LETTER, STATE> spoilerNwaSucc =
							(SpoilerNwaVertex<LETTER, STATE>) secondSuccessor;

					// We add (spoilerVertex -> duplicatorSucc -> spoilerSucc)
					// to the game automaton
					final GameSpoilerNwaVertex<LETTER, STATE> gameNwaSucc = new GameSpoilerNwaVertex<>(spoilerNwaSucc);
					addGameStateToGameAutomaton(gameNwaSucc, gameAutomaton);

					if (transType.equals(TransitionType.INTERNAL)) {
						addEdgeToGameAutomaton(gameNwaVertex, letter, gameNwaSucc, gameAutomaton);
					} else if (transType.equals(TransitionType.CALL)) {
						addEdgeToGameAutomaton(gameNwaVertex, letter, gameNwaSucc, gameAutomaton);
					} else if (transType.equals(TransitionType.RETURN)) {
						final Iterable<GameSpoilerNwaVertex<LETTER, STATE>> gameHierPreds = computeAllGameHierPreds(
								spoilerNwaVertex, spoilerNwaSucc, duplicatorNwaSucc.getLetter());
						for (final GameSpoilerNwaVertex<LETTER, STATE> gameHierPred : gameHierPreds) {
							addGameStateToGameAutomaton(gameHierPred, gameAutomaton);
							addEdgeToGameAutomaton(gameNwaVertex, gameHierPred, letter, gameNwaSucc, gameAutomaton);
						}
					}
				}

				// If operation was canceled, for example from the
				// Ultimate framework
				if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
					mLogger.debug("Stopped in generateSummarizeEdges/create game automaton");
					throw new AutomataOperationCanceledException(this.getClass());
				}
			}
		}

		// Add pairs that run into a Duplicator dead end by (spoilerVertex ->
		// duplicatorSucc -> mAuxiliaryGameState) for every needed game letter
		if (!runningInDuplicatorDeadEnd.isEmpty()) {
			addGameStateToGameAutomaton(mAuxiliaryGameState, gameAutomaton);
		}
		for (final Pair<SpoilerNwaVertex<LETTER, STATE>, DuplicatorNwaVertex<LETTER, STATE>> runsInDuplicatorDeadEnd : runningInDuplicatorDeadEnd) {
			final SpoilerNwaVertex<LETTER, STATE> spoilerNwaVertex = runsInDuplicatorDeadEnd.getFirst();
			final DuplicatorNwaVertex<LETTER, STATE> duplicatorNwaSucc = runsInDuplicatorDeadEnd.getSecond();
			final STATE spoilerDest = duplicatorNwaSucc.getQ0();
			final LETTER letter = duplicatorNwaSucc.getLetter();

			final GameSpoilerNwaVertex<LETTER, STATE> gameNwaVertex = new GameSpoilerNwaVertex<>(spoilerNwaVertex);
			addGameStateToGameAutomaton(gameNwaVertex, gameAutomaton);

			// First setup the game letter we need and ensure it is contained in
			// the alphabet
			returnGameAlphabet.add(duplicatorNwaSucc);

			// We now add return edges for all corresponding game hierPreds
			for (final GameSpoilerNwaVertex<LETTER, STATE> possibleGameHierPred : computeAllGameHierPreds(
					spoilerNwaVertex, spoilerDest, letter)) {
				addGameStateToGameAutomaton(possibleGameHierPred, gameAutomaton);
				addEdgeToGameAutomaton(gameNwaVertex, possibleGameHierPred, duplicatorNwaSucc, mAuxiliaryGameState,
						gameAutomaton);

				if (mLogger.isDebugEnabled()) {
					mLogger.debug("\tAdded edge for gameHierPred: " + possibleGameHierPred);
				}
			}
		}

		return gameAutomaton;
	}

	/**
	 * Returns whether Duplicator would directly lose in direct simulation if moving to the given Spoiler vertex, or if
	 * Spoiler moves from here to him. This is the case if Spoilers left state is final and the right state is not.
	 *
	 * @param leftSpoilerState
	 *            Left state of Spoilers vertex
	 * @param rightSpoilerState
	 *            Right state of Spoilers vertex
	 * @return Whether Duplicator would directly lose in direct simulation if moving to the given Spoiler vertex, or if
	 *         Spoiler moves from here to him.
	 */
	private boolean doesLoseInDirectSim(final STATE leftSpoilerState, final STATE rightSpoilerState) {
		final boolean doesLose = mNwa.isFinal(leftSpoilerState) && !mNwa.isFinal(rightSpoilerState);
		if (doesLose) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("\t\tDuplicator directly loses with Spoiler in: (" + leftSpoilerState + ", "
						+ rightSpoilerState + ")");
			}
		}
		return doesLose;
	}

	/**
	 * Returns if a given up state has a given down state.
	 *
	 * @param upState
	 *            Up state in question
	 * @param downState
	 *            Down state in question
	 * @return If the given up state has the given down state.
	 */
	private boolean hasDownState(final STATE upState, final STATE downState) {
		return mNwa.isDoubleDecker(upState, downState);
	}

	/**
	 * Adds a given duplicator vertex to the graph and all corresponding internal fields.
	 *
	 * @param vertex
	 *            Vertex to add
	 */
	protected void addDuplicatorVertex(final DuplicatorVertex<LETTER, STATE> vertex) {
		if (vertex instanceof DuplicatorNwaVertex<?, ?>) {
			final DuplicatorNwaVertex<LETTER, STATE> vertexAsNwa = (DuplicatorNwaVertex<LETTER, STATE>) vertex;
			mGameGraph.getInternalDuplicatorVerticesField().add(vertexAsNwa);
			mAutomatonStatesToGraphDuplicatorVertex.put(
					new Hep<>(vertexAsNwa.getQ0(), vertexAsNwa.getQ1(), vertexAsNwa.getLetter(), vertexAsNwa.isB(),
							vertexAsNwa.getTransitionType(), vertexAsNwa.getSummarizeEdge(), vertexAsNwa.getSink()),
					vertexAsNwa);
		} else {
			mGameGraph.addDuplicatorVertex(vertex);
		}
	}

	/**
	 * Adds the given edge to the graph and all corresponding internal fields.
	 *
	 * @param src
	 *            Source of the edge to add
	 * @param dest
	 *            Destination of the edge to add
	 */
	protected void addEdge(final Vertex<LETTER, STATE> src, final Vertex<LETTER, STATE> dest) {
		mGameGraph.addEdge(src, dest);
	}

	/**
	 * Adds a given spoiler vertex to the graph and all corresponding internal fields.
	 *
	 * @param vertex
	 *            Vertex to add
	 */
	protected void addSpoilerVertex(final SpoilerVertex<LETTER, STATE> vertex) {
		if (vertex instanceof SpoilerNwaVertex<?, ?>) {
			final SpoilerNwaVertex<LETTER, STATE> vertexAsNwa = (SpoilerNwaVertex<LETTER, STATE>) vertex;
			mGameGraph.getInternalSpoilerVerticesField().add(vertexAsNwa);
			mAutomatonStatesToGraphSpoilerVertex.put(new Quin<>(vertexAsNwa.getQ0(), vertexAsNwa.getQ1(),
					vertexAsNwa.isB(), vertexAsNwa.getSummarizeEdge(), vertexAsNwa.getSink()), vertexAsNwa);
		} else {
			mGameGraph.addSpoilerVertex(vertex);
		}
	}

	/**
	 * Gets the game graph that uses this generation object.
	 *
	 * @return The game graph that uses this generation object.
	 */
	protected AGameGraph<LETTER, STATE> getGameGraph() {
		return mGameGraph;
	}

	/**
	 * Removes a given duplicator vertex from the graph and all corresponding internal fields.
	 *
	 * @param vertex
	 *            Vertex to remove
	 */
	protected void removeDuplicatorVertex(final DuplicatorVertex<LETTER, STATE> vertex) {
		if (vertex instanceof DuplicatorNwaVertex<?, ?>) {
			final DuplicatorNwaVertex<LETTER, STATE> vertexAsNwa = (DuplicatorNwaVertex<LETTER, STATE>) vertex;
			mGameGraph.getInternalDuplicatorVerticesField().remove(vertexAsNwa);
			mAutomatonStatesToGraphDuplicatorVertex.put(
					new Hep<>(vertexAsNwa.getQ0(), vertexAsNwa.getQ1(), vertexAsNwa.getLetter(), vertexAsNwa.isB(),
							vertexAsNwa.getTransitionType(), vertexAsNwa.getSummarizeEdge(), vertexAsNwa.getSink()),
					null);
		} else {
			mGameGraph.removeDuplicatorVertex(vertex);
		}
	}

	/**
	 * Removes a given spoiler vertex from the graph and all corresponding internal fields.
	 *
	 * @param vertex
	 *            Vertex to remove
	 */
	protected void removeSpoilerVertex(final SpoilerVertex<LETTER, STATE> vertex) {
		if (vertex instanceof SpoilerNwaVertex<?, ?>) {
			final SpoilerNwaVertex<LETTER, STATE> vertexAsNwa = (SpoilerNwaVertex<LETTER, STATE>) vertex;
			mGameGraph.getInternalSpoilerVerticesField().remove(vertexAsNwa);
			mAutomatonStatesToGraphSpoilerVertex.put(new Quin<>(vertexAsNwa.getQ0(), vertexAsNwa.getQ1(),
					vertexAsNwa.isB(), vertexAsNwa.getSummarizeEdge(), vertexAsNwa.getSink()), null);
		} else {
			mGameGraph.removeSpoilerVertex(vertex);
		}
	}
}
