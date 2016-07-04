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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.nwa.graph;

import java.math.BigInteger;
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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomatonFilteredStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Determinize;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.MinimizeNwaMaxSat2;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.ASimulation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.ESimulationType;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.GameGraphChanges;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.fair.FairGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.performance.ECountingMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.performance.ETimeMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.performance.SimulationPerformance;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.nwa.ETransitionType;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.nwa.LoopDetector;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.nwa.SearchElement;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.nwa.graph.game.GameDoubleDeckerSet;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.nwa.graph.game.GameFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.nwa.graph.game.GameLetter;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.nwa.graph.game.GameSinkState;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.nwa.graph.game.GameSpoilerNwaVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.nwa.graph.game.IGameState;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UniqueQueue;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Hep;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Quin;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Generates double decker game graphs based on nwa automaton. Supports
 * different types of simulation types.
 * 
 * @author Daniel Tischner
 *
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
	 * Data structure that allows a fast access to {@link DuplicatorVertex}
	 * objects by using their representation:<br/>
	 * <b>(Up state of spoiler or q0, up state of duplicator or q1, letter
	 * spoiler used before, bit, type of transition, summarize edge, sink)</b>.
	 */
	private final HashMap<Hep<STATE, STATE, LETTER, Boolean, ETransitionType, SummarizeEdge<LETTER, STATE>, IWinningSink<LETTER, STATE>>, DuplicatorVertex<LETTER, STATE>> mAutomatonStatesToGraphDuplicatorVertex;
	/**
	 * Data structure that allows a fast access to {@link SpoilerVertex} objects
	 * by using their representation:<br/>
	 * <b>(Up state of spoiler or q0, up state of duplicator or q1, bit,
	 * summarize edge, sink)</b>.
	 */
	private final HashMap<Quin<STATE, STATE, Boolean, SummarizeEdge<LETTER, STATE>, IWinningSink<LETTER, STATE>>, SpoilerVertex<LETTER, STATE>> mAutomatonStatesToGraphSpoilerVertex;

	/**
	 * Auxiliary game state, is used at summarize edge computation for pointing
	 * to dead-end return vertices.
	 */
	private final GameSinkState mAuxiliaryGameState;
	/**
	 * Provides a fast access to all Spoiler vertices that are directly losing
	 * for Duplicator, if he moves in. The set is only used if the simulation
	 * type is direct simulation.
	 */
	private final HashSet<SpoilerNwaVertex<LETTER, STATE>> mDuplicatorDirectlyLosesInSpoiler;

	/**
	 * Data structure of all duplicator vertices that have the transition type
	 * {@link ETransitionType#RETURN}. They are used for summarize edge
	 * generation.
	 */
	private final HashSet<DuplicatorNwaVertex<LETTER, STATE>> mDuplicatorReturningVertices;
	/**
	 * Instance of a Duplicator winning sink, <tt>null</tt> if not used.
	 */
	private DuplicatorWinningSink<LETTER, STATE> mDuplicatorWinningSink;
	/**
	 * Map of all winning sinks of the graph. Provides a fast access via the
	 * sink entry.
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
	 * The underlying nwa automaton, as double decker automaton, from which the
	 * game graph gets generated.
	 */
	private final IDoubleDeckerAutomaton<LETTER, STATE> mNwa;
	/**
	 * Data structure of all duplicator vertices that may end up being a dead
	 * end and are not using a return transition.
	 */
	private final HashSet<DuplicatorNwaVertex<LETTER, STATE>> mPossibleNonReturnDuplicatorDeadEnd;
	/**
	 * Data structure of all spoiler vertices that may end up being a dead end,
	 * because they can not take a return-transition due to their down state.
	 */
	private final HashSet<SpoilerNwaVertex<LETTER, STATE>> mPossibleSpoilerDeadEnd;
	/**
	 * Timer used for responding to timeouts and operation cancellation.
	 */
	private final IProgressAwareTimer mProgressTimer;
	/**
	 * Object that stores all changes made for removing return vertices and
	 * their edges. It includes the removed returning vertex, its out- and
	 * in-going edges and generated push-over edges.
	 */
	private final GameGraphChanges<LETTER, STATE> mRemovedReturnBridges;
	/**
	 * Amount of states the result automaton has.
	 */
	private int mResultAmountOfStates;
	/**
	 * Amount of transitions the result automaton has.
	 */
	private int mResultAmountOfTransitions;
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
	private final ESimulationType mSimulationType;
	/**
	 * Data structure of all Spoiler vertices that are predecessor of a
	 * Duplicator calling vertex. They are used for summarize edge generation.
	 */
	private final HashSet<SpoilerNwaVertex<LETTER, STATE>> mSpoilerCallPredecessors;
	/**
	 * Instance of a Spoiler winning sink, <tt>null</tt> if not used.
	 */
	private SpoilerWinningSink<LETTER, STATE> mSpoilerWinningSink;
	/**
	 * Instance of an extended Spoiler winning sink, <tt>null</tt> if not used.
	 */
	private SpoilerWinningSinkExtended<LETTER, STATE> mSpoilerWinningSinkExtended;
	/**
	 * Map of all summarize edges of the graph. Provides a fast access via
	 * source and destinations of the edge.
	 */
	private final NestedMap2<SpoilerNwaVertex<LETTER, STATE>, Pair<STATE, Set<STATE>>, SummarizeEdge<LETTER, STATE>> mSrcDestToSummarizeEdges;
	/**
	 * If the game graph should use push-over edges between successors and
	 * predecessors of return-invoking Duplicator vertices. If set to
	 * <tt>true</tt>, push-over edges will be generated.
	 */
	private final boolean mUsePushOverEdges;

	/**
	 * Creates a new generation object that modifies a given graph using a given
	 * nwa automaton and a desired simulation method.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param progressTimer
	 *            Timer used for responding to timeouts and operation
	 *            cancellation.
	 * @param logger
	 *            ILogger of the Ultimate framework.
	 * @param nwa
	 *            The underlying nwa automaton from which the game graph gets
	 *            generated.
	 * @param gameGraph
	 *            Game graph that should get modified by this object
	 * @param simulationType
	 *            Simulation method to use for graph generation. Supported types
	 *            are {@link ESimulationType#DIRECT DIRECT} and
	 *            {@link ESimulationType#FAIR FAIR}.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public NwaGameGraphGeneration(final AutomataLibraryServices services, final IProgressAwareTimer progressTimer,
			final ILogger logger, final IDoubleDeckerAutomaton<LETTER, STATE> nwa,
			final AGameGraph<LETTER, STATE> gameGraph, final ESimulationType simulationType)
					throws AutomataOperationCanceledException {
		mServices = services;
		mNwa = nwa;
		mAutomatonStatesToGraphDuplicatorVertex = new HashMap<>();
		mAutomatonStatesToGraphSpoilerVertex = new HashMap<>();
		mDuplicatorReturningVertices = new HashSet<>();
		mSpoilerCallPredecessors = new HashSet<>();
		mPossibleSpoilerDeadEnd = new HashSet<>();
		mPossibleNonReturnDuplicatorDeadEnd = new HashSet<>();
		mDuplicatorDirectlyLosesInSpoiler = new HashSet<>();
		mSrcDestToSummarizeEdges = new NestedMap2<>();
		mEntryToSink = new HashMap<>();
		mRemovedReturnBridges = new GameGraphChanges<>();
		mAuxiliaryGameState = new GameSinkState();
		mLogger = logger;
		mProgressTimer = progressTimer;
		mGameGraph = gameGraph;
		mSimulationType = simulationType;
		mUsePushOverEdges = false;

		mSpoilerWinningSink = null;
		mSpoilerWinningSinkExtended = null;
		mDuplicatorWinningSink = null;

		mResultAmountOfStates = 0;
		mResultAmountOfTransitions = 0;
		mSimulationPerformance = new SimulationPerformance(simulationType, false);
	}

	/**
	 * Clears all internal data structures of this object.
	 */
	public void clear() {
		mPossibleSpoilerDeadEnd.clear();
		mPossibleNonReturnDuplicatorDeadEnd.clear();
		mDuplicatorReturningVertices.clear();
		mEntryToSink.clear();
		mSrcDestToSummarizeEdges.clear();
		mDuplicatorDirectlyLosesInSpoiler.clear();
	}

	/**
	 * Computes the priorities of all previous generated summarize edges.
	 * 
	 * @throws IllegalStateException
	 *             If computing summarize edge priorities could not be done
	 *             because a live lock occurred.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public void computeSummarizeEdgePriorities() throws AutomataOperationCanceledException {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Computing priorities of summarize edges.");
		}
		// XXX Temporary fix
		for (final Triple<SpoilerNwaVertex<LETTER, STATE>, Pair<STATE, Set<STATE>>, SummarizeEdge<LETTER, STATE>> summarizeEdgeEntry : mSrcDestToSummarizeEdges
				.entrySet()) {
			final SummarizeEdge<LETTER, STATE> summarizeEdge = summarizeEdgeEntry.getThird();
			// In direct simulation every edge will have a priority of zero,
			// since nearly every vertex has a priority of zero.
			if (mSimulationType == ESimulationType.DIRECT) {
				// Do not add something to the queue and finish
				// the method by that
				summarizeEdge.setAllPriorities(0);
			}
			// XXX Temporary debugging line, remove it afterwards!
			if (mSimulationType == ESimulationType.DELAYED) {
				// Very destructive but preserves correctness
				summarizeEdge.setAllPriorities(1);
			}
		}

		/*
		// XXX Rework this
		final Queue<SearchElement<LETTER, STATE>> searchQueue = new UniqueQueue<>();
		final HashMap<Pair<Vertex<LETTER, STATE>, Vertex<LETTER, STATE>>, Integer> searchPriorities = new HashMap<>();
		final LoopDetector<LETTER, STATE> loopDetector = new LoopDetector<>(mGameGraph, mLogger, mProgressTimer);
		final HashMap<Pair<Vertex<LETTER, STATE>, VertexDownState<STATE>>, SummarizeEdge<LETTER, STATE>> invokerToSummarizeEdge = new HashMap<>();
		// Every vertex can maximal be added '3 * out-degree' times to the queue
		// TODO Performance impact of BigInteger is to high for a safety check.
		// This event may not even be possible for correct game graphs. In this
		// case, remove it after verification.
		final BigInteger maxAmountOfSearches = BigInteger.valueOf(mGameGraph.getSize()).pow(2)
				.multiply(BigInteger.valueOf(3));
		final BigInteger searchCounter = BigInteger.ZERO;
		// Add starting elements
		for (final Triple<SpoilerNwaVertex<LETTER, STATE>, Pair<STATE, Set<STATE>>, SummarizeEdge<LETTER, STATE>> summarizeEdgeEntry : mSrcDestToSummarizeEdges
				.entrySet()) {
			final SummarizeEdge<LETTER, STATE> summarizeEdge = summarizeEdgeEntry.getThird();
			// In direct simulation every edge will have a priority of zero,
			// since nearly every vertex has a priority of zero.
			if (mSimulationType == ESimulationType.DIRECT) {
				// Do not add something to the queue and finish
				// the method by that
				summarizeEdge.setAllPriorities(0);
			} else {
				final Vertex<LETTER, STATE> edgeSource = summarizeEdge.getSource();
				for (STATE duplicatorChoice : summarizeEdge.getDuplicatorChoices()) {
					for (SpoilerVertex<LETTER, STATE> spoilerInvoker : summarizeEdge
							.getSpoilerInvokerForChoice(duplicatorChoice)) {
						final SearchElement<LETTER, STATE> searchElement = new SearchElement<LETTER, STATE>(
								spoilerInvoker, edgeSource, null, summarizeEdge, duplicatorChoice);
						searchQueue.add(searchElement);
					}
				}
				// Memorize invoker element for detection of
				// corresponding summarize edges
				invokerToSummarizeEdge.put(new Pair<>(spoilerInvoker, invokingState), summarizeEdge);
			}
		}
		// Start the search
		while (!searchQueue.isEmpty() && searchCounter.compareTo(maxAmountOfSearches) <= 0) {
			searchCounter.add(BigInteger.ONE);
			final SearchElement<LETTER, STATE> searchElement = searchQueue.poll();
			final Vertex<LETTER, STATE> searchVertex = searchElement.getVertex();
			final Vertex<LETTER, STATE> searchTarget = searchElement.getTarget();
			final SummarizeEdge<LETTER, STATE> searchSummarizeEdge = searchElement.getSummarizeEdge();
			final STATE searchDuplicatorChoice = searchElement.getDuplicatorChoice();
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
					if (succ instanceof DuplicatorNwaVertex) {
						// Successor is duplicator vertex
						final DuplicatorNwaVertex<LETTER, STATE> succAsDuplicatorNwa = (DuplicatorNwaVertex<LETTER, STATE>) succ;
						final ETransitionType transitionType = succAsDuplicatorNwa.getTransitionType();
						// We will reject successor if it has no search priority
						// yet. This may indicate that the successor is
						// not capable of reaching the destination of
						// the summarize edge, which priority currently
						// shall be computed. If it, however, is capable
						// of that, he may force an update on the
						// current vertex later anyway. At this time the
						// successor will also have a search priority.
						if (transitionType == ETransitionType.RETURN || transitionType == ETransitionType.SINK
								|| transitionType == ETransitionType.SUMMARIZE_EXIT) {
							// Ignore return and special edges
							continue;
						} else if (transitionType == ETransitionType.SUMMARIZE_ENTRY) {
							// Use min(summarizeEdgePriority,
							// summarizeEdgeDestinationPriority) as priority
							// candidate
							final SummarizeEdge<LETTER, STATE> summarizeEdge = succAsDuplicatorNwa.getSummarizeEdge();
							// TODO Duplicator must have a choice at this point
							final Vertex<LETTER, STATE> destination = summarizeEdge.getDestination();
							int summarizeEdgePriority = summarizeEdge.getPriority();
							if (summarizeEdgePriority == SummarizeEdge.NO_PRIORITY) {
								// If summarize edge has no priority yet, use
								// the neutral element 2.
								summarizeEdgePriority = 2;
							}
							final Integer destinationSearchPriority = searchPriorities
									.get(new Pair<>(destination, searchTarget));
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
						} else if (transitionType == ETransitionType.CALL) {
							// Left down state changes by using
							// 'spoiler -call-> duplicator'
							final VertexDownState<STATE> downState = new VertexDownState<>(searchVertex.getQ0(),
									searchDownState.getRightDownState());
							final Integer succSearchPriority = searchPriorities.get(new Pair<>(succ, downState));
							if (succSearchPriority == null || succSearchPriority == SummarizeEdge.NO_PRIORITY) {
								continue;
							}
							succPriority = succSearchPriority;
						} else {
							final Integer succSearchPriority = searchPriorities.get(new Pair<>(succ, searchTarget));
							if (succSearchPriority == null || succSearchPriority == SummarizeEdge.NO_PRIORITY) {
								continue;
							}
							succPriority = succSearchPriority;
						}
					} else {
						// Successor is spoiler vertex
						if (isSearchVertexDuplicatorNwa) {
							final ETransitionType transitionType = searchVertexAsDuplicatorNwa.getTransitionType();
							if (transitionType == ETransitionType.RETURN || transitionType == ETransitionType.SINK
									|| transitionType == ETransitionType.SUMMARIZE_ENTRY
									|| transitionType == ETransitionType.SUMMARIZE_EXIT) {
								// Ignore return and special edges
								break;
							} else if (transitionType == ETransitionType.CALL) {
								// Right down state changes by using
								// 'duplicator -call-> spoiler'
								final VertexDownState<STATE> downState = new VertexDownState<>(
										searchDownState.getLeftDownState(), searchVertex.getQ1());
								final Integer succSearchPriority = searchPriorities.get(new Pair<>(succ, downState));
								if (succSearchPriority == null || succSearchPriority == SummarizeEdge.NO_PRIORITY) {
									continue;
								}
								succPriority = succSearchPriority;
							} else {
								final Integer succSearchPriority = searchPriorities.get(new Pair<>(succ, searchTarget));
								if (succSearchPriority == null || succSearchPriority == SummarizeEdge.NO_PRIORITY) {
									continue;
								}
								succPriority = succSearchPriority;
							}
						}
					}
					// Evaluate the priority of the current successor
					// Differentiate between non-loop and loop vertices
					if (!loopDetector.isLoopVertex(succ, searchSummarizeEdge.getSpoilerInvoker(), searchVertex)) {
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
			final Integer previousSearchPriorityValue = searchPriorities.put(new Pair<>(searchVertex, searchTarget),
					searchPriority);
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
				// summarize edges, if existent.
				if (isSearchVertexDuplicatorNwa) {
					final ETransitionType transitionType = searchVertexAsDuplicatorNwa.getTransitionType();
					if (transitionType == ETransitionType.CALL) {
						updateCorrespondingSummarizeEdge(searchElement, searchPriority);
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
							final DuplicatorNwaVertex<LETTER, STATE> predAsDuplicatorNwa = (DuplicatorNwaVertex<LETTER, STATE>) pred;
							final ETransitionType transitionType = predAsDuplicatorNwa.getTransitionType();
							if (transitionType == ETransitionType.RETURN || transitionType == ETransitionType.SINK
									|| transitionType == ETransitionType.SUMMARIZE_ENTRY) {
								// Ignore return and special edges
								continue;
							} else if (transitionType == ETransitionType.CALL) {
								// Right down state changes by using
								// 'duplicator -call-> spoiler'
								final VertexDownState<STATE> downState = predAsDuplicatorNwa.getVertexDownState();
								// Create a search element for corresponding
								// correct double decker.
								if (downState.getLeftDownState().equals(searchDownState.getLeftDownState())) {
									final SummarizeEdge<LETTER, STATE> correspondingEdge = SearchElement
											.computeSummarizeEdge(pred, downState, searchSummarizeEdge,
													invokerToSummarizeEdge);
									searchQueue.add(new SearchElement<LETTER, STATE>(pred, downState, searchDownState,
											correspondingEdge));
								}
							} else if (transitionType == ETransitionType.SUMMARIZE_EXIT) {
								// Follow summarize edge to the source and use
								// this vertex if the edge belongs to the
								// current down state configuration
								final Vertex<LETTER, STATE> source = predAsDuplicatorNwa.getSummarizeEdge().getSource();
								if (source instanceof SpoilerNwaVertex) {
									final SpoilerNwaVertex<LETTER, STATE> sourceAsSpoilerNwa = (SpoilerNwaVertex<LETTER, STATE>) source;
									if (sourceAsSpoilerNwa.hasVertexDownState(searchDownState)) {
										searchQueue.add(new SearchElement<LETTER, STATE>(source, searchDownState,
												searchDownState, searchSummarizeEdge));
									}
								}
							} else {
								// Only add the vertex if the edge belongs to
								// the current down state configuration
								if (predAsDuplicatorNwa.hasVertexDownState(searchDownState)) {
									searchQueue.add(new SearchElement<LETTER, STATE>(pred, searchDownState,
											searchDownState, searchSummarizeEdge));
								}
							}
						} else {
							// Predecessor is spoiler vertex
							if (isSearchVertexDuplicatorNwa) {
								final ETransitionType transitionType = searchVertexAsDuplicatorNwa.getTransitionType();
								if (transitionType == ETransitionType.RETURN || transitionType == ETransitionType.SINK
										|| transitionType == ETransitionType.SUMMARIZE_ENTRY
										|| transitionType == ETransitionType.SUMMARIZE_EXIT) {
									// Ignore return and special edges
									break;
								} else if (transitionType == ETransitionType.CALL) {
									if (pred instanceof SpoilerNwaVertex) {
										final SpoilerNwaVertex<LETTER, STATE> predAsSpoilerNwa = (SpoilerNwaVertex<LETTER, STATE>) pred;
										// Left down state changes by using
										// 'spoiler -call-> duplicator'
										final VertexDownState<STATE> downState = predAsSpoilerNwa.getVertexDownState();
										// Create a search element for
										// corresponding correct double decker.
										if (downState.getRightDownState().equals(searchDownState.getRightDownState())) {
											final SummarizeEdge<LETTER, STATE> correspondingEdge = SearchElement
													.computeSummarizeEdge(pred, downState, searchSummarizeEdge,
															invokerToSummarizeEdge);
											searchQueue.add(new SearchElement<LETTER, STATE>(pred, downState,
													searchDownState, correspondingEdge));
										}
									}
								} else {
									// Only add the vertex if the edge belongs
									// to the current down state configuration
									if (pred instanceof SpoilerNwaVertex) {
										final SpoilerNwaVertex<LETTER, STATE> predAsSpoilerDD = (SpoilerNwaVertex<LETTER, STATE>) pred;
										if (predAsSpoilerDD.hasVertexDownState(searchDownState)) {
											searchQueue.add(new SearchElement<LETTER, STATE>(pred, searchDownState,
													searchDownState, searchSummarizeEdge));
										}
									}
								}
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
		if (searchCounter.compareTo(maxAmountOfSearches) > 0) {
			throw new IllegalStateException(
					"Computing summarize edge priorities could not be done. The process detected a live lock and aborted.");
		}
		*/
	}

	/**
	 * Generates a possible reduced nwa automaton by using the current state of
	 * the game graph that may hold information, usable for reduction, generated
	 * by an {@link ASimulation}.
	 * 
	 * @return A possible reduced nwa automaton
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public INestedWordAutomatonOldApi<LETTER, STATE> generateAutomatonFromGraph()
			throws AutomataOperationCanceledException {
		final FairGameGraph<LETTER, STATE> fairGraph = castGraphToFairGameGraph();

		// By default, we assume that there are merge-able states.
		boolean areThereMergeableStates = true;
		if (fairGraph != null) {
			// For fair simulation, we know if there are such states.
			areThereMergeableStates = fairGraph.areThereMergeableStates();
		}
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

		final StateFactory<STATE> stateFactory = mNwa.getStateFactory();
		INestedWordAutomatonOldApi<LETTER, STATE> result = null;

		// Merge states
		if (areThereMergeableStates) {
			// Equivalence class that holds all state classes
			// with their representatives
			UnionFind<STATE> equivalenceClasses;

			if (fairGraph != null) {
				// For fair simulation, this was already set up.
				equivalenceClasses = fairGraph.getEquivalenceClasses();
			} else {
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
					// For delayed simulation we need to choose between the
					// vertex with bit set to true or false
					// TODO Reevaluate this regarding simulation with matched
					// return words
					if (mSimulationType == ESimulationType.DELAYED) {
						if (v.isB()) {
							considerVertex = mNwa.isFinal(state1) && !mNwa.isFinal(state2);
						} else {
							considerVertex = !mNwa.isFinal(state1) || mNwa.isFinal(state2);
						}
					}
					if (considerVertex && state1 != null && state2 != null) {
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
			}

			Collection<Set<STATE>> equivalenceClassesAsCollection = equivalenceClasses.getAllEquivalenceClasses();

			// Use a Max-Sat-Solver that minimizes the automaton based on
			// our simulation results
			mSimulationPerformance.startTimeMeasure(ETimeMeasure.SOLVE_MAX_SAT);
			MinimizeNwaMaxSat2<LETTER, STATE> minimizer = new MinimizeNwaMaxSat2<>(mServices, stateFactory, mNwa, false,
					false, equivalenceClassesAsCollection);
			mSimulationPerformance.stopTimeMeasure(ETimeMeasure.SOLVE_MAX_SAT);
			result = new RemoveUnreachable<LETTER, STATE>(mServices, minimizer.getResult()).getResult();

			mResultAmountOfStates = result.size();
			// TODO One of the operations should provide a #transition method,
			// counting it manually is a, for metrics only, not acceptable
			// overhead.
			// Count transitions
			for (STATE state : result.getStates()) {
				for (@SuppressWarnings("unused")
				OutgoingInternalTransition<LETTER, STATE> internalTrans : result.internalSuccessors(state)) {
					increaseResultAmountOfTransitions();
				}
				for (@SuppressWarnings("unused")
				OutgoingCallTransition<LETTER, STATE> callTrans : result.callSuccessors(state)) {
					increaseResultAmountOfTransitions();
				}
				for (@SuppressWarnings("unused")
				OutgoingReturnTransition<LETTER, STATE> returnTrans : result.returnSuccessors(state)) {
					increaseResultAmountOfTransitions();
				}

				if (mProgressTimer != null && !mProgressTimer.continueProcessing()) {
					mLogger.debug("Stopped in generateBuchiAutomatonFromGraph/counting");
					throw new AutomataOperationCanceledException(this.getClass());
				}
			}
		} else {
			// If there is no merge-able state simply
			// copy the inputed automaton
			NestedWordAutomaton<LETTER, STATE> resultAsChangeableAutomaton = new NestedWordAutomaton<>(mServices,
					mNwa.getInternalAlphabet(), mNwa.getCallAlphabet(), mNwa.getReturnAlphabet(), stateFactory);
			for (final STATE state : mNwa.getStates()) {
				// Copy states
				final boolean isInitial = mNwa.isInitial(state);
				final boolean isFinal = mNwa.isFinal(state);
				resultAsChangeableAutomaton.addState(isInitial, isFinal, state);
				increaseResultAmountOfStates();

				// Copy transitions
				for (OutgoingInternalTransition<LETTER, STATE> internalTrans : mNwa.internalSuccessors(state)) {
					resultAsChangeableAutomaton.addInternalTransition(state, internalTrans.getLetter(),
							internalTrans.getSucc());
					increaseResultAmountOfTransitions();
				}
				for (OutgoingCallTransition<LETTER, STATE> callTrans : mNwa.callSuccessors(state)) {
					resultAsChangeableAutomaton.addCallTransition(state, callTrans.getLetter(), callTrans.getSucc());
					increaseResultAmountOfTransitions();
				}
				for (OutgoingReturnTransition<LETTER, STATE> returnTrans : mNwa.returnSuccessors(state)) {
					resultAsChangeableAutomaton.addReturnTransition(state, returnTrans.getHierPred(),
							returnTrans.getLetter(), returnTrans.getSucc());
					increaseResultAmountOfTransitions();
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
			final NestedWordAutomatonReachableStates<LETTER, STATE> nwaReachableStates = new RemoveUnreachable<LETTER, STATE>(
					mServices, result).getResult();
			return nwaReachableStates;
		} else {
			return result;
		}
	}

	/**
	 * Generates the game graph out of an original nwa automaton. The graph
	 * represents a game, see {@link AGameGraph}.
	 * 
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public void generateGameGraphFromAutomaton() throws AutomataOperationCanceledException {
		mSimulationPerformance.startTimeMeasure(ETimeMeasure.BUILD_GRAPH);

		generateVertices();
		generateRegularEdges();
		patchGraph();

		mSimulationPerformance.startTimeMeasure(ETimeMeasure.GENERATE_SUMMARIZE_EDGES);
		generateSummarizeEdges();
		mSimulationPerformance.stopTimeMeasure(ETimeMeasure.GENERATE_SUMMARIZE_EDGES);

		mSimulationPerformance.startTimeMeasure(ETimeMeasure.COMPUTE_SUMMARIZE_EDGE_PRIORITIES);
		computeSummarizeEdgePriorities();
		mSimulationPerformance.stopTimeMeasure(ETimeMeasure.COMPUTE_SUMMARIZE_EDGE_PRIORITIES);

		clear();

		mSimulationPerformance.stopTimeMeasure(ETimeMeasure.BUILD_GRAPH);
	}

	/**
	 * Generates the regular edges of the game graph from the input automaton.
	 * 
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public void generateRegularEdges() throws AutomataOperationCanceledException {
		mLogger.debug("Generating regular edges.");
		for (final STATE edgeDest : mNwa.getStates()) {
			// Edges generated by internal transitions
			for (final IncomingInternalTransition<LETTER, STATE> trans : mNwa.internalPredecessors(edgeDest)) {
				for (final STATE fixState : mNwa.getStates()) {
					// Duplicator edges q1 -a-> q2 : (x, q1, a) -> (x, q2)
					Vertex<LETTER, STATE> duplicatorSrc = getDuplicatorVertex(fixState, trans.getPred(),
							trans.getLetter(), false, ETransitionType.INTERNAL, null, null);
					Vertex<LETTER, STATE> spoilerDest = getSpoilerVertex(fixState, edgeDest, false, null, null);
					if (duplicatorSrc != null && spoilerDest != null) {
						addEdge(duplicatorSrc, spoilerDest);
					}

					// For delayed simulation we also need to account for
					// source vertices with the bit set to true
					if (mSimulationType == ESimulationType.DELAYED) {
						duplicatorSrc = getDuplicatorVertex(fixState, trans.getPred(), trans.getLetter(), true,
								ETransitionType.INTERNAL, null, null);
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
							false, ETransitionType.INTERNAL, null, null);
					if (spoilerSrc != null) {
						// In delayed simulation the destination needs to have
						// the bit set to true if Spoilers destination is final
						if (mSimulationType == ESimulationType.DELAYED && mNwa.isFinal(edgeDest)) {
							duplicatorDest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), true,
									ETransitionType.INTERNAL, null, null);
						}
						if (duplicatorDest != null) {
							addEdge(spoilerSrc, duplicatorDest);
						}
					}

					// For delayed simulation we also need to account for
					// source vertices with the bit set to true
					if (mSimulationType == ESimulationType.DELAYED) {
						spoilerSrc = getSpoilerVertex(trans.getPred(), fixState, true, null, null);
						duplicatorDest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), true,
								ETransitionType.INTERNAL, null, null);
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
							trans.getLetter(), false, ETransitionType.CALL, null, null);
					Vertex<LETTER, STATE> spoilerDest = getSpoilerVertex(fixState, edgeDest, false, null, null);
					if (duplicatorSrc != null && spoilerDest != null) {
						addEdge(duplicatorSrc, spoilerDest);
					}

					// For delayed simulation we also need to account for
					// source vertices with the bit set to true
					if (mSimulationType == ESimulationType.DELAYED) {
						duplicatorSrc = getDuplicatorVertex(fixState, trans.getPred(), trans.getLetter(), true,
								ETransitionType.CALL, null, null);
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
							false, ETransitionType.CALL, null, null);
					if (spoilerSrc != null) {
						// In delayed simulation the destination needs to have
						// the bit set to true if Spoilers destination is final
						if (mSimulationType == ESimulationType.DELAYED && mNwa.isFinal(edgeDest)) {
							duplicatorDest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), true,
									ETransitionType.CALL, null, null);
						}
						if (duplicatorDest != null) {
							addEdge(spoilerSrc, duplicatorDest);
						}
					}

					// For delayed simulation we also need to account for
					// source vertices with the bit set to true
					if (mSimulationType == ESimulationType.DELAYED) {
						spoilerSrc = getSpoilerVertex(trans.getPred(), fixState, true, null, null);
						duplicatorDest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), true,
								ETransitionType.CALL, null, null);
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
							trans.getLetter(), false, ETransitionType.RETURN, null, null);
					Vertex<LETTER, STATE> spoilerDest = getSpoilerVertex(fixState, edgeDest, false, null, null);
					if (duplicatorSrc != null && spoilerDest != null) {
						addEdge(duplicatorSrc, spoilerDest);
					}

					// For delayed simulation we also need to account for
					// source vertices with the bit set to true
					if (mSimulationType == ESimulationType.DELAYED) {
						duplicatorSrc = getDuplicatorVertex(fixState, trans.getLinPred(), trans.getLetter(), true,
								ETransitionType.RETURN, null, null);
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
					Vertex<LETTER, STATE> spoilerSrc = getSpoilerVertex(trans.getLinPred(), fixState, false, null,
							null);
					Vertex<LETTER, STATE> duplicatorDest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(),
							false, ETransitionType.RETURN, null, null);
					if (spoilerSrc != null) {
						// In delayed simulation the destination needs to have
						// the bit set to true if Spoilers destination is final
						if (mSimulationType == ESimulationType.DELAYED && mNwa.isFinal(edgeDest)) {
							duplicatorDest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), true,
									ETransitionType.RETURN, null, null);
						}
						if (duplicatorDest != null) {
							addEdge(spoilerSrc, duplicatorDest);
						}
					}

					// For delayed simulation we also need to account for
					// vertices with the bit set to true
					if (mSimulationType == ESimulationType.DELAYED) {
						spoilerSrc = getSpoilerVertex(trans.getLinPred(), fixState, true, null, null);
						duplicatorDest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), true,
								ETransitionType.RETURN, null, null);
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
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public void generateSummarizeEdges() throws AutomataOperationCanceledException {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Generating summarize edges.");
		}
		// Create the game automaton, we will use it for summarize computation
		NestedWordAutomaton<GameLetter<LETTER, STATE>, IGameState> gameAutomaton = createGameAutomaton();
		NestedWordAutomatonReachableStates<GameLetter<LETTER, STATE>, IGameState> gameAutomatonWithSummaries = new RemoveUnreachable<>(
				mServices, gameAutomaton).getResult();

		// Retrieve all single summary edge sources
		Set<IGameState> summarySources = new HashSet<>();
		for (SpoilerVertex<LETTER, STATE> spoilerVertex : mGameGraph.getSpoilerVertices()) {
			if (!(spoilerVertex instanceof SpoilerNwaVertex<?, ?>)) {
				continue;
			}
			SpoilerNwaVertex<LETTER, STATE> spoilerNwaVertex = (SpoilerNwaVertex<LETTER, STATE>) spoilerVertex;
			GameSpoilerNwaVertex<LETTER, STATE> gameNwaVertex = new GameSpoilerNwaVertex<>(spoilerNwaVertex);

			Iterable<SummaryReturnTransition<GameLetter<LETTER, STATE>, IGameState>> summariesOfSource = gameAutomatonWithSummaries
					.returnSummarySuccessor(gameNwaVertex);
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
		// Retrieve the merged summary edges for the game graph that start at
		// the given source.
		// We make all summarySources the only initial game states and determinize
		// the automaton.

		// Determinizing is very expensive, it is the dominant part of the
		// whole algorithm
		INestedWordAutomatonOldApi<GameLetter<LETTER, STATE>, IGameState> determinizedGameAutomaton = new Determinize<GameLetter<LETTER, STATE>, IGameState>(
				mServices, gameAutomatonWithSummaries.getStateFactory(), gameAutomatonWithSummaries, summarySources)
						.getResult();
		mSimulationPerformance.setCountingMeasure(ECountingMeasure.DETERMINIZED_GAME_AUTOMATON_STATES,
				determinizedGameAutomaton.size());
		NestedWordAutomatonReachableStates<GameLetter<LETTER, STATE>, IGameState> gameAutomatonWithMergedSummaries = new RemoveUnreachable<>(
				mServices, determinizedGameAutomaton).getResult();
		IGameState emptyStackState = gameAutomatonWithMergedSummaries.getEmptyStackState();

		// The initial game states are the source of
		// the summary edges we are interested in
		for (IGameState mergedSummarySourceAsGameState : gameAutomatonWithMergedSummaries.getInitialStates()) {
			if (!(mergedSummarySourceAsGameState instanceof GameDoubleDeckerSet)) {
				throw new IllegalStateException(
						"Expected cast possible, something seems to be wrong with the game graph.");
			}
			GameDoubleDeckerSet mergedSummarySourceDDSet = (GameDoubleDeckerSet) mergedSummarySourceAsGameState;

			// We are only interested in sources where the down state is the
			// empty stack symbol
			Set<IGameState> mergedSummarySourceUpStates = mergedSummarySourceDDSet.getUpStates(emptyStackState);
			if (mergedSummarySourceUpStates.size() > 1) {
				throw new IllegalStateException(
						"Expected only one up state after determizing the game automaton at summary sources.");
			}
			IGameState mergedSummarySourceUpStateAsGameState = mergedSummarySourceUpStates.iterator().next();
			if (!(mergedSummarySourceUpStateAsGameState instanceof GameSpoilerNwaVertex<?, ?>)) {
				throw new IllegalStateException(
						"Expected cast possible, something seems to be wrong with the game graph.");
			}
			@SuppressWarnings("unchecked")
			SpoilerNwaVertex<LETTER, STATE> mergedSummarySource = ((GameSpoilerNwaVertex<LETTER, STATE>) mergedSummarySourceUpStateAsGameState)
					.getSpoilerNwaVertex();

			Map<STATE, Set<STATE>> spoilerToDuplicatorChoices = new HashMap<>();
			boolean runsInDuplicatorDeadEnd = false;
			// Collect all summary edges
			for (SummaryReturnTransition<GameLetter<LETTER, STATE>, IGameState> summary : gameAutomatonWithMergedSummaries
					.returnSummarySuccessor(mergedSummarySourceAsGameState)) {
				IGameState summaryDestinationAsGameState = summary.getSucc();
				GameDoubleDeckerSet summaryDestinationAsDD = (GameDoubleDeckerSet) summaryDestinationAsGameState;
				Set<IGameState> summaryDestinationUpStates = summaryDestinationAsDD.getUpStates(emptyStackState);

				// If the destination up states are null, then the destination
				// is empty. This is the case if the source is not total,
				// because Determinize makes the automaton total. We can just
				// ignore this event and continue.
				if (summaryDestinationUpStates == null) {
					continue;
				}
				
				for (IGameState summaryDestinationUpState : summaryDestinationUpStates) {
					if (summaryDestinationUpState.equals(mAuxiliaryGameState)) {
						runsInDuplicatorDeadEnd = true;
						continue;
					}
					
					@SuppressWarnings("unchecked")
					SpoilerNwaVertex<LETTER, STATE> summaryDestination = ((GameSpoilerNwaVertex<LETTER, STATE>) summaryDestinationUpState)
							.getSpoilerNwaVertex();
					// Add the summary to Duplicators choices for this
					// merged summary
					STATE spoilerTarget = summaryDestination.getQ0();
					STATE duplicatorTarget = summaryDestination.getQ1();
					if (!spoilerToDuplicatorChoices.containsKey(spoilerTarget)) {
						spoilerToDuplicatorChoices.put(spoilerTarget, new LinkedHashSet<>());
					}
					Set<STATE> choices = spoilerToDuplicatorChoices.get(spoilerTarget);
					choices.add(duplicatorTarget);
					spoilerToDuplicatorChoices.put(spoilerTarget, choices);
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
				addSpoilerWinningSinkExtended((SpoilerNwaVertex<LETTER, STATE>) mergedSummarySource);
			}
			// Create and add the merged summaries
			for (Entry<STATE, Set<STATE>> choiceEntry : spoilerToDuplicatorChoices.entrySet()) {
				STATE spoilerChoice = choiceEntry.getKey();
				addSummarizeEdge((SpoilerNwaVertex<LETTER, STATE>) mergedSummarySource, spoilerChoice,
						choiceEntry.getValue());
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
						final SpoilerNwaVertex<LETTER, STATE> preAsNwa = (SpoilerNwaVertex<LETTER, STATE>) pred;
						addDuplicatorWinningSink(preAsNwa);
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
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public void generateVertices() throws AutomataOperationCanceledException {
		mLogger.debug("Generating vertices.");
		int duplicatorPriority = DUPLICATOR_PRIORITY;

		for (final STATE leftState : mNwa.getStates()) {
			for (final STATE rightState : mNwa.getStates()) {
				// Generate Spoiler vertices (leftState, rightState)
				final int priority = calculatePriority(leftState, rightState);

				// In delayed simulation we always generate the vertex with
				// priority zero. Conditionally we also add a vertex with
				// priority one.
				if (mSimulationType == ESimulationType.DELAYED) {
					addSpoilerVertexHelper(0, false, leftState, rightState);
				} else {
					addSpoilerVertexHelper(priority, false, leftState, rightState);
				}

				// In delayed simulation we may also add a vertex with
				// priority one that has the bit set to true.
				if (mSimulationType == ESimulationType.DELAYED) {
					if (priority == 1) {
						addSpoilerVertexHelper(1, true, leftState, rightState);
					}
				}

				// Generate Duplicator vertices (leftState, rightState, letter)
				// Vertices generated by internal transitions
				for (final LETTER letter : mNwa.lettersInternalIncoming(leftState)) {
					addDuplicatorVertexHelper(duplicatorPriority, false, leftState, rightState, letter,
							ETransitionType.INTERNAL);
					if (mSimulationType == ESimulationType.DELAYED) {
						addDuplicatorVertexHelper(duplicatorPriority, true, leftState, rightState, letter,
								ETransitionType.INTERNAL);
					}
				}
				// Vertices generated by call transitions
				for (final LETTER letter : mNwa.lettersCallIncoming(leftState)) {
					addDuplicatorVertexHelper(duplicatorPriority, false, leftState, rightState, letter,
							ETransitionType.CALL);
					if (mSimulationType == ESimulationType.DELAYED) {
						addDuplicatorVertexHelper(duplicatorPriority, true, leftState, rightState, letter,
								ETransitionType.CALL);
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
								transition.getLetter(), ETransitionType.RETURN);
						if (mSimulationType == ESimulationType.DELAYED) {
							addDuplicatorVertexHelper(duplicatorPriority, true, leftState, rightState,
									transition.getLetter(), ETransitionType.RETURN);
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

			// Generate an equivalence class for every state from
			// the nwa automaton, if fair simulation
			makeEquivalenceClass(leftState);
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
	 *            Summarize edge the vertex belongs to if the transition is of
	 *            type {@link ETransitionType#SUMMARIZE_ENTRY} or
	 *            {@link ETransitionType#SUMMARIZE_EXIT}. Use <tt>null</tt> if
	 *            that is not the case.
	 * @param sink
	 *            Sink the vertex belongs to if the transition is of type
	 *            {@link ETransitionType#SINK}. Use <tt>null</tt> if that is not
	 *            the case.
	 * @return The duplicator vertex associated to the given signature. See
	 *         {@link #getDuplicatorVertex(Object, Object, Object, boolean)}.
	 */
	public DuplicatorVertex<LETTER, STATE> getDuplicatorVertex(final STATE q0, final STATE q1, final LETTER a,
			final boolean bit, final ETransitionType transType, final SummarizeEdge<LETTER, STATE> summarizeEdge,
			final DuplicatorWinningSink<LETTER, STATE> sink) {
		return mAutomatonStatesToGraphDuplicatorVertex.get(new Hep<>(q0, q1, a, bit, transType, summarizeEdge, sink));
	}

	/**
	 * Gets the changes that where made for removing return vertices and their
	 * edges. It includes the removed returning vertex, its out- and in-going
	 * edges and generated push-over edges.
	 * 
	 * @return The changes that where made for removing return vertices and
	 *         their edges.
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
	 * Gets a Spoiler vertex by its signature. See
	 * {@link #getSpoilerVertex(Object, Object, boolean)}.
	 * 
	 * @param q0
	 *            Left state
	 * @param q1
	 *            Right state
	 * @param bit
	 *            Extra bit of the vertex
	 * @param summarizeEdge
	 *            Summarize edge the vertex belongs to. Use <tt>null</tt> if the
	 *            vertex does not belong to one. This is used for special
	 *            vertices that are used to represent a summary edge correctly
	 *            for a valid game graph.
	 * @param sink
	 *            Sink the vertex belongs to. Use <tt>null</tt> if the vertex
	 *            does not belong to one. This is used for special vertices that
	 *            are used to represent a sink correctly for a valid game graph.
	 * @return The spoiler vertex associated to the given signature. See
	 *         {@link #getSpoilerVertex(Object, Object, boolean)}.
	 */
	public SpoilerVertex<LETTER, STATE> getSpoilerVertex(final STATE q0, final STATE q1, final boolean bit,
			final SummarizeEdge<LETTER, STATE> summarizeEdge, final DuplicatorWinningSink<LETTER, STATE> sink) {
		return mAutomatonStatesToGraphSpoilerVertex.get(new Quin<>(q0, q1, bit, summarizeEdge, sink));
	}

	/**
	 * Transforms dead ending Spoiler/Duplicator vertices into instant wins for
	 * Duplicator/Spoiler by adding a Duplicator/Spoiler-Winning-Sink. Such
	 * vertices may occur if they can not use a return-transition due to their
	 * down state and if no other transitions are available.<br/>
	 * <br/>
	 * In direct simulation it correctly takes care of spoiler vertices that are
	 * directly loosing for Duplicator. Such vertices need to form a legal win
	 * for Spoiler though they are dead-ends.
	 * 
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public void patchGraph() throws AutomataOperationCanceledException {
		// Patch Spoiler vertices that are directly losing for Duplicator in
		// direct simulation
		for (SpoilerNwaVertex<LETTER, STATE> spoilerVertex : mDuplicatorDirectlyLosesInSpoiler) {
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
		for (SpoilerNwaVertex<LETTER, STATE> possibleDeadEnd : mPossibleSpoilerDeadEnd) {
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
		for (DuplicatorNwaVertex<LETTER, STATE> possibleDeadEnd : mPossibleNonReturnDuplicatorDeadEnd) {
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
	 * Adds a given transition to the internal field of buechi transitions, if
	 * fair simulation.
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
	 * Generates and adds the duplicator vertex represented by the arguments.
	 * Also possibly adds the vertex to some data structures.
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
	 */
	private void addDuplicatorVertexHelper(final int priority, final boolean bit, final STATE leftState,
			final STATE rightState, final LETTER letter, final ETransitionType type) {

		// For returning duplicator vertices, it may often be requested to
		// add existent vertices again. This may cause problems, because of
		// that we check it.
		if (type != ETransitionType.RETURN
				|| (getDuplicatorVertex(leftState, rightState, letter, bit, type, null, null) == null)) {
			DuplicatorNwaVertex<LETTER, STATE> duplicatorVertex = new DuplicatorNwaVertex<>(priority, bit, leftState,
					rightState, letter, type);
			addDuplicatorVertex(duplicatorVertex);

			// Memorize vertices that possible end up as dead-ends because they
			// can not take a transition.
			// Such vertices need to form a instant win for Spoiler.
			boolean hasSuccessors = true;
			if (type.equals(ETransitionType.INTERNAL)) {
				hasSuccessors = mNwa.internalSuccessors(rightState, letter).iterator().hasNext();
			} else if (type.equals(ETransitionType.CALL)) {
				hasSuccessors = mNwa.callSuccessors(rightState, letter).iterator().hasNext();
			} else if (type.equals(ETransitionType.RETURN)) {
				hasSuccessors = mNwa.returnSuccessors(rightState, letter).iterator().hasNext();

				// Memorize Duplicator Return vertices, we later need it for
				// summarize edge generation.
				mDuplicatorReturningVertices.add(duplicatorVertex);
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("\tAdded to duplicatorReturningVertices: " + duplicatorVertex);
				}
			}
			if (!hasSuccessors) {
				if (!type.equals(ETransitionType.RETURN)) {
					mPossibleNonReturnDuplicatorDeadEnd.add(duplicatorVertex);
					if (mLogger.isDebugEnabled()) {
						mLogger.debug("\tAdded to possibleNonReturnDuplicatorDeadEnd: " + duplicatorVertex);
					}
				}
			}
		}
	}

	/**
	 * Creates and adds a duplicator winning sink to the given sink entry. To
	 * form a valid edge it creates a pair of two states after the entry. In
	 * detail this will be: <b>sinkEntry -> DuplicatorSink -> SpoilerSink ->
	 * DuplicatorSink -> ...</b>. <br/>
	 * <br/>
	 * The SpoilerSink will have a priority of 0 to form a winning vertex for
	 * Duplicator.
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
	private void addEdgeToGameAutomaton(final IGameState src, final GameLetter<LETTER, STATE> letter,
			final IGameState dest, final NestedWordAutomaton<GameLetter<LETTER, STATE>, IGameState> gameAutomaton) {
		ETransitionType transType = letter.getTransitionType();
		if (transType.equals(ETransitionType.INTERNAL)) {
			if (!gameAutomaton.containsInternalTransition(src, letter, dest)) {
				gameAutomaton.addInternalTransition(src, letter, dest);
			}
		} else if (transType.equals(ETransitionType.CALL)) {
			if (!gameAutomaton.containsCallTransition(src, letter, dest)) {
				gameAutomaton.addCallTransition(src, letter, dest);
			}
		} else {
			throw new IllegalArgumentException(
					"The transition type of the game letter is not supported by this operation.");
		}
	}

	/**
	 * Adds a given return edge to the given game automaton, if not already
	 * existent.
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
			final GameLetter<LETTER, STATE> letter, final IGameState dest,
			final NestedWordAutomaton<GameLetter<LETTER, STATE>, IGameState> gameAutomaton) {
		ETransitionType transType = letter.getTransitionType();
		if (transType.equals(ETransitionType.RETURN)) {
			if (!gameAutomaton.containsReturnTransition(src, hierPred, letter, dest)) {
				gameAutomaton.addReturnTransition(src, hierPred, letter, dest);
			}
		} else {
			throw new IllegalArgumentException(
					"The transition type of the game letter is not supported by this operation.");
		}
	}

	/**
	 * Adds a given game state to the given game automaton, if not already
	 * existent. The state will be initial and not final.
	 * 
	 * @param gameState
	 *            Game state to add
	 * @param gameAutomaton
	 *            Game automaton to add to
	 */
	private void addGameStateToGameAutomaton(final IGameState gameState,
			final NestedWordAutomaton<GameLetter<LETTER, STATE>, IGameState> gameAutomaton) {
		if (!gameAutomaton.contains(gameState)) {
			gameAutomaton.addState(true, false, gameState);
		}
	}

	/**
	 * Generates and adds the spoiler vertex represented by the arguments. Also
	 * increases global infinity bound and possibly adds the vertex to some data
	 * structures.
	 * 
	 * @param priority
	 *            Priority of the vertex
	 * @param bit
	 *            Bit of the vertex
	 * @param leftState
	 *            Left state of the vertex
	 * @param rightState
	 *            Right state of the vertex
	 */
	private void addSpoilerVertexHelper(final int priority, final boolean bit, final STATE leftState,
			final STATE rightState) {
		SpoilerNwaVertex<LETTER, STATE> spoilerVertex = new SpoilerNwaVertex<>(priority, bit, leftState, rightState);
		addSpoilerVertex(spoilerVertex);
		// Increase the infinity bound for every such vertex
		if (priority == 1) {
			mGameGraph.increaseGlobalInfinity();
		}

		// Memorize vertices that possible end up as dead-ends because they
		// can not take a return-transition due to their down state.
		// Such vertices need to form a instant win for Duplicator.
		boolean hasInternalSuccessors = mNwa.internalSuccessors(leftState).iterator().hasNext();
		boolean hasCallSuccessors = mNwa.callSuccessors(leftState).iterator().hasNext();
		// Do this in the order of the most unlikely events,
		// reduces computation time
		if (!hasInternalSuccessors) {
			boolean hasReturnSuccessors = mNwa.returnSuccessors(leftState).iterator().hasNext();
			if (!hasReturnSuccessors) {
				if (!hasCallSuccessors) {
					mPossibleSpoilerDeadEnd.add(spoilerVertex);
					if (mLogger.isDebugEnabled()) {
						mLogger.debug("\tAdded to possibleSpoilerDeadEnd: " + spoilerVertex);
					}
				}
			}
		}
		// Memorize Spoiler vertices that are predecessor of Duplicator calling
		// vertices.
		if (hasCallSuccessors) {
			mSpoilerCallPredecessors.add(spoilerVertex);
		}
		// Remember the vertex if direct simulation and it is directly losing
		// for Duplicator
		if (mSimulationType.equals(ESimulationType.DIRECT) && doesLoseInDirectSim(leftState, rightState)) {
			mDuplicatorDirectlyLosesInSpoiler.add(spoilerVertex);
		}
		// Remember the vertex if delayed simulation, the right state is final and the bit is set to true
		if (mSimulationType.equals(ESimulationType.DELAYED) && bit && mNwa.isFinal(rightState)) {
			// Such vertices should end up also being dead ends
			mPossibleSpoilerDeadEnd.add(spoilerVertex);
		}
	}

	/**
	 * Creates and adds a spoiler winning sink to the given sink entry. To form
	 * a valid edge it creates a pair of two states after the entry. In detail
	 * this will be: <b>sinkEntry -> SpoilerSink -> DuplicatorSink ->
	 * SpoilerSink -> ...</b>. <br/>
	 * <br/>
	 * The SpoilerSink will have a priority of 1 to form a winning vertex for
	 * Spoiler.
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
	 * Creates and adds a spoiler winning sink to the given sink entry. To form
	 * a valid edge it creates a pair of two states after the entry. In detail
	 * this will be: <b>sinkEntry -> DuplicatorSink -> SpoilerSink ->
	 * DuplicatorSink -> ...</b>. <br/>
	 * <br/>
	 * The SpoilerSink will have a priority of 1 to form a winning vertex for
	 * Spoiler.
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
	 * Creates and adds a summarize edge with given source and destinations.
	 * <br/>
	 * <br/>
	 * The sub-summarize edges will have no priority by default, it must be
	 * taken care of this afterwards.
	 * 
	 * @param src
	 *            Source of the summarize edge
	 * @param spoilerChoice
	 *            The choice Spoiler did take for this summarize edge
	 * @param duplicatorChoices
	 *            Choices Duplicator can make, determine the sub-summarize edges
	 * @param map
	 *            The Spoiler vertex that invoked creating this summarize edge.
	 *            This is the predecessor of the Duplicator returning vertex.
	 */
	private void addSummarizeEdge(final SpoilerNwaVertex<LETTER, STATE> src, final STATE spoilerChoice,
			final Set<STATE> duplicatorChoices) {
		// TODO We may need invoker information for correct priority search. We
		// also might be able to revert returningBridgeRemoval and then do the
		// search.
		// Only add if not already existent
		if (mSrcDestToSummarizeEdges.get(src, new Pair<>(spoilerChoice, duplicatorChoices)) == null) {
			final SummarizeEdge<LETTER, STATE> summarizeEdge = new SummarizeEdge<>(src, spoilerChoice,
					duplicatorChoices, this);
			summarizeEdge.addToGameGraph();
			mSrcDestToSummarizeEdges.put(src, new Pair<>(spoilerChoice, duplicatorChoices), summarizeEdge);

			mSimulationPerformance.increaseCountingMeasure(ECountingMeasure.SUMMARIZE_EDGES);
			int currentAmountOfSubSummarize = mSimulationPerformance
					.getCountingMeasureResult(ECountingMeasure.SUB_SUMMARIZE_EDGES);
			if (currentAmountOfSubSummarize == SimulationPerformance.NO_COUNTING_RESULT) {
				currentAmountOfSubSummarize = 0;
			}
			mSimulationPerformance.setCountingMeasure(ECountingMeasure.SUB_SUMMARIZE_EDGES,
					currentAmountOfSubSummarize + duplicatorChoices.size());

			if (mLogger.isDebugEnabled()) {
				mLogger.debug("\tAdded summarizeEdge: " + src + " -" + spoilerChoice + "-> " + duplicatorChoices);
			}
		}
	}

	/**
	 * Calculates the priority of a given {@link SpoilerVertex} by its
	 * representation <i>(state spoiler is at, state duplicator is at)</i>.<br/>
	 * Note that {@link DuplicatorVertex} objects always should have priority of
	 * {@link #DUPLICATOR_PRIORITY}.
	 * 
	 * @param leftState
	 *            The state spoiler is at
	 * @param rightState
	 *            The state duplicator is at
	 * @return The calculated priority of the given {@link SpoilerVertex} which
	 *         is 0 if the right state is final, 2 if both are final and 1 if
	 *         only the left state is final.
	 */
	private int calculatePriority(final STATE leftState, final STATE rightState) {
		// In direct simulation, every vertex has zero as priority
		if (mSimulationType == ESimulationType.DIRECT) {
			return 0;
		}

		// In delayed simulation priority zero is always possible, only priority
		// one is conditional. In this case, this method should only return one
		// if possible, else zero.
		if (mSimulationType == ESimulationType.DELAYED) {
			if (!mNwa.isFinal(rightState)) {
				return 1;
			} else {
				return 0;
			}
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
	 * @return The graph casted to a fair game graph, <tt>null</tt> if not
	 *         possible.
	 */
	private FairGameGraph<LETTER, STATE> castGraphToFairGameGraph() {
		FairGameGraph<LETTER, STATE> fairGraph = null;
		if (mGameGraph instanceof FairGameGraph<?, ?>) {
			fairGraph = (FairGameGraph<LETTER, STATE>) mGameGraph;
		}
		return fairGraph;
	}

	/**
	 * Computes all hierPreds for a game automaton, given the source and
	 * destination for both players as SpoilerVertex.
	 * 
	 * @param src
	 *            Source of both players
	 * @param dest
	 *            Destination of both players
	 * @param returnLetter
	 *            Letter used for returning
	 * @return
	 */
	private Iterable<GameSpoilerNwaVertex<LETTER, STATE>> computeAllGameHierPreds(
			final SpoilerVertex<LETTER, STATE> src, final SpoilerVertex<LETTER, STATE> dest,
			final LETTER returnLetter) {
		return computeAllGameHierPreds(src.getQ0(), src.getQ1(), dest.getQ0(), dest.getQ1(), returnLetter);
	}

	/**
	 * Computes all hierPreds for a game automaton, given the source and
	 * destination for both players.
	 * 
	 * @param spoilerSrc
	 *            Source of Spoiler
	 * @param duplicatorSrc
	 *            Source of Duplicator
	 * @param spoilerDest
	 *            Destination of Spoiler
	 * @param duplicatorDest
	 *            Destination of Duplicator
	 * @param returnLetter
	 *            Letter used for returning
	 * @return
	 */
	private Iterable<GameSpoilerNwaVertex<LETTER, STATE>> computeAllGameHierPreds(final STATE spoilerSrc,
			final STATE duplicatorSrc, final STATE spoilerDest, final STATE duplicatorDest, final LETTER returnLetter) {
		Set<GameSpoilerNwaVertex<LETTER, STATE>> gameHierPreds = new LinkedHashSet<>();
		Set<STATE> spoilerHierPreds = new HashSet<>();
		Set<STATE> duplicatorHierPreds = new HashSet<>();

		// Retrieve hierPred of Spoiler
		for (OutgoingReturnTransition<LETTER, STATE> spoilerReturnTrans : mNwa.returnSuccessors(spoilerSrc,
				returnLetter)) {
			if (spoilerReturnTrans.getSucc().equals(spoilerDest)) {
				spoilerHierPreds.add(spoilerReturnTrans.getHierPred());
			}
		}
		// Retrieve hierPred of Duplicator
		for (OutgoingReturnTransition<LETTER, STATE> duplicatorReturnTrans : mNwa.returnSuccessors(duplicatorSrc,
				returnLetter)) {
			if (duplicatorReturnTrans.getSucc().equals(duplicatorDest)) {
				duplicatorHierPreds.add(duplicatorReturnTrans.getHierPred());
			}
		}
		// Merge both sets
		for (STATE spoilerHierPred : spoilerHierPreds) {
			for (STATE duplicatorHierPred : duplicatorHierPreds) {
				SpoilerVertex<LETTER, STATE> representingHierPred = getSpoilerVertex(spoilerHierPred,
						duplicatorHierPred, false, null, null);
				if (representingHierPred instanceof SpoilerNwaVertex<?, ?>) {
					gameHierPreds
							.add(new GameSpoilerNwaVertex<>((SpoilerNwaVertex<LETTER, STATE>) representingHierPred));
				}
				// In delayed simulation we also need to account for the bit set to true
				if (mSimulationType.equals(ESimulationType.DELAYED)) {
					representingHierPred = getSpoilerVertex(spoilerHierPred, duplicatorHierPred, true, null, null);
					if (representingHierPred instanceof SpoilerNwaVertex<?, ?>) {
						gameHierPreds
								.add(new GameSpoilerNwaVertex<>((SpoilerNwaVertex<LETTER, STATE>) representingHierPred));
					}
				}
			}
		}

		return gameHierPreds;
	}

	/**
	 * Creates a game automaton that is used for summarize edge computation. All
	 * states are initial and no state will be final. This can afterwards be
	 * changed by using {@link NestedWordAutomatonFilteredStates} as a wrapper.
	 * 
	 * @return A game automaton that is used for summarize edge computation
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	private NestedWordAutomaton<GameLetter<LETTER, STATE>, IGameState> createGameAutomaton()
			throws AutomataOperationCanceledException {
		Set<GameLetter<LETTER, STATE>> internalGameAlphabet = new HashSet<>();
		Set<GameLetter<LETTER, STATE>> callGameAlphabet = new HashSet<>();
		Set<GameLetter<LETTER, STATE>> returnGameAlphabet = new HashSet<>();

		NestedWordAutomaton<GameLetter<LETTER, STATE>, IGameState> gameAutomaton = new NestedWordAutomaton<>(mServices,
				internalGameAlphabet, callGameAlphabet, returnGameAlphabet, new GameFactory());

		// Collect all data by using
		// (spoilerVertex -> duplicatorSucc -> spoilerSucc)
		List<Pair<SpoilerNwaVertex<LETTER, STATE>, DuplicatorNwaVertex<LETTER, STATE>>> runningInDuplicatorDeadEnd = new LinkedList<>();
		for (SpoilerVertex<LETTER, STATE> spoilerVertex : mGameGraph.getSpoilerVertices()) {
			if (!(spoilerVertex instanceof SpoilerNwaVertex<?, ?>)) {
				continue;
			}
			SpoilerNwaVertex<LETTER, STATE> spoilerNwaVertex = (SpoilerNwaVertex<LETTER, STATE>) spoilerVertex;

			Set<Vertex<LETTER, STATE>> firstSuccessors = mGameGraph.getSuccessors(spoilerNwaVertex);
			if (firstSuccessors == null) {
				// Spoiler dead-end, not possible since patched before.
				continue;
			}
			for (Vertex<LETTER, STATE> firstSuccessor : firstSuccessors) {
				if (!(firstSuccessor instanceof DuplicatorNwaVertex<?, ?>)) {
					// This should not be possible in a correct game graph.
					continue;
				}
				DuplicatorNwaVertex<LETTER, STATE> duplicatorNwaSucc = (DuplicatorNwaVertex<LETTER, STATE>) firstSuccessor;
				Set<Vertex<LETTER, STATE>> secondSuccessors = mGameGraph.getSuccessors(duplicatorNwaSucc);
				if (secondSuccessors == null) {
					// Duplicator dead-end, only possible for some return
					// vertices.
					if (duplicatorNwaSucc.getTransitionType().equals(ETransitionType.RETURN)) {
						// We later add (spoilerVertex -> duplicatorSucc ->
						// mAuxiliaryGameState) for every letter of the alphabet
						runningInDuplicatorDeadEnd.add(new Pair<>(spoilerNwaVertex, duplicatorNwaSucc));
						if (mLogger.isDebugEnabled()) {
							mLogger.debug("\tRuns into DD dead end: " + spoilerNwaVertex + " -> " + duplicatorNwaSucc);
						}
					}
					continue;
				}
				for (Vertex<LETTER, STATE> secondSuccessor : secondSuccessors) {
					if (!(secondSuccessor instanceof SpoilerNwaVertex<?, ?>)) {
						// This should not be possible in a correct game graph.
						continue;
					}
					SpoilerNwaVertex<LETTER, STATE> spoilerNwaSucc = (SpoilerNwaVertex<LETTER, STATE>) secondSuccessor;

					// We add (spoilerVertex -> duplicatorSucc -> spoilerSucc)
					// to the game automaton
					GameSpoilerNwaVertex<LETTER, STATE> gameNwaVertex = new GameSpoilerNwaVertex<>(spoilerNwaVertex);
					GameSpoilerNwaVertex<LETTER, STATE> gameNwaSucc = new GameSpoilerNwaVertex<>(spoilerNwaSucc);

					addGameStateToGameAutomaton(gameNwaVertex, gameAutomaton);
					addGameStateToGameAutomaton(gameNwaVertex, gameAutomaton);
					addGameStateToGameAutomaton(gameNwaSucc, gameAutomaton);
					ETransitionType transType = duplicatorNwaSucc.getTransitionType();
					if (transType.equals(ETransitionType.INTERNAL)) {
						GameLetter<LETTER, STATE> letter = new GameLetter<>(duplicatorNwaSucc.getLetter(),
								duplicatorNwaSucc.getQ0(), ETransitionType.INTERNAL);
						internalGameAlphabet.add(letter);
						addEdgeToGameAutomaton(gameNwaVertex, letter, gameNwaSucc, gameAutomaton);
					} else if (transType.equals(ETransitionType.CALL)) {
						GameLetter<LETTER, STATE> letter = new GameLetter<>(duplicatorNwaSucc.getLetter(),
								duplicatorNwaSucc.getQ0(), ETransitionType.CALL);
						callGameAlphabet.add(letter);
						addEdgeToGameAutomaton(gameNwaVertex, letter, gameNwaSucc, gameAutomaton);
					} else if (transType.equals(ETransitionType.RETURN)) {
						GameLetter<LETTER, STATE> letter = new GameLetter<>(duplicatorNwaSucc.getLetter(),
								duplicatorNwaSucc.getQ0(), ETransitionType.RETURN);
						returnGameAlphabet.add(letter);
						Iterable<GameSpoilerNwaVertex<LETTER, STATE>> gameHierPreds = computeAllGameHierPreds(
								spoilerNwaVertex, spoilerNwaSucc, duplicatorNwaSucc.getLetter());
						for (GameSpoilerNwaVertex<LETTER, STATE> gameHierPred : gameHierPreds) {
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
		// duplicatorSucc -> mAuxiliaryGameState) for every letter of the
		// alphabet
		for (Pair<SpoilerNwaVertex<LETTER, STATE>, DuplicatorNwaVertex<LETTER, STATE>> runsInDuplicatorDeadEnd : runningInDuplicatorDeadEnd) {
			SpoilerNwaVertex<LETTER, STATE> spoilerNwaVertex = runsInDuplicatorDeadEnd.getFirst();

			GameSpoilerNwaVertex<LETTER, STATE> gameNwaVertex = new GameSpoilerNwaVertex<>(spoilerNwaVertex);

			addGameStateToGameAutomaton(gameNwaVertex, gameAutomaton);
			addGameStateToGameAutomaton(mAuxiliaryGameState, gameAutomaton);

			for (GameLetter<LETTER, STATE> internalLetter : internalGameAlphabet) {
				addEdgeToGameAutomaton(gameNwaVertex, internalLetter, mAuxiliaryGameState, gameAutomaton);
			}
			for (GameLetter<LETTER, STATE> callLetter : callGameAlphabet) {
				addEdgeToGameAutomaton(gameNwaVertex, callLetter, mAuxiliaryGameState, gameAutomaton);
			}
			for (GameLetter<LETTER, STATE> returnLetter : returnGameAlphabet) {
				for (SpoilerNwaVertex<LETTER, STATE> possibleGameHierPred : mSpoilerCallPredecessors) {
					GameSpoilerNwaVertex<LETTER, STATE> possibleGameHierPredGameState = new GameSpoilerNwaVertex<>(
							possibleGameHierPred);
					addGameStateToGameAutomaton(possibleGameHierPredGameState, gameAutomaton);
					addEdgeToGameAutomaton(gameNwaVertex, possibleGameHierPredGameState, returnLetter,
							mAuxiliaryGameState, gameAutomaton);
				}
			}
		}

		return gameAutomaton;
	}

	/**
	 * Returns whether Duplicator would directly lose in direct simulation if
	 * moving to the given Spoiler vertex, or if Spoiler moves from here to him.
	 * This is the case if Spoilers left state is final and the right state is
	 * not.
	 * 
	 * @param leftSpoilerState
	 *            Left state of Spoilers vertex
	 * @param rightSpoilerState
	 *            Right state of Spoilers vertex
	 * @return Whether Duplicator would directly lose in direct simulation if
	 *         moving to the given Spoiler vertex, or if Spoiler moves from here
	 *         to him.
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
		return mNwa.getDownStates(upState).contains(downState);
	}

	/**
	 * Increases the internal counter of the amount of result states by one.
	 */
	private void increaseResultAmountOfStates() {
		mResultAmountOfStates++;
	}

	/**
	 * Increases the internal counter of the amount of result transitions by
	 * one.
	 */
	private void increaseResultAmountOfTransitions() {
		mResultAmountOfTransitions++;
	}

	/**
	 * Generates an equivalence class for the given state from the nwa
	 * automaton, if fair simulation.
	 * 
	 * @param leftState
	 *            State to make equivalence class for
	 */
	private void makeEquivalenceClass(final STATE leftState) {
		final FairGameGraph<LETTER, STATE> fairGraph = castGraphToFairGameGraph();
		if (fairGraph != null) {
			fairGraph.getEquivalenceClasses().makeEquivalenceClass(leftState);
		}
	}

	/**
	 * Updates the priority of the summarize edge corresponding to the given
	 * objects, if the current down state is safe.
	 * 
	 * @param invoker
	 *            Element corresponding to the duplicator vertex that uses the
	 *            call which invoked the summarize edge
	 * @param priorityToSet
	 *            Priority to set for the summarize edge
	 */
	private void updateCorrespondingSummarizeEdge(final SearchElement<LETTER, STATE> invoker, int priorityToSet) {
		// XXX Rework this

		// We need to compute which summarize edges correspond to the current
		// vertex.
		// We do so by using the to the summarize edge corresponding target
		// configuration. This is exactly the target the current
		// configuration leads to after using the outgoing call edge.
		// We access this by using the history element of the search element.
		final Vertex<LETTER, STATE> invokingVertex = invoker.getVertex();
		final Vertex<LETTER, STATE> historyTarget = invoker.getHistory();
		final Vertex<LETTER, STATE> invokingTarget = invoker.getTarget();
		// The corresponding target defines the source of the corresponding
		// edges. If the target is (q0, q1) then all corresponding summarize
		// edges have (q0, q1) as source.
		int bound = 1;
		// In delayed simulation there may be up to two sources, differentiating
		// in the bit, depending on if they are predecessors of the invoker.
		if (mSimulationType == ESimulationType.DELAYED) {
			bound = 2;
		}
		for (int i = 0; i < bound; i++) {
			// First use the false bit. In other cases also try the true bit.
			final boolean bitToUse = i != 0;
			// The source gets determined by the historyTarget.
			final Vertex<LETTER, STATE> sourceOfSummarizeEdges = historyTarget;
			if (sourceOfSummarizeEdges != null && sourceOfSummarizeEdges instanceof SpoilerNwaVertex<?, ?>) {
				final SpoilerNwaVertex<LETTER, STATE> sourceOfSummarizeEdgeAsSpoilerDD = (SpoilerNwaVertex<LETTER, STATE>) sourceOfSummarizeEdges;
				// First we need to validate if the invoking down state
				// forms a safe down state.
				// If the down state is unsafe we do not update summarize
				// edges. We do so by first assuming that the down state is
				// reversely safe, that is when following outgoing edges to
				// the search root. The down state then is safe if the
				// computed source of the summarize edges is a predecessor
				// of the current vertex.
				if (!(mGameGraph.hasPredecessors(invokingVertex)
						&& mGameGraph.getPredecessors(invokingVertex).contains(sourceOfSummarizeEdges))) {
					if (mLogger.isDebugEnabled()) {
						mLogger.debug("\t\tIs no pred: " + sourceOfSummarizeEdges + ", for: " + invokingVertex);
					}
					return;
				}
				// Now update the priority of all
				// corresponding summarize edges
				final Map<Pair<STATE, Set<STATE>>, SummarizeEdge<LETTER, STATE>> destToEdges = mSrcDestToSummarizeEdges
						.get(sourceOfSummarizeEdgeAsSpoilerDD);
				if (destToEdges != null) {
					for (final SummarizeEdge<LETTER, STATE> summarizeEdge : destToEdges.values()) {
						summarizeEdge.setPriority(invoker.getDuplicatorChoice(), priorityToSet);
						if (mLogger.isDebugEnabled()) {
							mLogger.debug("\t\tUpdated summarize edge: " + summarizeEdge.hashCode());
						}
					}
				}
			}
		}
	}

	/**
	 * Adds a given duplicator vertex to the graph and all corresponding
	 * internal fields.
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
	 * Adds a given spoiler vertex to the graph and all corresponding internal
	 * fields.
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
	 * Removes a given duplicator vertex from the graph and all corresponding
	 * internal fields.
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
	 * Removes a given spoiler vertex from the graph and all corresponding
	 * internal fields.
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
