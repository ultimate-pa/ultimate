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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.fair;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.EGameGraphChangeType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.GameGraphChanges;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance.ETimeMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance.SimulationPerformance;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Game graph that realizes <b>fair simulation</b>.<br/>
 * In fair simulation each time <i>Spoiler</i> builds an accepting word
 * <i>Duplicator</i>s word must also be accepting.<br/>
 * <br/>
 * 
 * If its impossible for <i>Spoiler</i> to build a word such that
 * <i>Duplicator</i> can not fulfill its condition we say <b>q1 fair simulates
 * q0</b> where q0 was the starting state of <i>Spoiler</i> and q1 of
 * <i>Duplicator</i>.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 *
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public class FairGameGraph<LETTER, STATE> extends AGameGraph<LETTER, STATE> {
	/**
	 * If it is currently known that there are merge-able states.
	 */
	private boolean mAreThereMergeableStates;
	/**
	 * The underlying buechi automaton from which the game graph gets generated.
	 */
	private final INestedWordAutomaton<LETTER, STATE> mBuechi;
	/**
	 * Data structure that allows a fast access to all transitions of the buechi
	 * automaton.<br/>
	 * Gets used for example by {@link #hasBuechiTransition(Triple)}.
	 */
	private final Set<Triple<STATE, LETTER, STATE>> mBuechiTransitions;
	/**
	 * Data structure that stores changes that where made on buechi transitions
	 * from the perspective of this game graph.<br/>
	 * The transitions are stored <b>inversely</b> by <i>(destination, letter,
	 * source)</i> instead of <i>(source, letter, destination)</i>.
	 */
	private final NestedMap3<STATE, LETTER, STATE, EGameGraphChangeType> mChangedBuechiTransitionsInverse;
	/**
	 * Maintains equivalence classes for every state. The game graph has methods
	 * that allow to union the classes of states. The data structure is used for
	 * result generation and indicates states that should be merged, all states
	 * of an equivalence class then get merged to one state.
	 */
	private final UnionFind<STATE> mEquivalenceClasses;
	/**
	 * Time duration building the graph took in milliseconds.
	 */
	private long mGraphBuildTime;
	/**
	 * Service provider of Ultimate framework.
	 */
	private final AutomataLibraryServices mServices;
	/**
	 * Transitions that safely can be removed from the buechi automaton.
	 */
	private List<Triple<STATE, LETTER, STATE>> mTransitionsToRemove;

	/**
	 * Creates a new fair game graph by using the given buechi automaton.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param progressTimer
	 *            Timer used for responding to timeouts and operation
	 *            cancellation.
	 * @param logger
	 *            ILogger of the Ultimate framework.
	 * @param buechi
	 *            The underlying buechi automaton from which the game graph gets
	 *            generated.
	 * @param stateFactory
	 *            State factory used for state creation
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 * @throws IllegalArgumentException
	 *             If the inputed automaton is no Buechi-automaton. It must have
	 *             an empty call and return alphabet.
	 */
	public FairGameGraph(final AutomataLibraryServices services, final IProgressAwareTimer progressTimer,
			final ILogger logger, final INestedWordAutomaton<LETTER, STATE> buechi,
			final IStateFactory<STATE> stateFactory) throws AutomataOperationCanceledException {
		super(services, progressTimer, logger, stateFactory, buechi);
		final INestedWordAutomaton<LETTER, STATE> preparedBuechi = getAutomaton();
		verifyAutomatonValidity(preparedBuechi);

		mServices = services;
		mBuechi = preparedBuechi;
		mChangedBuechiTransitionsInverse = new NestedMap3<>();
		mBuechiTransitions = new HashSet<>();
		mEquivalenceClasses = new UnionFind<>();
		mAreThereMergeableStates = false;
		// Since there are often no remove-able transitions we first initiate it
		// when we actually need it
		mTransitionsToRemove = null;
		mGraphBuildTime = 0;
	}

	/**
	 * Returns whether there are merge-able states in the game graph.
	 * 
	 * @return <tt>True</tt> if there are merge-able states in the graph,
	 *         <tt>false</tt> if not.
	 */
	public boolean areThereMergeableStates() {
		return mAreThereMergeableStates;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.AGameGraph#generateBuchiAutomatonFromGraph()
	 */
	@Override
	public INestedWordAutomaton<LETTER, STATE> generateAutomatonFromGraph() throws AutomataOperationCanceledException {
		final SimulationPerformance performance = getSimulationPerformance();
		if (performance != null) {
			performance.startTimeMeasure(ETimeMeasure.BUILD_RESULT);
		}

		final boolean areThereMergeableStates = mAreThereMergeableStates;
		final boolean areThereRemoveableTransitions = mTransitionsToRemove != null && !mTransitionsToRemove.isEmpty();
		Map<STATE, STATE> input2result = null;

		final NestedWordAutomaton<LETTER, STATE> result = new NestedWordAutomaton<>(mServices,
				mBuechi.getInternalAlphabet(), null, null, getStateFactory());

		// Merge states
		if (areThereMergeableStates) {
			// Calculate initial states
			final Set<STATE> representativesOfInitials = new HashSet<>();
			for (final STATE initialState : mBuechi.getInitialStates()) {
				representativesOfInitials.add(mEquivalenceClasses.find(initialState));
			}
			// Calculate final states
			final Set<STATE> representativesOfFinals = new HashSet<>();
			for (final STATE finalState : mBuechi.getFinalStates()) {
				representativesOfFinals.add(mEquivalenceClasses.find(finalState));
			}

			// If operation was canceled, for example from the
			// Ultimate framework
			if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
				getLogger().debug("Stopped in generateBuchiAutomatonFromGraph/state calculation finished");
				throw new AutomataOperationCanceledException(this.getClass());
			}

			// Add states

			input2result = new HashMap<>(mBuechi.size());
			for (final STATE representative : mEquivalenceClasses.getAllRepresentatives()) {
				final boolean isInitial = representativesOfInitials.contains(representative);
				final boolean isFinal = representativesOfFinals.contains(representative);
				final Set<STATE> eqClass = mEquivalenceClasses.getEquivalenceClassMembers(representative);
				final STATE mergedState = getStateFactory().minimize(eqClass);
				result.addState(isInitial, isFinal, mergedState);
				for (final STATE eqClassMember : eqClass) {
					input2result.put(eqClassMember, mergedState);
				}
			}
		} else {
			// If there is no merge-able state simply
			// copy the inputed automaton
			for (final STATE state : mBuechi.getStates()) {
				final boolean isInitial = mBuechi.isInitial(state);
				final boolean isFinal = mBuechi.isFinal(state);
				result.addState(isInitial, isFinal, state);
			}
		}

		// Add transitions
		for (final STATE inputSrc : mBuechi.getStates()) {
			STATE resultSrc;
			if (areThereMergeableStates) {
				// Only access field if it was initialized
				resultSrc = input2result.get(inputSrc);
			} else {
				resultSrc = inputSrc;
			}
			for (final OutgoingInternalTransition<LETTER, STATE> outTrans : mBuechi.internalSuccessors(inputSrc)) {
				final LETTER a = outTrans.getLetter();
				final STATE inputDest = outTrans.getSucc();
				STATE resultDest;
				if (areThereMergeableStates) {
					// Only access field if it was initialized
					resultDest = input2result.get(inputDest);
				} else {
					resultDest = inputDest;
				}

				if (areThereRemoveableTransitions) {
					// Skip edges that should get removed
					final Triple<STATE, LETTER, STATE> transAsTriple = new Triple<>(inputSrc, a, inputDest);
					if (!mTransitionsToRemove.contains(transAsTriple)) {
						result.addInternalTransition(resultSrc, a, resultDest);
					}
				} else {
					// If there is no removable transition simply copy the
					// inputed automaton
					result.addInternalTransition(resultSrc, a, resultDest);
				}

			}
		}

		// If operation was canceled, for example from the
		// Ultimate framework
		if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
			getLogger().debug("Stopped in generateBuchiAutomatonFromGraph/states and transitions added");
			throw new AutomataOperationCanceledException(this.getClass());
		}

		// Log performance
		if (performance != null) {
			performance.stopTimeMeasure(ETimeMeasure.BUILD_RESULT);
			performance.addTimeMeasureValue(ETimeMeasure.BUILD_GRAPH, mGraphBuildTime);
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

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.AGameGraph#generateGameGraphFromBuechi()
	 */
	@Override
	public void generateGameGraphFromAutomaton() throws AutomataOperationCanceledException {
		final long graphBuildTimeStart = System.currentTimeMillis();

		final INestedWordAutomaton<LETTER, STATE> buechi = mBuechi;

		// Generate vertices
		for (final STATE leftState : buechi.getStates()) {
			for (final STATE rightState : buechi.getStates()) {
				// Generate Spoiler vertices (leftState, rightState)
				final int priority = calculatePriority(leftState, rightState);
				if (priority == 1) {
					increaseGlobalInfinity();
				}
				final SpoilerVertex<LETTER, STATE> spoilerVertex = new SpoilerVertex<>(priority, false, leftState,
						rightState);
				addSpoilerVertex(spoilerVertex);

				// Generate Duplicator vertices (leftState, rightState, letter)
				for (final LETTER letter : buechi.lettersInternalIncoming(leftState)) {
					final DuplicatorVertex<LETTER, STATE> duplicatorVertex = new DuplicatorVertex<>(2, false, leftState,
							rightState, letter);
					addDuplicatorVertex(duplicatorVertex);
				}

				// If operation was canceled, for example from the
				// Ultimate framework
				if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
					getLogger().debug("Stopped in generateGameGraphFromBuechi/generating vertices");
					throw new AutomataOperationCanceledException(this.getClass());
				}
			}

			// Generate an equivalence class for every state from
			// the buechi automaton
			mEquivalenceClasses.makeEquivalenceClass(leftState);
		}

		increaseGlobalInfinity();

		// Generate edges
		for (final STATE edgeDest : buechi.getStates()) {
			for (final IncomingInternalTransition<LETTER, STATE> trans : buechi.internalPredecessors(edgeDest)) {
				for (final STATE fixState : buechi.getStates()) {
					// Duplicator edges q1 -a-> q2 : (x, q1, a) -> (x, q2)
					Vertex<LETTER, STATE> src = getDuplicatorVertex(fixState, trans.getPred(), trans.getLetter(),
							false);
					Vertex<LETTER, STATE> dest = getSpoilerVertex(fixState, edgeDest, false);
					if (src != null && dest != null) {
						addEdge(src, dest);
					}

					// Spoiler edges q1 -a-> q2 : (q1, x) -> (q2, x, a)
					src = getSpoilerVertex(trans.getPred(), fixState, false);
					dest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), false);
					if (src != null && dest != null) {
						addEdge(src, dest);
					}

					// If operation was canceled, for example from the
					// Ultimate framework
					if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
						getLogger().debug("Stopped in generateGameGraphFromBuechi/generating edges");
						throw new AutomataOperationCanceledException(this.getClass());
					}
				}

				mBuechiTransitions.add(new Triple<>(trans.getPred(), trans.getLetter(), edgeDest));
			}
		}

		mGraphBuildTime = System.currentTimeMillis() - graphBuildTimeStart;
	}

	/**
	 * Gets the internal field of all transitions the used buechi has.
	 * 
	 * @return The internal field of all transitions the used buechi has
	 */
	public Set<Triple<STATE, LETTER, STATE>> getBuechiTransitions() {
		return mBuechiTransitions;
	}

	/**
	 * Gets the equivalence classes.
	 * 
	 * @return The equivalence classes
	 */
	public UnionFind<STATE> getEquivalenceClasses() {
		return mEquivalenceClasses;
	}

	/**
	 * Gets the list of transitions that should be removed from the input
	 * automaton.
	 * 
	 * @return List of transitions that should be removed from the input
	 *         automaton.
	 */
	public List<Triple<STATE, LETTER, STATE>> getTransitionsToRemove() {
		return mTransitionsToRemove;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.AGameGraph#undoChanges(de.uni_freiburg.informatik.ultimate
	 * .automata.nwalibrary.operations.buchiReduction.GameGraphChanges)
	 */
	@Override
	public void undoChanges(final GameGraphChanges<LETTER, STATE> changes) {
		super.undoChanges(changes);

		if (changes == null) {
			return;
		}

		if (changes instanceof FairGameGraphChanges) {
			final FairGameGraphChanges<LETTER, STATE> fairChanges = (FairGameGraphChanges<LETTER, STATE>) changes;
			// Undo buechi transition changes
			final NestedMap3<STATE, LETTER, STATE, EGameGraphChangeType> changedTransitions = fairChanges
					.getChangedBuechiTransitions();
			for (final STATE changedKey : changedTransitions.keySet()) {
				for (final Triple<LETTER, STATE, EGameGraphChangeType> changedTrans : changedTransitions.get(changedKey)
						.entrySet()) {
					final STATE src = changedKey;
					final LETTER a = changedTrans.getFirst();
					final STATE dest = changedTrans.getSecond();
					// Only undo if there actually is changed transition stored
					if (changedTrans.getThird().equals(EGameGraphChangeType.ADDITION)
							|| changedTrans.getThird().equals(EGameGraphChangeType.REMOVAL)) {
						mChangedBuechiTransitionsInverse.get(dest).remove(a, src);
					}
				}
			}
		}
	}

	/**
	 * Equalizes a given state to another by adding transitions so that the
	 * state to align has the same out- and in-going transitions that the state
	 * to align to has.
	 * 
	 * @param stateToAlign
	 *            The state to align
	 * @param stateToAlignTo
	 *            The state to align to
	 * @return A game graph changes object that has all made changes stored or
	 *         <tt>null</tt> if no changes where made. Can be used to undo
	 *         changes by using {@link #undoChanges(GameGraphChanges)}.
	 * @throws IllegalArgumentException
	 *             If arguments are <tt>null</tt>, equal or do not exist in the
	 *             buechi automaton.
	 */
	private FairGameGraphChanges<LETTER, STATE> equalizeBuechiStatesOneDir(final STATE stateToAlign,
			final STATE stateToAlignTo) {
		final Set<STATE> states = mBuechi.getStates();
		if (stateToAlignTo == null || stateToAlign == null || !states.contains(stateToAlignTo)
				|| !states.contains(stateToAlign) || stateToAlignTo == stateToAlign) {
			throw new IllegalArgumentException("Arguments must exist in the automaton, be different and not null.");
		}

		final FairGameGraphChanges<LETTER, STATE> changes = new FairGameGraphChanges<>();
		boolean madeAChange = false;

		// Work successors of stateToAlignTo
		for (final OutgoingInternalTransition<LETTER, STATE> outTrans : mBuechi.internalSuccessors(stateToAlignTo)) {
			final STATE src = stateToAlign;
			final LETTER a = outTrans.getLetter();
			final STATE dest = outTrans.getSucc();
			if (!hasBuechiTransition(new Triple<>(src, a, dest))) {
				final FairGameGraphChanges<LETTER, STATE> currentChange = addBuechiTransition(src, a, dest);
				if (currentChange != null) {
					changes.merge(currentChange, true);
					madeAChange = true;
				}
			}
		}
		// Work predecessors of stateToAlignTo
		for (final IncomingInternalTransition<LETTER, STATE> inTrans : mBuechi.internalPredecessors(stateToAlignTo)) {
			final STATE src = inTrans.getPred();
			final LETTER a = inTrans.getLetter();
			final STATE dest = stateToAlign;

			if (!hasBuechiTransition(new Triple<>(src, a, dest))) {
				final FairGameGraphChanges<LETTER, STATE> currentChange = addBuechiTransition(src, a, stateToAlign);
				if (currentChange != null) {
					changes.merge(currentChange, true);
					madeAChange = true;
				}
			}
		}

		if (madeAChange) {
			return changes;
		} else {
			return null;
		}
	}

	/**
	 * Simulates the addition of a transition to the buechi automaton. More
	 * precisely to the buechi automaton <i>Spoiler</i> plays on.<br/>
	 * It will add the corresponding edges and vertices to the game graph and
	 * remember the changes made.
	 * 
	 * @param src
	 *            Source of the transition to add
	 * @param a
	 *            Letter of the transition to add
	 * @param dest
	 *            Destination of the transition to add
	 * @return A game graph changes object that has all made changes stored or
	 *         <tt>null</tt> if no changes where made. Can be used to undo
	 *         changes by using {@link #undoChanges(GameGraphChanges)}.
	 * @throws IllegalArgumentException
	 *             If arguments are <tt>null</tt>, equal, do not exist in the
	 *             buechi automaton or the transition already existed.
	 */
	protected FairGameGraphChanges<LETTER, STATE> addBuechiTransition(final STATE src, final LETTER a,
			final STATE dest) {
		final Set<STATE> states = mBuechi.getStates();
		if (src == null || dest == null || !states.contains(src) || !states.contains(dest)
				|| hasBuechiTransition(new Triple<>(src, a, dest))) {
			throw new IllegalArgumentException("Arguments must exist in the"
					+ " automaton, not be null and the given transitions must not already exist.");
		}
		final EGameGraphChangeType wasChangedBefore = mChangedBuechiTransitionsInverse.get(dest, a, src);
		if (wasChangedBefore != null && wasChangedBefore.equals(EGameGraphChangeType.ADDITION)) {
			// Transition was already added previously.
			return null;
		}

		// Check if letter is a new incoming letter for destination
		boolean isLetterNew = true;
		final Map<STATE, EGameGraphChangeType> changedPreds = mChangedBuechiTransitionsInverse.get(dest, a);
		// First iterate over original transitions
		final Iterator<IncomingInternalTransition<LETTER, STATE>> iter =
				mBuechi.internalPredecessors(dest, a).iterator();
		while (iter.hasNext()) {
			final STATE pred = iter.next().getPred();
			// Ignore transition if it was removed before
			if (changedPreds != null) {
				final EGameGraphChangeType change = changedPreds.get(pred);
				if (change != null && change.equals(EGameGraphChangeType.REMOVAL)) {
					continue;
				}
			}
			// Found a valid transition with given letter
			isLetterNew = false;
			break;
		}
		// Second iterate over possible added transitions
		if (isLetterNew && changedPreds != null) {
			for (final Entry<STATE, EGameGraphChangeType> changeEntry : changedPreds.entrySet()) {
				if (changeEntry.getValue() != null && changeEntry.getValue().equals(EGameGraphChangeType.ADDITION)) {
					// Found a valid added transition with given letter
					isLetterNew = false;
					break;
				}
			}
		}

		final FairGameGraphChanges<LETTER, STATE> changes = new FairGameGraphChanges<>();

		// Generate new edges and some missing vertices
		for (final STATE fixState : states) {
			/*
			 * If letter is new it now generates some new Duplicator vertices If
			 * 'a' was new for q2: (q2, x, a) gets generated
			 */
			if (isLetterNew) {
				final STATE rightState = fixState;
				// Continue if that state already exists or was generated before
				if (getDuplicatorVertex(dest, rightState, a, false) != null) {
					continue;
				}
				final DuplicatorVertex<LETTER, STATE> generatedVertex = new DuplicatorVertex<>(2, false, dest, rightState, a);
				addDuplicatorVertex(generatedVertex);
				// Remember addition
				changes.addedVertex(generatedVertex);

				/*
				 * Generate left edges for newly generated vertices.
				 * 
				 * Newly generated vertices need their left edges that would be
				 * there if they were not be obsolete in the previous graph. Now
				 * they are not obsolete anymore and need to be generated.
				 * 
				 * It is very important that the right state does not give a
				 * successor transition that was added in previous usages of the
				 * add-function or language may change.
				 */
				for (final OutgoingInternalTransition<LETTER, STATE> succTrans : mBuechi
						.internalSuccessors(generatedVertex.getQ1(), generatedVertex.getLetter())) {
					/*
					 * Duplicator edges. If 'a' was new for q2: (q2, x, a) gets
					 * generated and (q2, x, a) -> (q2, succ(x, a)) needs also
					 * to be generated.
					 */
					final Vertex<LETTER, STATE> edgeDest = getSpoilerVertex(generatedVertex.getQ0(), succTrans.getSucc(),
							false);
					if (generatedVertex != null && edgeDest != null) {
						addEdge(generatedVertex, edgeDest);
						// Remember addition
						changes.addedEdge(generatedVertex, edgeDest);
					}
					/*
					 * Spoiler edges. Also (pre(q2, a), x) -> (q2, x, a) needs
					 * to be generated but it gets already covered by the next
					 * statement.
					 */
				}
			}

			// Generate new edges

			// Addition of edges must only be made to vertices of Spoiler
			// Spoiler edges q1 -a-> q2 : (q1, x) -> (q2, x, a)
			final Vertex<LETTER, STATE> edgeSrc = getSpoilerVertex(src, fixState, false);
			final Vertex<LETTER, STATE> edgeDest = getDuplicatorVertex(dest, fixState, a, false);
			if (src != null && dest != null) {
				addEdge(edgeSrc, edgeDest);
				// Remember addition
				changes.addedEdge(edgeSrc, edgeDest);
			}
		}

		// Update set of changes
		mChangedBuechiTransitionsInverse.put(dest, a, src, EGameGraphChangeType.ADDITION);
		changes.addedBuechiTransition(src, a, dest);

		return changes;
	}

	/**
	 * Returns if the given states are in the same equivalence class.<br/>
	 * A equivalence class contains states that where marked as merge-able using
	 * {@link #markMergeable(Object, Object)}. This is especially useful if for
	 * example <i>firstState</i> and <i>secondState</i> came into the class with
	 * <i>thirdState</i> respectively. In this case <i>firstState</i> and
	 * <i>secondState</i> are also in the same equivalence class and so
	 * merge-able.
	 * 
	 * @param firstState
	 *            First state
	 * @param secondState
	 *            Second state
	 * @return True if the given states are in the same equivalence class, false
	 *         if not
	 * @throws IllegalArgumentException
	 *             If one or both states are <tt>null</tt>.
	 */
	protected boolean areInSameEquivalenceClasses(final STATE firstState, final STATE secondState) {
		if (firstState == null || secondState == null) {
			throw new IllegalArgumentException("The given states must not be null.");
		}

		if (firstState.equals(secondState)) {
			return true;
		}
		final Set<STATE> equivalenceClass = mEquivalenceClasses.getEquivalenceClassMembers(firstState);

		return equivalenceClass != null && equivalenceClass.contains(secondState);
	}

	/**
	 * Calculates the priority of a given {@link SpoilerVertex} by its
	 * representation <i>(state spoiler is at, state duplicator is at)</i>.<br/>
	 * Note that {@link DuplicatorVertex} objects always should have priority 2.
	 * 
	 * @param leftState
	 *            The state spoiler is at
	 * @param rightState
	 *            The state duplicator is at
	 * @return The calculated priority of the given {@link SpoilerVertex} which
	 *         is 0 if the right state is final, 2 if both are final and 1 if
	 *         only the left state is final.
	 */
	protected int calculatePriority(final STATE leftState, final STATE rightState) {
		if (mBuechi.isFinal(rightState)) {
			return 0;
		} else if (mBuechi.isFinal(leftState)) {
			return 1;
		} else {
			return 2;
		}
	}

	/**
	 * Equalizes two given states to each other by adding transitions so that
	 * both have the same out- and in-going transitions.
	 * 
	 * @param firstState
	 *            First state to equalize
	 * @param secondState
	 *            Second state to equalize
	 * @return A game graph changes object that has all made changes stored or
	 *         <tt>null</tt> if no changes where made. Can be used to undo
	 *         changes by using {@link #undoChanges(GameGraphChanges)}.
	 * @throws IllegalArgumentException
	 *             If arguments are <tt>null</tt>, equal or do not exist in the
	 *             buechi automaton.
	 */
	protected FairGameGraphChanges<LETTER, STATE> equalizeBuechiStates(final STATE firstState,
			final STATE secondState) {
		final Set<STATE> states = mBuechi.getStates();
		if (firstState == null || secondState == null || !states.contains(firstState) || !states.contains(secondState)
				|| firstState == secondState) {
			throw new IllegalArgumentException(
					"Arguments must exist in the" + " automaton, be different and not null.");
		}

		final FairGameGraphChanges<LETTER, STATE> changes = new FairGameGraphChanges<>();
		boolean madeAChange = false;

		// Equalize states in both directions
		FairGameGraphChanges<LETTER, STATE> currentChange = equalizeBuechiStatesOneDir(secondState, firstState);
		if (currentChange != null) {
			changes.merge(currentChange, true);
			madeAChange = true;
		}
		currentChange = equalizeBuechiStatesOneDir(firstState, secondState);
		if (currentChange != null) {
			changes.merge(currentChange, true);
			madeAChange = true;
		}

		if (madeAChange) {
			return changes;
		} else {
			return null;
		}
	}

	/**
	 * Returns if the underlying buechi automaton has a given transition.
	 * 
	 * @param transition
	 *            The transition of interest
	 * @return True if the underlying buechi automaton has a given transition,
	 *         false if not.
	 */
	protected boolean hasBuechiTransition(final Triple<STATE, LETTER, STATE> transition) {
		return mBuechiTransitions.contains(transition);
	}

	/**
	 * Marks two given states merge-able.<br/>
	 * This unions the internal equivalence classes of the two given states. The
	 * equivalence classes indicate which states are merge-able. All states in a
	 * class get merged to one state.
	 * 
	 * @param firstState
	 *            First state
	 * @param secondState
	 *            Second state
	 * @throws IllegalArgumentException
	 *             If one or both states do not exist in the buechi automaton.
	 */
	protected void markMergeable(final STATE firstState, final STATE secondState) {
		final Set<STATE> allStates = mBuechi.getStates();
		if (!allStates.contains(firstState) || !allStates.contains(secondState)) {
			throw new IllegalArgumentException("The given states must exist in the buechi automaton.");
		}
		mEquivalenceClasses.union(firstState, secondState);

		// There is at least one equivalence class with size greater than one
		if (!mAreThereMergeableStates && firstState != secondState) {
			mAreThereMergeableStates = true;
		}
	}

	/**
	 * Marks a given transition remove-able.<br/>
	 * When generating the resulting automaton the marked transitions will be
	 * left.
	 * 
	 * @param src
	 *            Source of the transition
	 * @param a
	 *            Letter of the transition
	 * @param dest
	 *            Destination of the transition
	 * @throws IllegalArgumentException
	 *             If the given transition does not exist in the buechi
	 *             automaton.
	 */
	protected void markRemoveableTransition(final STATE src, final LETTER a, final STATE dest) {
		final Triple<STATE, LETTER, STATE> transition = new Triple<>(src, a, dest);
		if (!hasBuechiTransition(transition)) {
			throw new IllegalArgumentException("The given transition must exist in the buechi automaton.");
		}

		// Initialize if not already done
		if (mTransitionsToRemove == null) {
			mTransitionsToRemove = new LinkedList<>();
		}
		mTransitionsToRemove.add(transition);
	}

	/**
	 * Simulates the removal of a transition from the buechi automaton. More
	 * precisely to the buechi automaton <i>Duplicator</i> plays on.<br/>
	 * It will remove the corresponding edges from the game graph and remember
	 * the changes made.
	 * 
	 * @param src
	 *            Source of the transition to remove
	 * @param a
	 *            Letter of the transition to remove
	 * @param dest
	 *            Destination of the transition to remove
	 * @return A game graph changes object that has all made changes stored or
	 *         <tt>null</tt> if no changes where made. Can be used to undo
	 *         changes by using {@link #undoChanges(GameGraphChanges)}.
	 * @throws IllegalArgumentException
	 *             If arguments are <tt>null</tt>, equal, do not exist in the
	 *             buechi automaton or the transition does not existed.
	 */
	protected FairGameGraphChanges<LETTER, STATE> removeBuechiTransition(final STATE src, final LETTER a,
			final STATE dest) {
		final Set<STATE> states = mBuechi.getStates();
		if (src == null || dest == null || !states.contains(src) || !states.contains(dest)
				|| !hasBuechiTransition(new Triple<>(src, a, dest))) {
			throw new IllegalArgumentException(
					"Arguments must exist in the" + " automaton, not be null and the given transitions must exist.");
		}
		final EGameGraphChangeType wasChangedBefore = mChangedBuechiTransitionsInverse.get(dest, a, src);
		if (wasChangedBefore != null && wasChangedBefore.equals(EGameGraphChangeType.REMOVAL)) {
			// Transition was already removed previously
			return null;
		}

		final FairGameGraphChanges<LETTER, STATE> changes = new FairGameGraphChanges<>();

		// Remove edges that were generated of this transition
		for (final STATE fixState : states) {
			// Removal of edges must only be made to vertices of Duplicator
			// Duplicator edges q1 -a-> q2 : (x, q1, a) -> (x, q2, a)
			final Vertex<LETTER, STATE> edgeSrc = getDuplicatorVertex(fixState, src, a, false);
			final Vertex<LETTER, STATE> edgeDest = getSpoilerVertex(fixState, dest, false);
			if (edgeSrc != null && edgeDest != null) {
				removeEdge(edgeSrc, edgeDest);
				// Remember removal
				changes.removedEdge(edgeSrc, edgeDest);
			}
		}

		// Update set of changes
		mChangedBuechiTransitionsInverse.put(dest, a, src, EGameGraphChangeType.REMOVAL);
		changes.removedBuechiTransition(src, a, dest);

		return changes;
	}

	/**
	 * Sets the internal field of the graphBuildTime.
	 * 
	 * @param graphBuildTime
	 *            The graphBuildTime to set
	 */
	protected void setGraphBuildTime(final long graphBuildTime) {
		mGraphBuildTime = graphBuildTime;
	}
}
