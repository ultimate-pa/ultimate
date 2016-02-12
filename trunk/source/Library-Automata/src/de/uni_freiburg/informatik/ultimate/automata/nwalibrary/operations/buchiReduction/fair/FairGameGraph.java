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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.EGameGraphChangeType;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.GameGraphChanges;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.performance.ECountingMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.performance.SimulationPerformance;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.performance.ETimeMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.services.model.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.util.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.relation.Triple;

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
 * @author Daniel Tischner
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
	private boolean m_AreThereMergeableStates;
	/**
	 * The underlying buechi automaton from which the game graph gets generated.
	 */
	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Buechi;
	/**
	 * Amount of states the inputed buechi automata has.
	 */
	private int m_BuechiAmountOfStates;
	/**
	 * Amount of transitions the inputed buechi automata has.
	 */
	private int m_BuechiAmountOfTransitions;
	/**
	 * Data structure that allows a fast access to all transitions of the buechi
	 * automaton.<br/>
	 * Gets used for example by {@link #hasBuechiTransition(Triple)}.
	 */
	private final Set<Triple<STATE, LETTER, STATE>> m_BuechiTransitions;
	/**
	 * Data structure that stores changes that where made on buechi transitions
	 * from the perspective of this game graph.<br/>
	 * The transitions are stored <b>inversely</b> by <i>(destination, letter,
	 * source)</i> instead of <i>(source, letter, destination)</i>.
	 */
	private final NestedMap3<STATE, LETTER, STATE, EGameGraphChangeType> m_ChangedBuechiTransitionsInverse;
	/**
	 * Maintains equivalence classes for every state. The game graph has methods
	 * that allow to union the classes of states. The data structure is used for
	 * result generation and indicates states that should be merged, all states
	 * of an equivalence class then get merged to one state.
	 */
	private final UnionFind<STATE> m_EquivalenceClasses;
	/**
	 * Amount of edges the game graph has.
	 */
	private int m_GraphAmountOfEdges;
	/**
	 * Time duration building the graph took in milliseconds.
	 */
	private long m_GraphBuildTime;
	/**
	 * Service provider of Ultimate framework.
	 */
	private final AutomataLibraryServices m_Services;
	/**
	 * Transitions that safely can be removed from the buechi automaton.
	 */
	private List<Triple<STATE, LETTER, STATE>> m_TransitionsToRemove;

	/**
	 * Creates a new fair game graph by using the given buechi automaton.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param progressTimer
	 *            Timer used for responding to timeouts and operation
	 *            cancellation.
	 * @param logger
	 *            Logger of the Ultimate framework.
	 * @param buechi
	 *            The underlying buechi automaton from which the game graph gets
	 *            generated.
	 * @param stateFactory
	 *            State factory used for state creation
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 * @throws IllegalArgumentException
	 *             If the inputed automaton is no Buechi-automaton. It must have
	 *             an empty call and return alphabet.
	 */
	public FairGameGraph(final AutomataLibraryServices services, final IProgressAwareTimer progressTimer,
			final Logger logger, final INestedWordAutomatonOldApi<LETTER, STATE> buechi,
			StateFactory<STATE> stateFactory) throws OperationCanceledException {
		super(progressTimer, logger, stateFactory);
		if (!buechi.getCallAlphabet().isEmpty() || !buechi.getReturnAlphabet().isEmpty()) {
			throw new IllegalArgumentException(
					"The inputed automaton is no Buechi-automaton. It must have an empty call and return alphabet.");
		}
		m_Services = services;
		m_Buechi = buechi;
		m_ChangedBuechiTransitionsInverse = new NestedMap3<>();
		m_BuechiTransitions = new HashSet<>();
		m_EquivalenceClasses = new UnionFind<>();
		m_AreThereMergeableStates = false;
		// Since there are often no remove-able transitions we first initiate it
		// when we actually need it
		m_TransitionsToRemove = null;
		m_BuechiAmountOfStates = 0;
		m_BuechiAmountOfTransitions = 0;
		m_GraphBuildTime = 0;
		m_GraphAmountOfEdges = 0;

		generateGameGraphFromBuechi();
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
			FairGameGraphChanges<LETTER, STATE> fairChanges = (FairGameGraphChanges<LETTER, STATE>) changes;
			// Undo buechi transition changes
			NestedMap3<STATE, LETTER, STATE, EGameGraphChangeType> changedTransitions = fairChanges
					.getChangedBuechiTransitions();
			for (STATE changedKey : changedTransitions.keySet()) {
				for (Triple<LETTER, STATE, EGameGraphChangeType> changedTrans : changedTransitions.get(changedKey)
						.entrySet()) {
					STATE src = changedKey;
					LETTER a = changedTrans.getFirst();
					STATE dest = changedTrans.getSecond();
					// Only undo if there actually is changed transition stored
					if (changedTrans.getThird().equals(EGameGraphChangeType.ADDITION)
							|| changedTrans.getThird().equals(EGameGraphChangeType.REMOVAL)) {
						m_ChangedBuechiTransitionsInverse.get(dest).remove(a, src);
					}
				}
			}
		}
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
	private int calculatePriority(final STATE leftState, final STATE rightState) {
		if (m_Buechi.isFinal(rightState)) {
			return 0;
		} else if (m_Buechi.isFinal(leftState)) {
			return 1;
		} else {
			return 2;
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
		Set<STATE> states = m_Buechi.getStates();
		if (stateToAlignTo == null || stateToAlign == null || !states.contains(stateToAlignTo)
				|| !states.contains(stateToAlign) || stateToAlignTo == stateToAlign) {
			throw new IllegalArgumentException("Arguments must exist in the automaton, be different and not null.");
		}

		FairGameGraphChanges<LETTER, STATE> changes = new FairGameGraphChanges<>();
		boolean madeAChange = false;

		// Work successors of stateToAlignTo
		for (OutgoingInternalTransition<LETTER, STATE> outTrans : m_Buechi.internalSuccessors(stateToAlignTo)) {
			STATE src = stateToAlign;
			LETTER a = outTrans.getLetter();
			STATE dest = outTrans.getSucc();
			if (!hasBuechiTransition(new Triple<>(src, a, dest))) {
				FairGameGraphChanges<LETTER, STATE> currentChange = addBuechiTransition(src, a, dest);
				if (currentChange != null) {
					changes.merge(currentChange, true);
					madeAChange = true;
				}
			}
		}
		// Work predecessors of stateToAlignTo
		for (IncomingInternalTransition<LETTER, STATE> inTrans : m_Buechi.internalPredecessors(stateToAlignTo)) {
			STATE src = inTrans.getPred();
			LETTER a = inTrans.getLetter();
			STATE dest = stateToAlign;

			if (!hasBuechiTransition(new Triple<>(src, a, dest))) {
				FairGameGraphChanges<LETTER, STATE> currentChange = addBuechiTransition(src, a, stateToAlign);
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
		Set<STATE> states = m_Buechi.getStates();
		if (src == null || dest == null || !states.contains(src) || !states.contains(dest)
				|| hasBuechiTransition(new Triple<>(src, a, dest))) {
			throw new IllegalArgumentException("Arguments must exist in the"
					+ " automaton, not be null and the given transitions must not already exist.");
		}
		EGameGraphChangeType wasChangedBefore = m_ChangedBuechiTransitionsInverse.get(dest, a, src);
		if (wasChangedBefore != null && wasChangedBefore.equals(EGameGraphChangeType.ADDITION)) {
			// Transition was already added previously.
			return null;
		}

		// Check if letter is a new incoming letter for destination
		boolean isLetterNew = true;
		Map<STATE, EGameGraphChangeType> changedPreds = m_ChangedBuechiTransitionsInverse.get(dest, a);
		// First iterate over original transitions
		Iterator<STATE> iter = m_Buechi.predInternal(dest, a).iterator();
		while (iter.hasNext()) {
			STATE pred = iter.next();
			// Ignore transition if it was removed before
			if (changedPreds != null) {
				EGameGraphChangeType change = changedPreds.get(pred);
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
			for (Entry<STATE, EGameGraphChangeType> changeEntry : changedPreds.entrySet()) {
				if (changeEntry.getValue() != null && changeEntry.getValue().equals(EGameGraphChangeType.ADDITION)) {
					// Found a valid added transition with given letter
					isLetterNew = false;
					break;
				}
			}
		}

		FairGameGraphChanges<LETTER, STATE> changes = new FairGameGraphChanges<>();

		// Generate new edges and some missing vertices
		for (STATE fixState : states) {
			/*
			 * If letter is new it now generates some new Duplicator vertices If
			 * 'a' was new for q2: (q2, x, a) gets generated
			 */
			if (isLetterNew) {
				STATE rightState = fixState;
				// Continue if that state already exists or was generated before
				if (getDuplicatorVertex(dest, rightState, a, false) != null) {
					continue;
				}
				DuplicatorVertex<LETTER, STATE> generatedVertex = new DuplicatorVertex<>(2, false, dest, rightState, a);
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
				for (OutgoingInternalTransition<LETTER, STATE> succTrans : m_Buechi
						.internalSuccessors(generatedVertex.getQ1(), generatedVertex.getLetter())) {
					/*
					 * Duplicator edges. If 'a' was new for q2: (q2, x, a) gets
					 * generated and (q2, x, a) -> (q2, succ(x, a)) needs also
					 * to be generated.
					 */
					Vertex<LETTER, STATE> edgeDest = getSpoilerVertex(generatedVertex.getQ0(), succTrans.getSucc(),
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
			Vertex<LETTER, STATE> edgeSrc = getSpoilerVertex(src, fixState, false);
			Vertex<LETTER, STATE> edgeDest = getDuplicatorVertex(dest, fixState, a, false);
			if (src != null && dest != null) {
				addEdge(edgeSrc, edgeDest);
				// Remember addition
				changes.addedEdge(edgeSrc, edgeDest);
			}
		}

		// Update set of changes
		m_ChangedBuechiTransitionsInverse.put(dest, a, src, EGameGraphChangeType.ADDITION);
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
		Set<STATE> equivalenceClass = m_EquivalenceClasses.getEquivalenceClassMembers(firstState);

		return equivalenceClass != null && equivalenceClass.contains(secondState);
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
		Set<STATE> states = m_Buechi.getStates();
		if (firstState == null || secondState == null || !states.contains(firstState) || !states.contains(secondState)
				|| firstState == secondState) {
			throw new IllegalArgumentException(
					"Arguments must exist in the" + " automaton, be different and not null.");
		}

		FairGameGraphChanges<LETTER, STATE> changes = new FairGameGraphChanges<>();
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

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.AGameGraph#generateBuchiAutomatonFromGraph()
	 */
	@Override
	protected INestedWordAutomatonOldApi<LETTER, STATE> generateBuchiAutomatonFromGraph()
			throws OperationCanceledException {
		SimulationPerformance performance = getSimulationPerformance();
		if (performance != null) {
			performance.startTimeMeasure(ETimeMeasure.BUILD_RESULT_TIME);
		}

		boolean areThereMergeableStates = m_AreThereMergeableStates;
		boolean areThereRemoveableTransitions = m_TransitionsToRemove != null && !m_TransitionsToRemove.isEmpty();
		Map<STATE, STATE> input2result = null;

		NestedWordAutomaton<LETTER, STATE> result = new NestedWordAutomaton<>(m_Services,
				m_Buechi.getInternalAlphabet(), null, null, getStateFactory());

		int resultAmountOfStates = 0;

		// Merge states
		if (areThereMergeableStates) {
			// Calculate initial states
			Set<STATE> representativesOfInitials = new HashSet<>();
			for (STATE initialState : m_Buechi.getInitialStates()) {
				representativesOfInitials.add(m_EquivalenceClasses.find(initialState));
			}
			// Calculate final states
			Set<STATE> representativesOfFinals = new HashSet<>();
			for (STATE finalState : m_Buechi.getFinalStates()) {
				representativesOfFinals.add(m_EquivalenceClasses.find(finalState));
			}

			// If operation was canceled, for example from the
			// Ultimate framework
			if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
				getLogger().debug("Stopped in generateBuchiAutomatonFromGraph/state calculation finished");
				throw new OperationCanceledException(this.getClass());
			}

			// Add states

			input2result = new HashMap<>(m_Buechi.size());
			for (STATE representative : m_EquivalenceClasses.getAllRepresentatives()) {
				boolean isInitial = representativesOfInitials.contains(representative);
				boolean isFinal = representativesOfFinals.contains(representative);
				Set<STATE> eqClass = m_EquivalenceClasses.getEquivalenceClassMembers(representative);
				STATE mergedState = getStateFactory().minimize(eqClass);
				result.addState(isInitial, isFinal, mergedState);
				resultAmountOfStates++;
				for (STATE eqClassMember : eqClass) {
					input2result.put(eqClassMember, mergedState);
				}
			}
		} else {
			// If there is no merge-able state simply
			// copy the inputed automaton
			for (STATE state : m_Buechi.getStates()) {
				boolean isInitial = m_Buechi.isInitial(state);
				boolean isFinal = m_Buechi.isFinal(state);
				result.addState(isInitial, isFinal, state);
				resultAmountOfStates++;
			}
		}

		int resultAmountOfTransitions = 0;

		// Add transitions
		// for (STATE inputSrc : uf.getAllRepresentatives()) {
		for (STATE inputSrc : m_Buechi.getStates()) {
			// TODO Is it correct to only add transitions of representatives?
			STATE resultSrc;
			if (areThereMergeableStates) {
				// Only access field if it was initialized
				resultSrc = input2result.get(inputSrc);
			} else {
				resultSrc = inputSrc;
			}
			for (OutgoingInternalTransition<LETTER, STATE> outTrans : m_Buechi.internalSuccessors(inputSrc)) {
				LETTER a = outTrans.getLetter();
				STATE inputDest = outTrans.getSucc();
				STATE resultDest;
				if (areThereMergeableStates) {
					// Only access field if it was initialized
					resultDest = input2result.get(inputDest);
				} else {
					resultDest = inputDest;
				}

				if (areThereRemoveableTransitions) {
					// Skip edges that should get removed
					Triple<STATE, LETTER, STATE> transAsTriple = new Triple<>(inputSrc, a, inputDest);
					if (!m_TransitionsToRemove.contains(transAsTriple)) {
						result.addInternalTransition(resultSrc, a, resultDest);
						resultAmountOfTransitions++;
					}
				} else {
					// If there is no removable transition simply copy the
					// inputed automaton
					result.addInternalTransition(resultSrc, a, resultDest);
					resultAmountOfTransitions++;
				}

			}
		}

		// If operation was canceled, for example from the
		// Ultimate framework
		if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
			getLogger().debug("Stopped in generateBuchiAutomatonFromGraph/states and transitions added");
			throw new OperationCanceledException(this.getClass());
		}

		// Log performance
		if (performance != null) {
			performance.stopTimeMeasure(ETimeMeasure.BUILD_RESULT_TIME);
			performance.addTimeMeasureValue(ETimeMeasure.BUILD_GRAPH_TIME, m_GraphBuildTime);
			performance.setCountingMeasure(ECountingMeasure.REMOVED_STATES,
					m_BuechiAmountOfStates - resultAmountOfStates);
			performance.setCountingMeasure(ECountingMeasure.REMOVED_TRANSITIONS,
					m_BuechiAmountOfTransitions - resultAmountOfTransitions);
			performance.setCountingMeasure(ECountingMeasure.BUCHI_TRANSITIONS, m_BuechiAmountOfTransitions);
			performance.setCountingMeasure(ECountingMeasure.BUCHI_STATES, m_BuechiAmountOfStates);
			performance.setCountingMeasure(ECountingMeasure.GAMEGRAPH_EDGES, m_GraphAmountOfEdges);
		}

		// Remove unreachable states which can occur due to transition removal
		if (areThereRemoveableTransitions) {
			NestedWordAutomatonReachableStates<LETTER, STATE> nwaReachableStates = new RemoveUnreachable<LETTER, STATE>(
					m_Services, result).getResult();
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
	protected void generateGameGraphFromBuechi() throws OperationCanceledException {
		long graphBuildTimeStart = System.currentTimeMillis();

		INestedWordAutomatonOldApi<LETTER, STATE> buechi = m_Buechi;

		// Generate states
		for (STATE leftState : buechi.getStates()) {
			m_BuechiAmountOfStates++;

			for (STATE rightState : buechi.getStates()) {
				// Generate Spoiler vertices (leftState, rightState)
				int priority = calculatePriority(leftState, rightState);
				if (priority == 1) {
					increaseGlobalInfinity();
				}
				SpoilerVertex<LETTER, STATE> spoilerVertex = new SpoilerVertex<>(priority, false, leftState,
						rightState);
				addSpoilerVertex(spoilerVertex);

				// Generate Duplicator vertices (leftState, rightState, letter)
				for (LETTER letter : buechi.lettersInternalIncoming(leftState)) {
					DuplicatorVertex<LETTER, STATE> duplicatorVertex = new DuplicatorVertex<>(2, false, leftState,
							rightState, letter);
					addDuplicatorVertex(duplicatorVertex);
				}

				// If operation was canceled, for example from the
				// Ultimate framework
				if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
					getLogger().debug("Stopped in generateGameGraphFromBuechi/generating states");
					throw new OperationCanceledException(this.getClass());
				}
			}

			// Generate an equivalence class for every state from
			// the buechi automaton
			m_EquivalenceClasses.makeEquivalenceClass(leftState);
		}

		increaseGlobalInfinity();

		// Generate edges
		for (STATE edgeDest : buechi.getStates()) {
			// TODO Can we generate edges at the same time
			// we generate states?
			for (IncomingInternalTransition<LETTER, STATE> trans : buechi.internalPredecessors(edgeDest)) {
				m_BuechiAmountOfTransitions++;

				for (STATE fixState : buechi.getStates()) {
					// Duplicator edges q1 -a-> q2 : (x, q1, a) -> (x, q2)
					Vertex<LETTER, STATE> src = getDuplicatorVertex(fixState, trans.getPred(), trans.getLetter(),
							false);
					Vertex<LETTER, STATE> dest = getSpoilerVertex(fixState, edgeDest, false);
					if (src != null && dest != null) {
						addEdge(src, dest);
						m_GraphAmountOfEdges++;
					}

					// Spoiler edges q1 -a-> q2 : (q1, x) -> (q2, x, a)
					src = getSpoilerVertex(trans.getPred(), fixState, false);
					dest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), false);
					if (src != null && dest != null) {
						addEdge(src, dest);
						m_GraphAmountOfEdges++;
					}
					// TODO Can it link trivial edges like duplicator -> spoiler
					// where origin has no predecessors? If optimizing this be
					// careful with adding buechi transitions, this vertex than
					// may be generated and the left edge must also be
					// generated.

					// If operation was canceled, for example from the
					// Ultimate framework
					if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
						getLogger().debug("Stopped in generateGameGraphFromBuechi/generating edges");
						throw new OperationCanceledException(this.getClass());
					}
				}

				m_BuechiTransitions.add(new Triple<>(trans.getPred(), trans.getLetter(), edgeDest));
			}
		}

		m_GraphBuildTime = System.currentTimeMillis() - graphBuildTimeStart;
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
		return m_BuechiTransitions.contains(transition);
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
		Set<STATE> allStates = m_Buechi.getStates();
		if (!allStates.contains(firstState) || !allStates.contains(secondState)) {
			throw new IllegalArgumentException("The given states must exist in the buechi automaton.");
		}
		m_EquivalenceClasses.union(firstState, secondState);

		// There is at least one equivalence class with size greater than one
		if (!m_AreThereMergeableStates && firstState != secondState) {
			m_AreThereMergeableStates = true;
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
		Triple<STATE, LETTER, STATE> transition = new Triple<>(src, a, dest);
		if (!hasBuechiTransition(transition)) {
			throw new IllegalArgumentException("The given transition must exist in the buechi automaton.");
		}

		// Initialize if not already done
		if (m_TransitionsToRemove == null) {
			m_TransitionsToRemove = new LinkedList<>();
		}
		m_TransitionsToRemove.add(transition);
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
		Set<STATE> states = m_Buechi.getStates();
		if (src == null || dest == null || !states.contains(src) || !states.contains(dest)
				|| !hasBuechiTransition(new Triple<>(src, a, dest))) {
			throw new IllegalArgumentException(
					"Arguments must exist in the" + " automaton, not be null and the given transitions must exist.");
		}
		EGameGraphChangeType wasChangedBefore = m_ChangedBuechiTransitionsInverse.get(dest, a, src);
		if (wasChangedBefore != null && wasChangedBefore.equals(EGameGraphChangeType.REMOVAL)) {
			// Transition was already removed previously
			return null;
		}

		FairGameGraphChanges<LETTER, STATE> changes = new FairGameGraphChanges<>();

		// Remove edges that were generated of this transition
		for (STATE fixState : states) {
			// Removal of edges must only be made to vertices of Duplicator
			// Duplicator edges q1 -a-> q2 : (x, q1, a) -> (x, q2, a)
			Vertex<LETTER, STATE> edgeSrc = getDuplicatorVertex(fixState, src, a, false);
			Vertex<LETTER, STATE> edgeDest = getSpoilerVertex(fixState, dest, false);
			if (edgeSrc != null && edgeDest != null) {
				removeEdge(edgeSrc, edgeDest);
				// Remember removal
				changes.removedEdge(edgeSrc, edgeDest);
			}
		}

		// Update set of changes
		m_ChangedBuechiTransitionsInverse.put(dest, a, src, EGameGraphChangeType.REMOVAL);
		changes.removedBuechiTransition(src, a, dest);

		return changes;
	}
}
