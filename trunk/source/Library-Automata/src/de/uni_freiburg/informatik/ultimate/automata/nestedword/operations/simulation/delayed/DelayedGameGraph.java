/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.delayed;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance.ETimeMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance.SimulationPerformance;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;

/**
 * Game graph that realizes <b>delayed simulation</b>.<br/>
 * In delayed simulation each time <i>Spoiler</i> visits a final state
 * <i>Duplicator</i> must at least visit one in the future for coverage.<br/>
 * To reflect <i>Duplicator</i>s coverage the delayed game graph uses vertices
 * that have an extra bit.<br/>
 * <br/>
 * 
 * If its impossible for <i>Spoiler</i> to build a word such that
 * <i>Duplicator</i> can not fulfill its condition we say <b>q1 delayed
 * simulates q0</b> where q0 was the starting state of <i>Spoiler</i> and q1 of
 * <i>Duplicator</i>.
 *
 * The implementation is based on the following paper. Kousha Etessami, Thomas
 * Wilke, Rebecca A. Schuller: Fair Simulation Relations, Parity Games, and
 * State Space Reduction for Bu"chi Automata. SIAM J. Comput. 34(5): 1159-1175
 * (2005)
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 * @author Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * @author Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * 
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public class DelayedGameGraph<LETTER, STATE> extends AGameGraph<LETTER, STATE> {

	/**
	 * The underlying buechi automaton from which the game graph gets generated.
	 */
	private final INestedWordAutomaton<LETTER, STATE> mBuechi;
	/**
	 * Time duration building the graph took in milliseconds.
	 */
	private long mGraphBuildTime;
	/**
	 * Service provider of Ultimate framework.
	 */
	private final AutomataLibraryServices mServices;

	/**
	 * Creates a new delayed game graph by using the given buechi automaton.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param stateFactory
	 *            State factory used for state creation
	 * @param progressTimer
	 *            Timer used for responding to timeouts and operation
	 *            cancellation.
	 * @param logger
	 *            ILogger of the Ultimate framework.
	 * @param buechi
	 *            The underlying buechi automaton from which the game graph gets
	 *            generated.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 * @throws IllegalArgumentException
	 *             If the inputed automaton is no Buechi-automaton. It must have
	 *             an empty call and return alphabet.
	 */
	public DelayedGameGraph(final AutomataLibraryServices services, final IMergeStateFactory<STATE> stateFactory,
			final IProgressAwareTimer progressTimer, final ILogger logger,
			final INestedWordAutomaton<LETTER, STATE> buechi) throws AutomataOperationCanceledException {
		super(services, stateFactory, progressTimer, logger, buechi);
		final INestedWordAutomaton<LETTER, STATE> preparedBuechi = getAutomaton();
		verifyAutomatonValidity(preparedBuechi);

		mServices = services;
		mBuechi = preparedBuechi;
		mGraphBuildTime = 0;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.AGameGraph#generateBuchiAutomatonFromGraph()
	 */
	@Override
	public INestedWordAutomaton<LETTER, STATE> generateAutomatonFromGraph()
			throws AutomataOperationCanceledException {
		final SimulationPerformance performance = getSimulationPerformance();
		if (performance != null) {
			performance.startTimeMeasure(ETimeMeasure.BUILD_RESULT);
		}

		// Determine which states to merge
		final ArrayList<STATE> states = new ArrayList<>();
		states.addAll(mBuechi.getStates());
		final boolean[][] table = new boolean[states.size()][states.size()];
		for (final SpoilerVertex<LETTER, STATE> v : getSpoilerVertices()) {
			// All the states we need are in spoiler vertices

			// Which node do we have to consider in order to obtain the
			// simulation information for the state pair (q0,q1) ?
			// According to Lemma 4 (page 1166) of the above mentioned paper
			// We consider (q0, q1, true) if q0 is final and q1 is not final
			// and we consider (q0, q1, false) if q0 is not final or q1 is
			// final.
			final boolean considerVertex;
			if (v.isB()) {
				considerVertex = mBuechi.isFinal(v.getQ0()) && !mBuechi.isFinal(v.getQ1());
			} else {
				considerVertex = !mBuechi.isFinal(v.getQ0()) || mBuechi.isFinal(v.getQ1());
			}

			if (considerVertex) {
				if (v.getPM(null, getGlobalInfinity()) < getGlobalInfinity()) {
					table[states.indexOf(v.getQ0())][states.indexOf(v.getQ1())] = true;
				}
			}
			
			if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
				getLogger().debug("Stopped in generateBuchiAutomaton/filling table");
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}

		// Merge states
		final boolean[] marker = new boolean[states.size()];
		final Set<STATE> temp = new HashSet<>();
		final HashMap<STATE, STATE> oldSNames2newSNames = new HashMap<>();
		final NestedWordAutomaton<LETTER, STATE> result = new NestedWordAutomaton<>(mServices,
				mBuechi.getInternalAlphabet(), null, null, getStateFactory());

		for (int i = 0; i < states.size(); i++) {
			if (marker[i]) {
				continue;
			}
			temp.clear();
			temp.add(states.get(i));
			marker[i] = true;
			boolean isFinal = mBuechi.isFinal(states.get(i));
			boolean isInitial = mBuechi.isInitial(states.get(i));
			for (int j = i; j < states.size(); j++) {
				if (table[i][j] && table[j][i] && !marker[j]) {
					temp.add(states.get(j));
					marker[j] = true;
					if (mBuechi.isFinal(states.get(j))) {
						isFinal = true;
					}
					if (mBuechi.isInitial(states.get(j))) {
						isInitial = true;
					}
				}
			}
			final STATE minimizedStateName = getStateFactory().merge(temp);
			for (final STATE c : temp) {
				oldSNames2newSNames.put(c, minimizedStateName);
			}
			result.addState(isInitial, isFinal, minimizedStateName);
			marker[i] = true;
			
			if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
				getLogger().debug("Stopped in generateBuchiAutomaton/adding states to result BA");
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}

		// Add edges
		for (final STATE c : mBuechi.getStates()) {
			for (final LETTER s : mBuechi.getInternalAlphabet()) {
				for (final OutgoingInternalTransition<LETTER, STATE> trans :
						mBuechi.internalSuccessors(c, s)) {
					final STATE newPred = oldSNames2newSNames.get(c);
					final STATE newSucc = oldSNames2newSNames.get(trans.getSucc());
					result.addInternalTransition(newPred, s, newSucc);
				}
			}
			
			if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
				getLogger().debug("Stopped in generateBuchiAutomaton/adding edges");
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}

		// Log performance
		if (performance != null) {
			performance.stopTimeMeasure(ETimeMeasure.BUILD_RESULT);
			performance.addTimeMeasureValue(ETimeMeasure.BUILD_GRAPH, mGraphBuildTime);
		}

		return result;
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

		// Calculate v1 [paper ref 10]
		for (final STATE q0 : mBuechi.getStates()) {
			for (final STATE q1 : mBuechi.getStates()) {
				SpoilerVertex<LETTER, STATE> v1e = new SpoilerVertex<>(0, false, q0, q1);
				addSpoilerVertex(v1e);
				if (!mBuechi.isFinal(q1)) {
					v1e = new SpoilerVertex<>(1, true, q0, q1);
					addSpoilerVertex(v1e);
					increaseGlobalInfinity();
				}
			}
			if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
				getLogger().debug("Stopped in generateGameGraph/calculating v1");
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}
		// Calculate v0 and edges [paper ref 10, 11, 12]
		for (final STATE q0 : mBuechi.getStates()) {
			boolean countedTransitionsForQ0 = false;

			for (final STATE q1 : mBuechi.getStates()) {
				for (final LETTER s : mBuechi.lettersInternalIncoming(q0)) {
					if (mBuechi.internalPredecessors(q0, s).iterator().hasNext()) {
						DuplicatorVertex<LETTER, STATE> v0e = new DuplicatorVertex<>(2, false, q0, q1, s);
						addDuplicatorVertex(v0e);
						// V0 -> V1 edges [paper ref 11]
						for (final OutgoingInternalTransition<LETTER, STATE> trans :
								mBuechi.internalSuccessors(q1, s)) {
							final STATE q2 = trans.getSucc();
							addEdge(v0e, getSpoilerVertex(q0, q2, false));
						}
						// V1 -> V0 edges [paper ref 11]
						for (final IncomingInternalTransition<LETTER, STATE> trans :
								mBuechi.internalPredecessors(q0, s)) {
							final STATE q2 = trans.getPred();
							if (!mBuechi.isFinal(q0)) {
								addEdge(getSpoilerVertex(q2, q1, false), v0e);
							}
						}
						v0e = new DuplicatorVertex<>(2, true, q0, q1, s);
						addDuplicatorVertex(v0e);
						// V0 -> V1 edges [paper ref 11]
						for (final OutgoingInternalTransition<LETTER, STATE> trans :
								mBuechi.internalSuccessors(q1, s)) {
							final STATE q2 = trans.getSucc();
							if (!mBuechi.isFinal(q2) && getAmountOfBitsForSpoilerVertices(q0, q2) > 1) {
								addEdge(v0e, getSpoilerVertex(q0, q2, true));
							} else {
								addEdge(v0e, getSpoilerVertex(q0, q2, false));
							}
						}
						// V1 -> V0 edges [paper ref 11]
						for (final IncomingInternalTransition<LETTER, STATE> trans :
								mBuechi.internalPredecessors(q0, s)) {
							final STATE q2 = trans.getPred();
							if (getAmountOfBitsForSpoilerVertices(q2, q1) > 1) {
								addEdge(getSpoilerVertex(q2, q1, true), v0e);
							}
							if (mBuechi.isFinal(q0)) {
								addEdge(getSpoilerVertex(q2, q1, false), v0e);
							}

							// Make sure to only count this transitions one time
							// for q0
							if (!countedTransitionsForQ0) {
							}
						}
					}
				}
				countedTransitionsForQ0 = true;
				
				if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
					getLogger().debug("Stopped in generateGameGraph/calculating v0 and edges");
					throw new AutomataOperationCanceledException(this.getClass());
				}
			}
		}
		// global infinity = (# of pr==1 nodes) + 1
		increaseGlobalInfinity();
		final ILogger logger = getLogger();
		if (logger.isDebugEnabled()) {
			logger.debug("Infinity is " + getGlobalInfinity());
			logger.debug("Number of vertices in game graph: "
					+ (getDuplicatorVertices().size() + getSpoilerVertices().size()));
			logger.debug("Number of vertices in v0: " + getDuplicatorVertices().size());
			logger.debug("Number of vertices in v1: " + getSpoilerVertices().size());
		}

		mGraphBuildTime = System.currentTimeMillis() - graphBuildTimeStart;
	}

	/**
	 * Gets the amount of {@link SpoilerVertex} objects that exist in the game
	 * graph with representation (q0, q1). Since there can be such vertices with
	 * the extra bit false and true the returned value is between zero and two.
	 * 
	 * @param q0
	 *            The state spoiler is at
	 * @param q1
	 *            The state duplicator is at
	 * @return The amount of {@link SpoilerVertex} objects that exist in the
	 *         game graph with representation (q0, q1). Since there can be such
	 *         vertices with the extra bit false and true the returned value is
	 *         between zero and two.
	 */
	private int getAmountOfBitsForSpoilerVertices(final STATE q0, final STATE q1) {
		int amount = 0;

		if (getSpoilerVertex(q0, q1, false) != null) {
			amount++;
		}

		if (getSpoilerVertex(q0, q1, true) != null) {
			amount++;
		}

		return amount;
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
