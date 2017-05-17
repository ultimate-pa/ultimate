/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.direct;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance.SimulationPerformance;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance.TimeMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Game graph that realizes <b>direct simulation</b>.<br/>
 * In direct simulation each time <i>Spoiler</i> visits a final state <i>Duplicator</i> must also visit one at his next
 * turn.<br/>
 * <br/>
 * If its impossible for <i>Spoiler</i> to build a word such that <i>Duplicator</i> can not fulfill its condition we say
 * <b>q1 direct simulates q0</b> where q0 was the starting state of <i>Spoiler</i> and q1 of <i>Duplicator</i>.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public class DirectGameGraph<LETTER, STATE> extends AGameGraph<LETTER, STATE> {

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
	 * The state factory used for creating states.
	 */
	private final IMergeStateFactory<STATE> mStateFactory;

	/**
	 * Creates a new direct game graph by using the given buechi automaton.
	 * <p>
	 * Throws an IllegalArgumentException If the inputed automaton is no Buechi-automaton. It must have an empty call
	 * and return alphabet.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param stateFactory
	 *            State factory used for state creation The state factory used for creating states.
	 * @param progressTimer
	 *            Timer used for responding to timeouts and operation cancellation.
	 * @param logger
	 *            ILogger of the Ultimate framework.
	 * @param buechi
	 *            The underlying buechi automaton from which the game graph gets generated.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate framework.
	 */
	public DirectGameGraph(final AutomataLibraryServices services, final IMergeStateFactory<STATE> stateFactory,
			final IProgressAwareTimer progressTimer, final ILogger logger,
			final INestedWordAutomaton<LETTER, STATE> buechi) throws AutomataOperationCanceledException {
		super(services, stateFactory, progressTimer, logger, buechi);
		final INestedWordAutomaton<LETTER, STATE> preparedBuechi = getAutomaton();
		verifyAutomatonValidity(preparedBuechi);

		mServices = services;
		mBuechi = preparedBuechi;
		mStateFactory = stateFactory;
		mGraphBuildTime = 0;
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
			performance.startTimeMeasure(TimeMeasure.BUILD_RESULT);
		}

		// Determine which states to merge
		final UnionFind<STATE> uf = new UnionFind<>();
		for (final STATE state : mBuechi.getStates()) {
			uf.makeEquivalenceClass(state);
		}
		final HashRelation<STATE, STATE> similarStates = new HashRelation<>();
		for (final SpoilerVertex<LETTER, STATE> v : getSpoilerVertices()) {
			// all the states we need are in V1...
			if (v.getPM(null, getGlobalInfinity()) < getGlobalInfinity()) {
				final STATE state1 = v.getQ0();
				final STATE state2 = v.getQ1();
				if (state1 != null && state2 != null) {
					similarStates.addPair(state1, state2);
				}
			}

			if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
				getLogger().debug("Stopped in generateBuchiAutomatonFromGraph/filling table");
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}
		// Merge states if they simulate each other
		for (final STATE state1 : similarStates.getDomain()) {
			for (final STATE state2 : similarStates.getImage(state1)) {
				// Only merge if simulation holds in both directions
				if (similarStates.containsPair(state2, state1)) {
					uf.union(state1, state2);
				}
			}

			if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
				getLogger().debug("Stopped in generateBuchiAutomatonFromGraph/marking table");
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}

		// Merge states
		final NestedWordAutomaton<LETTER, STATE> result =
				new NestedWordAutomaton<>(mServices, mBuechi.getVpAlphabet(), mStateFactory);
		final Set<STATE> representativesOfInitials = new HashSet<>();
		for (final STATE initial : mBuechi.getInitialStates()) {
			representativesOfInitials.add(uf.find(initial));
		}

		final Map<STATE, STATE> input2result = new HashMap<>(mBuechi.size());
		for (final STATE representative : uf.getAllRepresentatives()) {
			final boolean isInitial = representativesOfInitials.contains(representative);
			final boolean isFinal = mBuechi.isFinal(representative);
			final Set<STATE> eqClass = uf.getEquivalenceClassMembers(representative);
			final STATE resultState = mStateFactory.merge(eqClass);

			result.addState(isInitial, isFinal, resultState);

			for (final STATE eqClassMember : eqClass) {
				input2result.put(eqClassMember, resultState);
			}
		}

		for (final STATE state : uf.getAllRepresentatives()) {
			final STATE pred = input2result.get(state);
			for (final OutgoingInternalTransition<LETTER, STATE> outTrans : mBuechi.internalSuccessors(state)) {
				final STATE succ = input2result.get(outTrans.getSucc());
				result.addInternalTransition(pred, outTrans.getLetter(), succ);
			}
		}

		// Log performance
		if (performance != null) {
			performance.stopTimeMeasure(TimeMeasure.BUILD_RESULT);
			performance.addTimeMeasureValue(TimeMeasure.BUILD_GRAPH, mGraphBuildTime);
		}

		if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
			getLogger().debug("Stopped in generateBuchiAutomatonFromGraph/states added to result BA");
			throw new AutomataOperationCanceledException(this.getClass());
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
				final SpoilerVertex<LETTER, STATE> v1e = new SpoilerVertex<>(0, false, q0, q1);
				addSpoilerVertex(v1e);
			}

			if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
				getLogger().debug("Stopped in generateGameGraphFromBuechi/calculating v1");
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}
		// Calculate v0 and edges [paper ref 10, 11, 12]
		for (final STATE q0 : mBuechi.getStates()) {
			for (final STATE q1 : mBuechi.getStates()) {
				final Set<LETTER> relevantLetters = new HashSet<>();
				relevantLetters.addAll(mBuechi.lettersInternalIncoming(q0));
				relevantLetters.addAll(mBuechi.lettersInternal(q1));
				for (final LETTER s : relevantLetters) {
					final DuplicatorVertex<LETTER, STATE> v0e = new DuplicatorVertex<>(0, false, q0, q1, s);
					addDuplicatorVertex(v0e);
					// V1 -> V0 edges [paper ref 11]
					for (final IncomingInternalTransition<LETTER, STATE> trans : mBuechi.internalPredecessors(q0, s)) {
						final STATE pred0 = trans.getPred();
						// Only add edge if duplicator does not directly loose
						if (!mBuechi.isFinal(pred0) || mBuechi.isFinal(q1)) {
							addEdge(getSpoilerVertex(pred0, q1, false), v0e);
						}
					}

					// V0 -> V1 edges [paper ref 11]
					for (final OutgoingInternalTransition<LETTER, STATE> trans : mBuechi.internalSuccessors(q1, s)) {
						final STATE succ1 = trans.getSucc();
						// Only add edge if duplicator does not directly loose
						if (!mBuechi.isFinal(q0) || mBuechi.isFinal(succ1)) {
							addEdge(v0e, getSpoilerVertex(q0, succ1, false));
						}
					}
				}

				if (getProgressTimer() != null && !getProgressTimer().continueProcessing()) {
					getLogger().debug("Stopped in generateGameGraphFromBuechi/calculating v0 and edges");
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

		setGraphBuildTime(System.currentTimeMillis() - graphBuildTimeStart);
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
