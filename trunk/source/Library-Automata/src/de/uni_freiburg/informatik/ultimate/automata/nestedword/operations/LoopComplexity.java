/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Thomas Lang
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.AutomatonSccComputation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * Operation that computes the loop complexity of an automaton.
 * We define the loop complexity of an automaton as the
 * loop complexity of the underlying graph representation.
 * This number is also called cycle rank.
 * https://en.wikipedia.org/wiki/Cycle_rank
 * 
 * @author Thomas Lang, Matthias Heizmann
 *
 * @param <LETTER> letter type
 * @param <STATE> state type
 */
public class LoopComplexity<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE> {

	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	
	private final NestedWordAutomatonReachableStates<LETTER, STATE> mGraph;
	private final Integer mResult;

	private final HashMap<Set<STATE>, Integer> mStatesToLc = new HashMap<>();

	/**
	 * @param services Ultimate services
	 * @param operand operand
	 * @throws AutomataLibraryException if construction fails
	 */
	public LoopComplexity(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> operand)
					throws AutomataLibraryException {
		super(services);

		if (operand instanceof NestedWordAutomatonReachableStates) {
			mOperand = operand;
		} else {
			mOperand = (new RemoveUnreachable<LETTER, STATE>(mServices, operand)).getResult();
		}

		mGraph = constructGraph();

		mLogger.info(startMessage());

		mResult = computeLoopComplexityOfSubgraph(mGraph.getStates());
		mLogger.info(this.exitMessage());
	}

	/**
	 * Construct an automaton that represents the graph structure of the operand.
	 * @return The Result is a copy of the operand where each edge has the same
	 *     label. As label we us some letter form the alphabet.
	 */
	private NestedWordAutomatonReachableStates<LETTER, STATE> constructGraph()
					throws AutomataOperationCanceledException {
		final LETTER letter = mOperand.getInternalAlphabet().iterator().next();
		final Set<LETTER> singletonAlphabet = Collections.singleton(letter);
		final NestedWordAutomaton<LETTER, STATE> graph =
				new NestedWordAutomaton<LETTER, STATE>(mServices, singletonAlphabet,
				singletonAlphabet, singletonAlphabet, mOperand.getStateFactory());

		for (final STATE q : mOperand.getStates()) {
			graph.addState(true, true, q);
		}

		for (final STATE q1 : mOperand.getStates()) {
			for (final OutgoingInternalTransition<LETTER, STATE> outTrans :
					mOperand.internalSuccessors(q1)) {
				final STATE q2 = outTrans.getSucc();
				if (!graph.containsInternalTransition(q1, letter, q2)) {
					graph.addInternalTransition(q1, letter, q2);
				}
			}
		}
		return (new RemoveUnreachable<LETTER, STATE>(mServices, graph)).getResult();
	}

	/**
	 * Compute the loop complexity of the subgraph that is obtained by projecting mGraph to a subgraph.
	 */
	private Integer computeLoopComplexityOfSubgraph(final Set<STATE> statesOfSubgraph)
			throws AutomataLibraryException {

		final AutomatonSccComputation<LETTER, STATE> sccComputation =
				new AutomatonSccComputation<LETTER, STATE>(mServices,
						mGraph, statesOfSubgraph, statesOfSubgraph);
		final Collection<StronglyConnectedComponent<STATE>> balls = sccComputation.getBalls();

		// Graph contains no balls.
		if (balls.isEmpty()) {
			return 0;
		} else if (balls.size() == 1) {
			// Graph itself is a ball.
			// Consider all subgraphs differing from original graph by one vertex.

			final Set<STATE> ballStates = balls.iterator().next().getNodes();

			final Collection<STATE> nonchainStates = extractNonchainStates(ballStates);

			// If every state has one predecessor and one successor, the ball is a cycle.
			if (nonchainStates.isEmpty()) {
				return 1;
			}

			final Collection<Integer> subGraphLoopComplexities = new ArrayList<Integer>();

			// Create a copy since 'nonchainStates' itself should not be modified.
			final Set<STATE> copyStates = new HashSet<STATE>(statesOfSubgraph);

			for (final STATE stateOut : nonchainStates) {
				// Check for cancel button.
				if (isCancellationRequested()) {
					throw new AutomataOperationCanceledException(this.getClass());
				}

				copyStates.remove(stateOut);

				if (mStatesToLc.containsKey(copyStates)) {
					subGraphLoopComplexities.add(mStatesToLc.get(copyStates));
				} else {
					final Integer i = this.computeLoopComplexityOfSubgraph(copyStates);

					// Create another copy to prevent HashMap from not
					// recognizing sets of states after they have been modified.
					final Set<STATE> keyStates = new HashSet<STATE>(copyStates);
					mStatesToLc.put(keyStates, i);

					subGraphLoopComplexities.add(i);
				}

				copyStates.add(stateOut);
			}

			return 1 + Collections.min(subGraphLoopComplexities);
		} else {
			// Graph itself is not a ball.
			final Collection<Integer> ballLoopComplexities = new ArrayList<Integer>();

			// Compute Loop Complexity for each ball.
			for (final StronglyConnectedComponent<STATE> scc : balls) {
				if (mStatesToLc.containsKey(scc.getNodes())) {
					ballLoopComplexities.add(mStatesToLc.get(scc.getNodes()));
				} else {
					final Integer i = this.computeLoopComplexityOfSubgraph(scc.getNodes());

					final Set<STATE> keyStates = new HashSet<STATE>(scc.getNodes());
					mStatesToLc.put(keyStates, i);

					ballLoopComplexities.add(i);
				}
			}

			return Collections.max(ballLoopComplexities);
		}
	}

	/**
	 * Returns a new collection that contains only the non-chain states.
	 * We call a state a non-chain state if it has not
	 * exactly one predecessor or not exactly one successor.
	 */
	private Collection<STATE> extractNonchainStates(final Set<STATE> states) {
		final Collection<STATE> peakStates = new ArrayList<STATE>();
		// Determine number of predecessors and successors for each state.
		for (final STATE q : states) {
			int pCount = 0;
			int sCount = 0;

			final Iterable<IncomingInternalTransition<LETTER, STATE>> preds =
					mGraph.internalPredecessors(q);
			final Iterable<OutgoingInternalTransition<LETTER, STATE>> succs =
					mGraph.internalSuccessors(q);

			for (final IncomingInternalTransition<LETTER, STATE> p : preds) {
				if (!states.contains(p.getPred())) {
					continue;
				}
				++pCount;
			}

			for (final OutgoingInternalTransition<LETTER, STATE> s : succs) {
				if (!states.contains(s.getSucc())) {
					continue;
				}
				++sCount;
			}

			assert pCount > 0 : "must have at least one predecessor";
			assert sCount > 0 : "must have at least one successor";
			// Add all those states with the maximum number of edges to peakStates.
			if (pCount != 1 || sCount != 1) {
				peakStates.add(q);
			}
		}
		return peakStates;
	}

	@Override
	public String operationName() {
		return "loopComplexity";
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ". Operand with "
				+ mOperand.size()
				+ " states has loop complexity " + mResult;
	}

	@Override
	protected INestedWordAutomatonSimple<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public Integer getResult() {
		return mResult;
	}
}
