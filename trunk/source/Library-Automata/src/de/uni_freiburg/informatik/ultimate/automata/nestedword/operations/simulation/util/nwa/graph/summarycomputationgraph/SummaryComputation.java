/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.summarycomputationgraph;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.SpoilerNwaVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.GameLetter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.GameSpoilerNwaVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.IGameState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.summarycomputationgraph.WeightedSummaryTargets.WeightedSummaryTargetsComparator;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.util.LexicographicCounter;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PosetUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * Class for computation of game graph summaries.
 * The computation of the summaries is done in the game automaton.
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class SummaryComputation<LETTER, STATE> {
	
	private final IDoubleDeckerAutomaton<GameLetter<LETTER, STATE>, IGameState> mGameAutomaton = null;
	private final Map<NestedMap2<IGameState, SpoilerNwaVertex<LETTER, STATE>, Integer>, SummaryComputationGraphNode<LETTER, STATE>> mSummaryComputationGraphNodes = 
			new HashMap<NestedMap2<IGameState, SpoilerNwaVertex<LETTER, STATE>, Integer>, SummaryComputationGraphNode<LETTER, STATE>>();
	private final ArrayDeque<SummaryComputationGraphNode<LETTER, STATE>> mWorklist = new ArrayDeque<>();
	
	
	private final WeightedSummaryTargetsComparator mWeightedSummaryTargetsComparator = new WeightedSummaryTargetsComparator();
	
	
	final Function<GameLetter<LETTER, STATE>, Integer> mDuplicatorNodePriorityProvider = (x -> 2);
	final Function<IGameState, Integer> mSpoilerNodePriorityProvider = (x -> ((GameSpoilerNwaVertex<LETTER, STATE>) x).getSpoilerNwaVertex().getPriority());
	final Function<IGameState, Integer> mCallWorkaroundPriorityProvider = (x -> 2);
	
	private final HashRelation<Set<IGameState>, SummaryComputationGraphNode<LETTER, STATE>> mSummaryTrigger2Node = new HashRelation<>();
	
	
	private void initialThings() {
		for (final IGameState gs : mGameAutomaton.getStates()) {
			mGameAutomaton.summarySuccessors(gs);
			
		}
	}
	
	
	private void process(final SummaryComputationGraphNode<LETTER, STATE> succNode) {
		final HashRelation3<LETTER, IGameState, IGameState> letter2succ2hier = collectIncomingReturnLetters(succNode);
		for (final LETTER letter : letter2succ2hier.projectToFst()) {
			final Set<IGameState> summaryTriggers = letter2succ2hier.projectToSnd(letter);
			mSummaryTrigger2Node.addPair(summaryTriggers, succNode);
		}
		
		final Set<LETTER> letters = collectIncomingInternalLetters(succNode);
		for (final LETTER letter : letters) {
			processInternalPredecessors(letter, succNode);
		}
		
		
	}
	
	
	private void processInternalPredecessors(final LETTER letter, final SummaryComputationGraphNode<LETTER, STATE> succNode) {
		for (final IGameState source : succNode.getSources()) {
			
		}
		
	}


	private void computePredecessors(final SummaryComputationGraphNode<LETTER, STATE> succNode) {
		
			
		// collect all relevant letters first
		final Set<LETTER> letters = collectIncomingInternalLetters(succNode);
		final List<SummaryComputationGraphNode<LETTER, STATE>> predecessors = new ArrayList();
		
		
		for (final IGameState source : succNode.getSources()) {
		for (final LETTER letter : letters) {
			final HashRelation<GameLetter<LETTER, STATE>, IGameState> dupl2spoi = new HashRelation<>();
			final HashRelation<IGameState, GameLetter<LETTER, STATE>> spoi2dupl = new HashRelation<>();
					
			for (final IGameState gs : succNode.getCurrent(source)) {
				for (final IncomingInternalTransition<GameLetter<LETTER, STATE>, IGameState> trans : mGameAutomaton.internalPredecessors(gs)) {
					final GameLetter<LETTER, STATE> gl = trans.getLetter();
					if (!gl.equals(letter)) {
						continue;
					}
					dupl2spoi.addPair(trans.getLetter(), gs);
					spoi2dupl.addPair(trans.getPred(), trans.getLetter());
				}
			}
			

			final Set<Map<GameLetter<LETTER, STATE>, WeightedSummaryTargets>> dupl2Wst = 
					computePredecessorsUnderPly(Collections.singleton(succNode.getCurrent2Targets(source)), dupl2spoi, mDuplicatorNodePriorityProvider);

			final Set<Map<IGameState, WeightedSummaryTargets>> spoi2Wsts =
					computePredecessorsUnderPly(dupl2Wst, spoi2dupl, mSpoilerNodePriorityProvider);
			for (final Map<IGameState, WeightedSummaryTargets> spoi2Wst : spoi2Wsts) {
				
			}
			
			
		}
		}		
		
	}


	private Set<LETTER> collectIncomingInternalLetters(final SummaryComputationGraphNode<LETTER, STATE> succNode) {
		final Set<LETTER> letters = new HashSet<>();
		for (final IGameState source : succNode.getSources()) {
			for (final IGameState gs : succNode.getCurrent(source)) {
				for ( final IncomingInternalTransition<GameLetter<LETTER, STATE>, IGameState> trans : mGameAutomaton.internalPredecessors(gs)) {
					final GameLetter<LETTER, STATE> gl = trans.getLetter();
					letters.add(gl.getLetter());
				}
			}
		}
		return letters;
	}
	
	private Set<LETTER> collectIncomingCallLetters(final SummaryComputationGraphNode<LETTER, STATE> succNode) {
		final Set<LETTER> letters = new HashSet<>();
		for (final IGameState source : succNode.getSources()) {
			for (final IGameState gs : succNode.getCurrent(source)) {
				for ( final IncomingCallTransition<GameLetter<LETTER, STATE>, IGameState> trans : mGameAutomaton.callPredecessors(gs)) {
					final GameLetter<LETTER, STATE> gl = trans.getLetter();
					letters.add(gl.getLetter());
				}
			}
		}
		return letters;
	}
	
	private HashRelation3<LETTER, IGameState, IGameState> collectIncomingReturnLetters(final SummaryComputationGraphNode<LETTER, STATE> succNode) {
		final HashRelation3<LETTER, IGameState, IGameState> letter2succ2hier = new HashRelation3<>();
		for (final IGameState source : succNode.getSources()) {
			for (final IGameState gs : succNode.getCurrent(source)) {
				for (final IncomingReturnTransition<GameLetter<LETTER, STATE>, IGameState> trans : mGameAutomaton.returnPredecessors(gs)) {
					final GameLetter<LETTER, STATE> gl = trans.getLetter();
					letter2succ2hier.addTriple(gl.getLetter(), gs, trans.getHierPred());
				}
			}
		}
		return letter2succ2hier;
	}

	
	
	private <PRED,SUCC> Set<Map<PRED, WeightedSummaryTargets>> computePredecessorsUnderPly(final Set<Map<SUCC, WeightedSummaryTargets>> succNodes,
			final HashRelation<PRED, SUCC> pred2succ, final Function<PRED, Integer> priorityProvider) {
		final Set<Map<PRED, WeightedSummaryTargets>> preds = new HashSet<>();
		for (final Map<SUCC, WeightedSummaryTargets> succNode : succNodes) {
			final List<PRED> predGameLetters = new ArrayList<>();
			final List<List<WeightedSummaryTargets>> predWeightedSummaryTargets = new ArrayList<>();
			for (final PRED pred : pred2succ.getDomain()) {
				final Set<WeightedSummaryTargets> weightedSummaryTargetsSet = new HashSet<>();
				final Set<SUCC> succs = pred2succ.getImage(pred);
				for (final SUCC succ : succs) {
					final int predPriority = priorityProvider.apply(pred);
					final WeightedSummaryTargets wst = succNode.get(succ);
					weightedSummaryTargetsSet.add(wst.computeUpdate(predPriority));
				}
				final List<WeightedSummaryTargets> filtered = 
						PosetUtils.filterMaximalElements(weightedSummaryTargetsSet, mWeightedSummaryTargetsComparator).collect(Collectors.toList());
				predGameLetters.add(pred);
				predWeightedSummaryTargets.add(filtered);
			}
			final int[] numberOfElements = new int[predWeightedSummaryTargets.size()];
			for (int i=0; i<predWeightedSummaryTargets.size(); i++) {
				numberOfElements[i] = predWeightedSummaryTargets.get(i).size();
			}

			final LexicographicCounter c = new LexicographicCounter(numberOfElements);
			do {
				final Map<PRED, WeightedSummaryTargets> pred = 
						new HashMap<>();
				final int[] currentCounterValue = c.getCurrentValue();
				for (int i=0; i<currentCounterValue.length; i++) {
					pred.put(predGameLetters.get(i), predWeightedSummaryTargets.get(i).get(currentCounterValue[i]));
				}
				preds.add(pred);
				c.increment();
			} while (c.isZero());
			assert c.getNumberOfValuesProduct() == preds.size() : "inconsistent";
		}
		return preds;
	}
	
}
