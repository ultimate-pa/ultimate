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
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.PriorityComparator;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.GameLetter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.GameSpoilerNwaVertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.IGameState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.summarycomputationgraph.WeightedSummaryTargets.WeightedSummaryTargetsComparator;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.LexicographicCounter;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PosetUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Class for computation of game graph summaries.
 * The computation of the summaries is done in the game automaton.
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class SummaryComputation<LETTER, STATE> {
	
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger; 
	
	private final IDoubleDeckerAutomaton<GameLetter<LETTER, STATE>, IGameState> mGameAutomaton;
	private final ArrayDeque<SummaryComputationGraphNode<LETTER, STATE>> mWorklist = new ArrayDeque<>();
	
	private final Set<SummaryComputationGraphNode<LETTER, STATE>> mNodes = new HashSet<>();
	
	
	private final WeightedSummaryTargetsComparator mWeightedSummaryTargetsComparator = new WeightedSummaryTargetsComparator();
	
	
	final Function<GameLetter<LETTER, STATE>, Function<IGameState, Integer>> mDuplicatorNodePriorityProvider = (x -> (y -> 2));
	
	private Integer duplicatorNodePriorityProvider(final GameLetter<LETTER, STATE> duplicatorNode, final IGameState spoilerNode) {
		return 2;
	}
	final Function<IGameState, Function<GameLetter<LETTER, STATE>, Integer>> mSpoilerNodePriorityProvider = (x -> (y -> ((GameSpoilerNwaVertex<LETTER, STATE>) x).getSpoilerNwaVertex().getPriority()));

	private Integer spoilerNodePriorityProvider(final IGameState spoilerNode, final GameLetter<LETTER, STATE> duplicatorNode) {
		return ((GameSpoilerNwaVertex<LETTER, STATE>) spoilerNode).getSpoilerNwaVertex().getPriority();
	}

	
	final Function<IGameState, Function<GameLetter<LETTER, STATE>, Integer>> mCallWorkaroundPriorityProvider = (x -> (y -> 2));
	
	private Integer callWorkaroundPriorityProvider(final IGameState spoilerNode, final GameLetter<LETTER, STATE> duplicatorNode) {
		return 2;
	}
	
	
	private final HashRelation<Set<IGameState>, NestedMap2<IGameState, IGameState, Integer>> mTrigger2Summaries = new HashRelation<>();
	
	private final HashRelation<Set<IGameState>, SummaryComputationGraphNode<LETTER, STATE>> mSummaryTrigger2Node = new HashRelation<>();
	
	
	
	
	
	public SummaryComputation(final AutomataLibraryServices services,
			final IDoubleDeckerAutomaton<GameLetter<LETTER, STATE>, IGameState> gameAutomaton) {
		super();
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mGameAutomaton = gameAutomaton;
		initialize();
		while (!mWorklist.isEmpty()) {
			final SummaryComputationGraphNode<LETTER, STATE> node = mWorklist.remove();
			process(node);
		}
		mLogger.info("Found " + mTrigger2Summaries.size() + " summaries");
	}


	private void initialize() {
		
		for (final IGameState gs : mGameAutomaton.getStates()) {
			final HashRelation<LETTER, IGameState> letter2summarySucc = new HashRelation<>();
			for (final SummaryReturnTransition<GameLetter<LETTER, STATE>, IGameState> trans : mGameAutomaton.summarySuccessors(gs)) {
				letter2summarySucc.addPair(trans.getLetter().getLetter(), trans.getSucc());
			}
			for (final LETTER letter : letter2summarySucc.getDomain()) {
				final NestedMap2<IGameState, IGameState, WeightedSummaryTargets> summarySucc = new NestedMap2<>();
				for (final IGameState succ : letter2summarySucc.getImage(letter)) {
					summarySucc.put(mGameAutomaton.getEmptyStackState(), succ, new WeightedSummaryTargets(succ, 2));
				}
				processReturnPredecessors(letter, summarySucc, letter2summarySucc.getImage(letter));
			}
		}
	}
	
	
	private void process(final SummaryComputationGraphNode<LETTER, STATE> succNode) {
		final HashRelation3<LETTER, IGameState, IGameState> letter2succ2hier = collectIncomingReturnLetters(succNode);
		for (final LETTER letter : letter2succ2hier.projectToFst()) {
			final Set<IGameState> summaryTriggers = letter2succ2hier.projectToSnd(letter);
			mSummaryTrigger2Node.addPair(summaryTriggers, succNode);
			for (final NestedMap2<IGameState, IGameState, Integer> summary : mTrigger2Summaries.getImage(summaryTriggers)) {
				processSummary(succNode, summary);
			}
			processReturnPredecessors(letter, succNode.getSource2Current2Targets(), summaryTriggers);
		}
		
		{
			final Set<LETTER> letters = collectIncomingCallLetters(succNode);
			for (final LETTER letter : letters) {
				processCallPredecessors(letter, succNode);
			}
		}

		{
			final Set<LETTER> letters = collectIncomingInternalLetters(succNode);
			for (final LETTER letter : letters) {
				processInternalPredecessors(letter, succNode);
			}
		}
		
		
		
	}
	
	
	private void processReturnPredecessors(final LETTER letter,
			final NestedMap2<IGameState, IGameState, WeightedSummaryTargets> source2Current2Targets,
			final Set<IGameState> summaryTriggers) {
		mLogger.info("computing predecessors under " + letter);
		final HashRelation<GameLetter<LETTER, STATE>, IGameState> dupl2spoi = new HashRelation<>();
		final Map<IGameState, HashRelation<GameLetter<LETTER, STATE>, IGameState>> hier2dupl2spoi = new HashMap<>();
		final HashRelation<IGameState, GameLetter<LETTER, STATE>> spoi2dupl = new HashRelation<>();
		for (final Pair<IGameState, IGameState> sourceCurrentPair : source2Current2Targets.keys2()) {
			for (final IncomingReturnTransition<GameLetter<LETTER, STATE>, IGameState> trans : mGameAutomaton.returnPredecessors(sourceCurrentPair.getSecond())) {
				final GameLetter<LETTER, STATE> gl = trans.getLetter();
				if (!gl.getLetter().equals(letter)) {
					continue;
				}
				dupl2spoi.addPair(trans.getLetter(), sourceCurrentPair.getSecond());
				{
					final IGameState hier = trans.getHierPred();
					HashRelation<GameLetter<LETTER, STATE>, IGameState> dupl2spoiForHier = hier2dupl2spoi.get(hier);
					if (dupl2spoiForHier == null) {
						dupl2spoiForHier = new HashRelation<>();
						hier2dupl2spoi.put(hier, dupl2spoiForHier);
					}
					dupl2spoiForHier.addPair(trans.getLetter(), sourceCurrentPair.getSecond());
				}
				spoi2dupl.addPair(trans.getLinPred(), trans.getLetter());
			}
		}
		if (dupl2spoi.size() == 0) {
			// no predecessor for this letter
			return;
		}
		
		final Set<NestedMap2<IGameState, GameLetter<LETTER, STATE>, WeightedSummaryTargets>> dupl2Wst = Collections.singleton( 
				computeDuplicatorPredecessorUnderReturn(source2Current2Targets, hier2dupl2spoi));
//				computePredecessorsUnderPly(Collections.singleton(source2Current2Targets), dupl2spoi, this::duplicatorNodePriorityProvider, hier2dupl2spoi);
		final Set<NestedMap2<IGameState, IGameState, WeightedSummaryTargets>> spoi2Wsts =
				computePredecessorsUnderPly(dupl2Wst, spoi2dupl, this::spoilerNodePriorityProvider, this::spoilerAggregration);
		
		for (final NestedMap2<IGameState, IGameState, WeightedSummaryTargets> spoi2Wst : spoi2Wsts) {
			constructNode(spoi2Wst, summaryTriggers);
		}

	}


	private NestedMap2<IGameState, GameLetter<LETTER, STATE>, WeightedSummaryTargets> computeDuplicatorPredecessorUnderReturn(
			final NestedMap2<IGameState, IGameState, WeightedSummaryTargets> source2Current2Targets,
			final Map<IGameState, HashRelation<GameLetter<LETTER, STATE>, IGameState>> hier2dupl2spoi) {
		final NestedMap2<IGameState, GameLetter<LETTER, STATE>, WeightedSummaryTargets> result = 
				new NestedMap2<IGameState, GameLetter<LETTER, STATE>, WeightedSummaryTargets>();
		for (final Entry<IGameState, HashRelation<GameLetter<LETTER, STATE>, IGameState>> entry : hier2dupl2spoi.entrySet()) {
			final IGameState source = entry.getKey();
			for (final GameLetter<LETTER, STATE> dupl : entry.getValue().getDomain()) {
				final Map<IGameState, Integer> target2priority = new HashMap<>();
				for (final IGameState target : entry.getValue().getImage(dupl)) {
					target2priority.put(target, 2);
				}
				final WeightedSummaryTargets wst = new WeightedSummaryTargets(target2priority);
				result.put(source, dupl, wst);
			}
		}
		return result;
	}


	private void processInternalPredecessors(final LETTER letter, final SummaryComputationGraphNode<LETTER, STATE> succNode) {
		mLogger.info("computing predecessors under " + letter);
		final HashRelation<GameLetter<LETTER, STATE>, IGameState> dupl2spoi = new HashRelation<>();
		final HashRelation<IGameState, GameLetter<LETTER, STATE>> spoi2dupl = new HashRelation<>();
		for (final IGameState source : succNode.getSources()) {
			for (final IGameState gs : succNode.getCurrent(source)) {
				for (final IncomingInternalTransition<GameLetter<LETTER, STATE>, IGameState> trans : mGameAutomaton.internalPredecessors(gs)) {
					final GameLetter<LETTER, STATE> gl = trans.getLetter();
					if (!gl.getLetter().equals(letter)) {
						continue;
					}
					dupl2spoi.addPair(trans.getLetter(), gs);
					spoi2dupl.addPair(trans.getPred(), trans.getLetter());
				}
			}
		}
		final Set<NestedMap2<IGameState, GameLetter<LETTER, STATE>, WeightedSummaryTargets>> dupl2Wst = 
				computePredecessorsUnderPly(Collections.singleton(succNode.getSource2Current2Targets()), dupl2spoi, 
						this::duplicatorNodePriorityProvider, this::duplicatorAggregration);
		final Set<NestedMap2<IGameState, IGameState, WeightedSummaryTargets>> spoi2Wsts =
				computePredecessorsUnderPly(dupl2Wst, spoi2dupl, this::spoilerNodePriorityProvider, this::spoilerAggregration);
		
		for (final NestedMap2<IGameState, IGameState, WeightedSummaryTargets> spoi2Wst : spoi2Wsts) {
			constructNode(spoi2Wst, succNode.getSummaryComputationTriggers());
		}
	}


	private void constructNode(final NestedMap2<IGameState, IGameState, WeightedSummaryTargets> spoi2Wst,
			final Set<IGameState> summaryComputationTriggers) {
		final SummaryComputationGraphNode<LETTER, STATE> node = new SummaryComputationGraphNode<LETTER, STATE>(spoi2Wst, summaryComputationTriggers);
		mLogger.info("constructed node " + node);
		if (!mNodes.contains(node)) {
			mLogger.info("added to worklist");
			mWorklist.add(node);
			mNodes.add(node);
		} else {
			mLogger.info("already constructed");
		}
	}
	
	
	private void processCallPredecessors(final LETTER letter, final SummaryComputationGraphNode<LETTER, STATE> succNode) {
		mLogger.info("computing predecessors under " + letter);
		final HashRelation<GameLetter<LETTER, STATE>, IGameState> dupl2spoi = new HashRelation<>();
		final HashRelation<IGameState, GameLetter<LETTER, STATE>> spoi2dupl = new HashRelation<>();
		for (final IGameState source : succNode.getSources()) {
			for (final IGameState gs : succNode.getCurrent(source)) {
				for (final IncomingCallTransition<GameLetter<LETTER, STATE>, IGameState> trans : mGameAutomaton.callPredecessors(gs)) {
					final GameLetter<LETTER, STATE> gl = trans.getLetter();
					if (!gl.getLetter().equals(letter)) {
						continue;
					}
					dupl2spoi.addPair(trans.getLetter(), gs);
					spoi2dupl.addPair(trans.getPred(), trans.getLetter());
				}
			}
		}
		final Set<NestedMap2<IGameState, GameLetter<LETTER, STATE>, WeightedSummaryTargets>> dupl2Wst = 
				computePredecessorsUnderPly(Collections.singleton(succNode.getSource2Current2Targets()), dupl2spoi, 
						this::duplicatorNodePriorityProvider, this::duplicatorAggregration);
		final Set<NestedMap2<IGameState, IGameState, WeightedSummaryTargets>> spoi2Wsts =
				computePredecessorsUnderPly(dupl2Wst, spoi2dupl, this::callWorkaroundPriorityProvider,
						this::spoilerAggregration);
		
		for (final NestedMap2<IGameState, IGameState, WeightedSummaryTargets> spoi2Wst : spoi2Wsts) {
			constructSummary(spoi2Wst, succNode.getSummaryComputationTriggers());
		}
	}


	private void constructSummary(final NestedMap2<IGameState, IGameState, WeightedSummaryTargets> spoi2Wst,
			final Set<IGameState> summaryComputationTriggers) {
		final NestedMap2<IGameState, IGameState, Integer> target2source2priority = new NestedMap2<>();
		for (final IGameState source : spoi2Wst.keySet()) {
			// take only these, where current state and summary source coincide
			final WeightedSummaryTargets wst = spoi2Wst.get(source, source);
			for (final Entry<IGameState, Integer> target2priority : wst.entrySet()) {
				target2source2priority.put(target2priority.getKey(), source, target2priority.getValue());
			}
		}
		mTrigger2Summaries.addPair(summaryComputationTriggers, target2source2priority);
		for (final SummaryComputationGraphNode<LETTER, STATE> waitingForSummary : mSummaryTrigger2Node.getImage(summaryComputationTriggers)) {
			processSummary(waitingForSummary, target2source2priority);
		}
	}


	private void processSummary(final SummaryComputationGraphNode<LETTER, STATE> waitingForSummary,
			final NestedMap2<IGameState, IGameState, Integer> target2source2priority) {
		final HashRelation<IGameState, IGameState> dupl2spoi = new HashRelation<>();
		for (final Pair<IGameState, IGameState> pair : target2source2priority.keys2()) {
			dupl2spoi.addPair(pair.getFirst(), pair.getSecond());
		}
		final Set<NestedMap2<IGameState, IGameState, WeightedSummaryTargets>> spoi2Wsts = 
				computePredecessorsUnderPly(Collections.singleton(waitingForSummary.getSource2Current2Targets()), 
						dupl2spoi, target2source2priority::get, this::duplicatorAggregration);

		for (final NestedMap2<IGameState, IGameState, WeightedSummaryTargets> spoi2Wst : spoi2Wsts) {
			constructNode(spoi2Wst, waitingForSummary.getSummaryComputationTriggers());
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
	
	 @FunctionalInterface
	 interface PriorityProvider<P,S> {
		 public Integer getPriority(P p, S s);
	 }

	
	
	private <PRED,SUCC> Set<NestedMap2<IGameState, PRED, WeightedSummaryTargets>> computePredecessorsUnderPly(
			final Set<NestedMap2<IGameState, SUCC, WeightedSummaryTargets>> succNodes,
			final HashRelation<PRED, SUCC> pred2succ,
			final PriorityProvider<PRED, SUCC> priorityProvider,
			final Aggregation aggregation) {
		final Set<NestedMap2<IGameState, PRED, WeightedSummaryTargets>> preds = new HashSet<>();
		for (final NestedMap2<IGameState, SUCC, WeightedSummaryTargets> succNode : succNodes) {
			final List<Pair<IGameState,PRED>> predSourceCurrentPairs = new ArrayList<>();
			final List<List<WeightedSummaryTargets>> predWeightedSummaryTargets = new ArrayList<>();
			for (final IGameState source : succNode.keySet()) {
				final Map<SUCC, WeightedSummaryTargets> current2wst = succNode.get(source);
				addPredecessorsToLists(pred2succ, priorityProvider, current2wst, predSourceCurrentPairs,
						predWeightedSummaryTargets, source, aggregation);

			}
			final int[] numberOfElements = new int[predWeightedSummaryTargets.size()];
			for (int i=0; i<predWeightedSummaryTargets.size(); i++) {
				numberOfElements[i] = predWeightedSummaryTargets.get(i).size();
			}

			final LexicographicCounter c = new LexicographicCounter(numberOfElements);
			do {
				final NestedMap2<IGameState, PRED, WeightedSummaryTargets> pred = 
						new NestedMap2<>();
				final int[] currentCounterValue = c.getCurrentValue();
				for (int i=0; i<currentCounterValue.length; i++) {
					pred.put(predSourceCurrentPairs.get(i).getFirst(), predSourceCurrentPairs.get(i).getSecond(), predWeightedSummaryTargets.get(i).get(currentCounterValue[i]));
				}
				preds.add(pred);
				c.increment();
			} while (!c.isZero());
			assert c.getNumberOfValuesProduct() == preds.size() : "inconsistent";
		}
		mLogger.info(preds.size() + " predecessors under ply");
		return preds;
	}


	private <SUCC, PRED> void addPredecessorsToLists(final HashRelation<PRED, SUCC> pred2succ,
			final PriorityProvider<PRED, SUCC> priorityProvider,
			final Map<SUCC, WeightedSummaryTargets> succNode,
			final List<Pair<IGameState, PRED>> predSourceCurrentPairs,
			final List<List<WeightedSummaryTargets>> predWeightedSummaryTargets,
			final IGameState source,
			final Aggregation aggregation) {
		for (final PRED pred : pred2succ.getDomain()) {
			final Set<WeightedSummaryTargets> weightedSummaryTargetsSet = new HashSet<>();
			final Set<SUCC> succs = pred2succ.getImage(pred);
			for (final SUCC succ : succs) {
				final WeightedSummaryTargets wst = succNode.get(succ);
				if (wst == null) {
					// omit, succ not in succNode
				} else {
					final int predPriority = priorityProvider.getPriority(pred, succ);
					weightedSummaryTargetsSet.add(wst.computeUpdate(predPriority));
				}
			}
			if (weightedSummaryTargetsSet.isEmpty()) {
				// omit, there was not a single successor of pred in succNode
			} else {
				final List<WeightedSummaryTargets> aggregated = 
						aggregation.aggregate(weightedSummaryTargetsSet);
				predSourceCurrentPairs.add(new Pair<IGameState, PRED>(source, pred));
				predWeightedSummaryTargets.add(aggregated);
			}
		}
	}
	
	 @FunctionalInterface
	 interface Aggregation {
		 public List<WeightedSummaryTargets> aggregate(Set<WeightedSummaryTargets> weightedSummaryTargetsSet);
	 }


	private List<WeightedSummaryTargets> spoilerAggregration(
			final Set<WeightedSummaryTargets> weightedSummaryTargetsSet) {
		return PosetUtils.filterMinimalElements(weightedSummaryTargetsSet, mWeightedSummaryTargetsComparator).collect(Collectors.toList());
	}
	
	private List<WeightedSummaryTargets> duplicatorAggregration(
			final Set<WeightedSummaryTargets> weightedSummaryTargetsSet) {
		final Map<IGameState, Integer> target2priority = new HashMap<>();
		for (final WeightedSummaryTargets wst : weightedSummaryTargetsSet) {
			for (final Entry<IGameState, Integer> entry : wst.entrySet()) {
				final Integer oldPrio = target2priority.get(entry.getKey());
				Integer resultPrio;
				if (oldPrio == null) {
					resultPrio = oldPrio;
				} else {
					if (new PriorityComparator().compare(oldPrio, entry.getValue()) >= 0) {
						resultPrio = oldPrio;
					} else {
						resultPrio = entry.getValue();
					}
				}
				target2priority.put(entry.getKey(), resultPrio);
			}
		}
		return Collections.singletonList(new WeightedSummaryTargets(target2priority));
	}

	
	
	
}
