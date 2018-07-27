/*
 * Copyright (C) 2015 Jeffery Hsu (a71128@gmail.com)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.incrementalinclusion;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.ITransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * This is an implementation of incremental inclusion check based on the Bn baseline Algorithm.<br/>
 * We use InclusionViaDIfference to check its correctness.
 *
 * @author jefferyyjhsu@iis.sinica.edu.tw
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class IncrementalInclusionCheck2DeadEndRemovalAdvanceCover_2Stacks_multipleCounterExamplesAtOnce<LETTER, STATE>
		extends AbstractIncrementalInclusionCheck<LETTER, STATE>
		implements IOperation<LETTER, STATE, IIncrementalInclusionStateFactory<STATE>> {
	public int counter_run = 0, counter_total_nodes = 0;
	public PseudoAutomata workingAutomata;
	public LinkedList<PseudoAutomata> prvPAutomaton;
	public int nodeNumberBeforeDelete = 0;
	public int totalNodes = 0, totalAACNodes = 0, totalCoveredNodes = 0, totalUniqueNodes = 0;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> local_mA;
	private INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> current_mB;
	private final LinkedList<INwaOutgoingLetterAndTransitionProvider<LETTER, STATE>> union_mBs;
	private final List<INwaOutgoingLetterAndTransitionProvider<LETTER, STATE>> local_mB;
	private final List<INwaOutgoingLetterAndTransitionProvider<LETTER, STATE>> local_mB2;
	private final IDeterminizeStateFactory<STATE> localStateFactory;
	private final AutomataLibraryServices localServiceProvider;
	private int counterExampleFlag;
	private final boolean macc;

	class NfaUnion implements IOperation<LETTER, STATE, IStateFactory<STATE>> {
		public IEmptyStackStateFactory<STATE> stateFactory;
		INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> orgin, target;
		NestedWordAutomaton<LETTER, STATE> result;
		Collection<STATE> state1, state2;
		Collection<LETTER> letter1, letter2;
		Set<LETTER> newLetterSet;
		private final AutomataLibraryServices mServices;

		public NfaUnion(final AutomataLibraryServices services, final IEmptyStackStateFactory<STATE> sf,
				final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> in1,
				final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> in2) {
			mServices = services;
			stateFactory = sf;
			mLogger.info(startMessage());
			orgin = in1;
			target = in2;
			letter1 = orgin.getVpAlphabet().getInternalAlphabet();
			letter2 = target.getVpAlphabet().getInternalAlphabet();
			newLetterSet = new HashSet<>();
			newLetterSet.addAll(letter1);
			newLetterSet.addAll(letter2);
			union();
			mLogger.info(exitMessage());
		}

		public void union() {
			result = new NestedWordAutomaton<LETTER, STATE>(mServices, new VpAlphabet<LETTER>(newLetterSet), stateFactory);
			final HashSet<STATE> currentStates = new HashSet<>();
			final HashSet<STATE> nextRoundStates = new HashSet<>();
			final HashSet<STATE> finishedStates = new HashSet<>();
			currentStates.addAll((Collection<? extends STATE>) orgin.getInitialStates());
			finishedStates.addAll(currentStates);
			do {
				for (final STATE a : currentStates) {
					result.addState(orgin.isInitial(a), orgin.isFinal(a), a);
					for (final OutgoingInternalTransition<LETTER, STATE> tran : orgin.internalSuccessors(a)) {
						result.addInternalTransition(a, tran.getLetter(), tran.getSucc());
						if (!finishedStates.contains(tran.getSucc())) {
							nextRoundStates.add(tran.getSucc());
							finishedStates.add(tran.getSucc());
						}
					}
				}
				if (nextRoundStates.isEmpty()) {
					break;
				} else {
					currentStates.clear();
					currentStates.addAll(nextRoundStates);
					nextRoundStates.clear();
				}
			} while (true);
			finishedStates.clear();
			currentStates.clear();
			nextRoundStates.clear();
			currentStates.addAll((Collection<? extends STATE>) target.getInitialStates());
			finishedStates.addAll(currentStates);
			do {
				for (final STATE a : currentStates) {
					result.addState(target.isInitial(a), target.isFinal(a), a);
					for (final OutgoingInternalTransition<LETTER, STATE> tran : target.internalSuccessors(a)) {
						result.addInternalTransition(a, tran.getLetter(), tran.getSucc());
						if (!finishedStates.contains(tran.getSucc())) {
							nextRoundStates.add(tran.getSucc());
							finishedStates.add(tran.getSucc());
						}
					}
				}
				if (nextRoundStates.isEmpty()) {
					break;
				} else {
					currentStates.clear();
					currentStates.addAll(nextRoundStates);
					nextRoundStates.clear();
				}
			} while (true);
			/*
			 * for(STATE a:state1){ result.addState(orgin.getInitialStates().contains(a),
			 * orgin.getFinalStates().contains(a), a); } for(STATE a:state2){
			 * result.addState(target.getInitialStates().contains(a), target.getFinalStates().contains(a), a); }
			 * for(STATE x:state1){ for(OutgoingInternalTransition<LETTER, STATE> y:orgin.internalSuccessors(x)){
			 * result.addInternalTransition(x, y.getLetter(), y.getSucc()); } } for(STATE x:state2){
			 * for(OutgoingInternalTransition<LETTER, STATE> y:target.internalSuccessors(x)){
			 * result.addInternalTransition(x, y.getLetter(), y.getSucc()); } }
			 */
		}

		@Override
		public String startMessage() {
			return "Start " + getOperationName();
		}

		@Override
		public String exitMessage() {
			return "Exit " + getOperationName();
		}

		@Override
		public INestedWordAutomaton<LETTER, STATE> getResult() {
			return result;
		}

		@Override
		public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataOperationCanceledException {
			return true;
		}

	}

	class PseudoAutomata {
		public INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> associatedAutomata;
		public PseudoAutomata prvPAutomata;
		public Set<LETTER> letter;
		public HashSet<NodeData> allNodes;
		public LinkedList<NodeData> errorNodes, errorNodes2, currentTree, stack2;
		// public LinkedList<NodeData> completeTree,coveredNodes,ACCNodes;
		public LinkedList<NodeData> coveredNodes;
		public HashMap<NodeData, LinkedList<NodeData>> completeTree, ACCNodes;
		public HashSet<NodeData> initialNodes;
		public boolean testing_newAcceptingState = false;

		public PseudoAutomata(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> a)
				throws AutomataOperationCanceledException {
			associatedAutomata = a;
			prvPAutomata = null;
			letter = a.getAlphabet();
			allNodes = new HashSet<>();
			errorNodes = new LinkedList<>();
			errorNodes2 = new LinkedList<>();
			stack2 = new LinkedList<>();
			completeTree = new HashMap<>();
			coveredNodes = new LinkedList<>();
			ACCNodes = new HashMap<>();
			currentTree = expand(true, true);
			initialNodes = new HashSet<>(currentTree);
			do {
				if (cover(macc)) {
					break;
				}
				currentTree = expand(true, false);
			} while (true);
		}

		public PseudoAutomata(final PseudoAutomata preAutomata, final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> bn)
				throws AutomataOperationCanceledException {
			associatedAutomata = bn;
			prvPAutomata = preAutomata;
			allNodes = new HashSet<>();
			errorNodes = new LinkedList<>();
			errorNodes2 = new LinkedList<>();
			stack2 = new LinkedList<>();
			completeTree = new HashMap<>();
			coveredNodes = new LinkedList<>();
			ACCNodes = new HashMap<>();
			letter = prvPAutomata.getAlphabet();
			if (!letter.equals(bn.getAlphabet())) {
				mLogger.info("Alphabet inconsistent");
				return;
			}
			prvPAutomata.deadendRemove();
			final HashMap<NodeData, LinkedList<NodeData>> finishTheseACCFirst = new HashMap<>();
			for (final NodeData node : prvPAutomata.ACCNodes.keySet()) {
				for (final NodeData node2 : prvPAutomata.ACCNodes.get(node)) {
					if (node2.keep && !node2.parentNode.keep_Hard) {
						// finishTheseACCFirst2.add(node2);
						if (!finishTheseACCFirst.keySet().contains(node2.parentNode)) {
							finishTheseACCFirst.put(node2.parentNode, new LinkedList<NodeData>());
						}
						finishTheseACCFirst.get(node2.parentNode).add(node2);
					}
				}
			}
			for (final NodeData parentNode : finishTheseACCFirst.keySet()) {
				prvPAutomata.finishACCover2(parentNode, finishTheseACCFirst.get(parentNode));
			}
			if (!finishTheseACCFirst.isEmpty()) {
				prvPAutomata.deadendRemove();
			}
			currentTree = expand(false, true);
			initialNodes = new HashSet<>(currentTree);
			do {
				calculateAcceptingStates();
				if (cover(macc)) {
					if (!stack2.isEmpty()) {
						final HashSet<NodeData> prvNodesToBeFinish = new HashSet<>();
						for (final NodeData stack2Nodes : stack2) {
							prvNodesToBeFinish.add(stack2Nodes.aState);
						}
						preAutomata.finishACCover(prvNodesToBeFinish);
						currentTree.clear();
						currentTree.addAll(stack2);
						do {
							currentTree = expand(false, false);
							calculateAcceptingStates();
							if (cover(macc)) {
								break;
							}
						} while (true);
					}
					break;
				}
				currentTree = expand(false, false);
			} while (true);
			// deadendRemove();
			// //HashSet<NodeData> finishTheseACCFirst2 = new HashSet<NodeData>();
			// HashMap<NodeData,LinkedList<NodeData>> finishTheseACCFirst = new
			// HashMap<NodeData,LinkedList<NodeData>>();
			// for(NodeData node :ACCNodes.keySet()){
			// for(NodeData node2 : ACCNodes.get(node)){
			// if(node2.keep&&!node2.parentNode.keep_Hard){
			// //finishTheseACCFirst2.add(node2);
			// if(!finishTheseACCFirst.keySet().contains(node2.parentNode)){
			// finishTheseACCFirst.put(node2.parentNode, new LinkedList<NodeData>());
			// }
			// finishTheseACCFirst.get(node2.parentNode).add(node2);
			// }
			// }
			// }
			// //finishACCover(finishTheseACCFirst2);
			// for(NodeData parentNode : finishTheseACCFirst.keySet()){
			// finishACCover2(parentNode,finishTheseACCFirst.get(parentNode));
			// }
			// deadendRemove();
			// 記得改回比較快的位置(有下一個iteration再做deadend remove) (還要改finishACC)
		}

		@SuppressWarnings("unchecked")
		public LinkedList<NodeData> expand(final boolean iteration1, final boolean init)
				throws AutomataOperationCanceledException {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}
			final LinkedList<NodeData> newNodes = new LinkedList<>();
			NodeData tempNodeData;
			if (iteration1) {
				if (init) {
					for (final STATE initStateA : associatedAutomata.getInitialStates()) {
						tempNodeData = new NodeData();
						totalNodes++;
						if (associatedAutomata.isFinal(initStateA)) {
							tempNodeData.accepting = true;
							errorNodes.add(tempNodeData);
							errorNodes2.add(tempNodeData);
							testing_newAcceptingState = true;
						} else {
							tempNodeData.accepting = false;
						}
						tempNodeData.parentNode = null;
						tempNodeData.aState = null;
						tempNodeData.bStates.add(initStateA);
						tempNodeData.correspondingAState = initStateA;
						tempNodeData.hash = initStateA.hashCode();
						tempNodeData.word = new NestedRun<>(initStateA);
						newNodes.add(tempNodeData);
						allNodes.add(tempNodeData);
					}
				} else {
					for (final NodeData preNode : currentTree) {
						if (preNode.coveredBy == null) {
							assert preNode.bStates.size() == 1;
							for (final STATE s : preNode.bStates) {
								for (final OutgoingInternalTransition<LETTER, STATE> ATransition : associatedAutomata
										.internalSuccessors(s)) {
									tempNodeData = new NodeData();
									totalNodes++;
									if (associatedAutomata.isFinal(ATransition.getSucc())) {
										tempNodeData.accepting = true;
										errorNodes.add(tempNodeData);
										errorNodes2.add(tempNodeData);
										testing_newAcceptingState = true;
									} else {
										tempNodeData.accepting = false;
									}
									tempNodeData.parentNode = preNode;
									tempNodeData.aState = null;
									tempNodeData.correspondingAState = ATransition.getSucc();
									tempNodeData.bStates.add(ATransition.getSucc());
									tempNodeData.hash = ATransition.getSucc().hashCode();
									final ArrayList<STATE> newStateSequence =
											(ArrayList<STATE>) preNode.word.getStateSequence().clone();
									newStateSequence.add(ATransition.getSucc());
									tempNodeData.word =
											new NestedRun<>(
													preNode.word.getWord()
															.concatenate(new NestedWord<>(ATransition.getLetter(), -2)),
													newStateSequence);
									newNodes.add(tempNodeData);
									allNodes.add(tempNodeData);
								}
							}
						}
					}
				}
			} else {
				if (init) {
					final HashSet<STATE> bStates = new HashSet<>();
					int BHash = 0;
					for (final STATE BState : associatedAutomata.getInitialStates()) {
						bStates.add(BState);
						BHash = BHash | BState.hashCode();
					}
					for (final NodeData initNode : prvPAutomata.initialNodes) {
						if (initNode.keep == true) {
							tempNodeData = new NodeData();
							totalNodes++;
							tempNodeData.parentNode = null;
							tempNodeData.aState = initNode;
							tempNodeData.correspondingAState = initNode.correspondingAState;
							tempNodeData.bStates = (HashSet<STATE>) bStates.clone();
							tempNodeData.hash = BHash;
							tempNodeData.word = new NestedRun<>(tempNodeData.correspondingAState);
							newNodes.add(tempNodeData);
							allNodes.add(tempNodeData);
						}
					}
				} else {
					for (final NodeData preNode : currentTree) {
						if (preNode.coveredBy == null) {
							for (final Transition tran : prvPAutomata.internalSuccessors(preNode.aState)) {
								if (tran.getSucc().keep == true) {
									tempNodeData = new NodeData();
									totalNodes++;
									tempNodeData.parentNode = preNode;
									tempNodeData.aState = tran.getSucc();
									tempNodeData.correspondingAState = tran.getSucc().correspondingAState;
									for (final STATE preBState : preNode.bStates) {
										for (final OutgoingInternalTransition<LETTER, STATE> BTransition : associatedAutomata
												.internalSuccessors(preBState, tran.getLetter())) {
											tempNodeData.bStates.add(BTransition.getSucc());
											tempNodeData.hash = tempNodeData.hash | BTransition.getSucc().hashCode();
										}
									}
									final ArrayList<STATE> newStateSequence =
											(ArrayList<STATE>) preNode.word.getStateSequence().clone();
									newStateSequence.add(tempNodeData.correspondingAState);
									tempNodeData.word = new NestedRun<>(
											preNode.word.getWord().concatenate(new NestedWord<>(tran.getLetter(), -2)),
											newStateSequence);
									newNodes.add(tempNodeData);
									allNodes.add(tempNodeData);
								}
							}
						}
					}
				}
			}
			return newNodes;
		}

		public void calculateAcceptingStates() throws AutomataOperationCanceledException {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}
			for (final NodeData currentNodeSet1 : currentTree) {
				if (currentNodeSet1.aState.accepting) {
					currentNodeSet1.accepting = true;
					for (final STATE state : currentNodeSet1.bStates) {
						if (associatedAutomata.isFinal(state)) {
							currentNodeSet1.accepting = false;
							break;
						}
					}
					if (currentNodeSet1.accepting == true) {
						errorNodes.add(currentNodeSet1);
						errorNodes2.add(currentNodeSet1);
						testing_newAcceptingState = true;
					}
				} else {
					currentNodeSet1.accepting = false;
				}
			}
		}

		public boolean cover(final boolean acc) throws AutomataOperationCanceledException {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}
			// cover() will need to write appropriate outgoing transition for previous nodes
			boolean newNodeInCompleteTree = false;
			boolean containsAllbnState = false;
			// NodeData currentNodeSet1 = null,potenialACCCandidate = null;
			NodeData potenialACCCandidate = null;
			final LinkedList<NodeData> toBeDeleteed = new LinkedList<>();
			// int i,j;
			// for(i=0;i<currentTree.size();i++){
			// currentNodeSet1 = currentTree.get(i);
			for (final NodeData currentNodeSet1 : currentTree) {
				containsAllbnState = false;
				potenialACCCandidate = null;
				if (completeTree.containsKey(currentNodeSet1.aState)) {
					for (final NodeData completeNodeSet : completeTree.get(currentNodeSet1.aState)) {
						if (completeNodeSet.hash == (currentNodeSet1.hash & completeNodeSet.hash)
								&& currentNodeSet1.bStates.size() >= completeNodeSet.bStates.size()) {
							if (currentNodeSet1.bStates.containsAll(completeNodeSet.bStates)) {
								if (currentNodeSet1.bStates.size() == completeNodeSet.bStates.size()) {
									containsAllbnState = true;
									totalCoveredNodes++;
									currentNodeSet1.coveredBy = completeNodeSet;
									currentNodeSet1.identicalCover = true;
									completeNodeSet.covering.add(currentNodeSet1);
									if (currentNodeSet1.parentNode != null) {
										currentNodeSet1.parentNode.outgoingTransition.add(new Transition(
												currentNodeSet1.word.getSymbol(currentNodeSet1.word.getLength() - 2),
												completeNodeSet));
									}
									coveredNodes.add(currentNodeSet1);
									// toBeDeleteed.add(currentNodeSet1);
									break;
								} else {
									if (acc) {
										currentNodeSet1.ACCPotentialCoverBy.add(completeNodeSet);
										if (potenialACCCandidate == null || potenialACCCandidate.bStates
												.size() > completeNodeSet.bStates.size()) {
											potenialACCCandidate = completeNodeSet;
										}
									}
								}
							}
						}
					}
				}
				if (acc && !containsAllbnState) {
					if (ACCNodes.containsKey(currentNodeSet1.aState)) {
						for (final NodeData completeNodeSet : ACCNodes.get(currentNodeSet1.aState)) {
							if (completeNodeSet.hash == (currentNodeSet1.hash & completeNodeSet.hash)
									&& currentNodeSet1.bStates.size() == completeNodeSet.bStates.size()) {
								if (currentNodeSet1.bStates.containsAll(completeNodeSet.bStates)) {
									containsAllbnState = true;
									totalCoveredNodes++;
									currentNodeSet1.coveredBy = completeNodeSet;
									currentNodeSet1.identicalCover = true;
									completeNodeSet.covering.add(currentNodeSet1);
									if (currentNodeSet1.parentNode != null) {
										currentNodeSet1.parentNode.outgoingTransition.add(new Transition(
												currentNodeSet1.word.getSymbol(currentNodeSet1.word.getLength() - 2),
												completeNodeSet));
									}
									coveredNodes.add(currentNodeSet1);
									// toBeDeleteed.add(currentNodeSet1);
									break;
								}
							}
						}
					}
				}
				if (acc && !containsAllbnState) {
					for (final NodeData currentNodeSet2 : currentTree) {
						if (currentNodeSet1 != currentNodeSet2 && currentNodeSet2.coveredBy == null
								&& currentNodeSet1.aState == currentNodeSet2.aState
								&& currentNodeSet2.hash == (currentNodeSet1.hash & currentNodeSet2.hash)
								&& currentNodeSet1.bStates.size() > currentNodeSet2.bStates.size()) {
							if (currentNodeSet1.bStates.containsAll(currentNodeSet2.bStates)) {
								currentNodeSet1.ACCPotentialCoverBy.add(currentNodeSet2);
								if (potenialACCCandidate == null
										|| potenialACCCandidate.bStates.size() > currentNodeSet2.bStates.size()) {
									potenialACCCandidate = currentNodeSet2;
								}
							}
						}
					}
					if (currentNodeSet1.aState != null && currentNodeSet1.aState.coveredBy != null) {
						for (final NodeData ACCANodes : currentNodeSet1.aState.ACCPotentialCoverBy) {
							if (completeTree.containsKey(ACCANodes)) {
								for (final NodeData completeNodeSet : completeTree.get(ACCANodes)) {
									if (completeNodeSet.hash == (currentNodeSet1.hash & completeNodeSet.hash)
											&& currentNodeSet1.bStates.size() >= completeNodeSet.bStates.size()) {
										if (currentNodeSet1.bStates.containsAll(completeNodeSet.bStates)) {
											currentNodeSet1.ACCPotentialCoverBy.add(completeNodeSet);
											if (acc == true
													&& (potenialACCCandidate == null || potenialACCCandidate.bStates
															.size() > completeNodeSet.bStates.size())) {
												potenialACCCandidate = completeNodeSet;
											}
										}
									}
								}
							}
							for (final NodeData currentNodeSet2 : currentTree) {
								if (currentNodeSet1 != currentNodeSet2 && currentNodeSet2.coveredBy == null
										&& ACCANodes == currentNodeSet2.aState
										&& currentNodeSet2.hash == (currentNodeSet1.hash & currentNodeSet2.hash)
										&& currentNodeSet1.bStates.size() >= currentNodeSet2.bStates.size()) {
									if (currentNodeSet1.bStates.containsAll(currentNodeSet2.bStates)) {
										currentNodeSet1.ACCPotentialCoverBy.add(currentNodeSet2);
										if (potenialACCCandidate == null || potenialACCCandidate.bStates
												.size() > currentNodeSet2.bStates.size()) {
											potenialACCCandidate = currentNodeSet2;
										}
									}
								}
							}
						}
					}
				}
				if (!containsAllbnState) {
					if (potenialACCCandidate == null || acc == false) {
						newNodeInCompleteTree = true;
						if (!completeTree.containsKey(currentNodeSet1.aState)) {
							completeTree.put(currentNodeSet1.aState, new LinkedList<NodeData>());
						}
						completeTree.get(currentNodeSet1.aState).addFirst(currentNodeSet1);
						totalUniqueNodes++;
						if (currentNodeSet1.parentNode != null) {
							currentNodeSet1.parentNode.outgoingTransition.add(
									new Transition(currentNodeSet1.word.getSymbol(currentNodeSet1.word.getLength() - 2),
											currentNodeSet1));
						}
						if (currentNodeSet1.aState != null && currentNodeSet1.aState.coveredBy != null) {
							stack2.add(currentNodeSet1);
							toBeDeleteed.add(currentNodeSet1);
						}
					} else {
						totalAACNodes++;
						currentNodeSet1.coveredBy = potenialACCCandidate;
						currentNodeSet1.identicalCover = false;
						potenialACCCandidate.covering.add(currentNodeSet1);
						if (currentNodeSet1.parentNode != null) {
							currentNodeSet1.parentNode.outgoingTransition.add(
									new Transition(currentNodeSet1.word.getSymbol(currentNodeSet1.word.getLength() - 2),
											currentNodeSet1));
						}
						if (!ACCNodes.containsKey(currentNodeSet1.aState)) {
							ACCNodes.put(currentNodeSet1.aState, new LinkedList<NodeData>());
						}
						ACCNodes.get(currentNodeSet1.aState).addFirst(currentNodeSet1);
						// toBeDeleteed.add(currentNodeSet1);
					}
				}
			}
			currentTree.removeAll(toBeDeleteed);
			return !newNodeInCompleteTree;
		}

		public void finishACCover(final HashSet<NodeData> nodes) throws AutomataOperationCanceledException {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}
			final HashSet<NodeData> nodesToBeFinishedFirst = new HashSet<>();
			currentTree.clear();
			for (final NodeData key : nodes) {
				ACCNodes.get(key.aState).remove(key);
				if (!completeTree.containsKey(key.aState)) {
					completeTree.put(key.aState, new LinkedList<NodeData>());
				}
				completeTree.get(key.aState).add(key);
				totalAACNodes--;
				totalUniqueNodes++;
				key.coveredBy.covering.remove(key);
				key.coveredBy = null;
				if (key.aState != null && key.aState.coveredBy != null) {
					nodesToBeFinishedFirst.add(key.aState);
				}
			}
			currentTree.addAll(nodes);
			if (!nodesToBeFinishedFirst.isEmpty() && prvPAutomata != null) {
				prvPAutomata.finishACCover(nodesToBeFinishedFirst);
			}
			do {
				if (prvPAutomata == null) {
					currentTree = expand(true, false);
					if (cover(false)) {
						deadendRemove();
						break;
					}
				} else {
					currentTree = expand(false, false);
					calculateAcceptingStates();
					if (cover(false)) {
						deadendRemove();
						break;
					}
				}
			} while (true);
		}

		public void finishACCover2(final NodeData parentNode, final LinkedList<NodeData> nodes)
				throws AutomataOperationCanceledException {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}
			final HashSet<NodeData> nodesToBeFinishedFirst = new HashSet<>();
			for (final NodeData key : nodes) {
				testing_newAcceptingState = false;
				currentTree.clear();
				currentTree.add(key);
				ACCNodes.get(key.aState).remove(key);
				if (!completeTree.containsKey(key.aState)) {
					completeTree.put(key.aState, new LinkedList<NodeData>());
				}
				completeTree.get(key.aState).add(key);
				totalAACNodes--;
				totalUniqueNodes++;
				key.coveredBy.covering.remove(key);
				key.coveredBy = null;
				if (key.aState != null && key.aState.coveredBy != null) {
					nodesToBeFinishedFirst.add(key.aState);
					prvPAutomata.finishACCover(nodesToBeFinishedFirst);
				}
				do {
					if (prvPAutomata == null) {
						currentTree = expand(true, false);
						if (cover(false)) {
							// deadendRemove();
							break;
						}
					} else {
						currentTree = expand(false, false);
						calculateAcceptingStates();
						if (cover(false)) {
							// deadendRemove();
							break;
						}
					}
				} while (true);
				if (testing_newAcceptingState == true) {
					break;
				}
			}
		}

		// private HashSet<NodeData> toBeKeepedNodes;

		public void deadendRemove() {
			// toBeKeepedNodes = new HashSet<NodeData>();
			// HashSet<NodeData> toBeDeletedNodes = new HashSet<NodeData>(allNodes);
			int i = 0;
			for (final NodeData node : completeTree.keySet()) {
				for (final NodeData node2 : completeTree.get(node)) {
					if (node2.keep) {
						i++;
					}
				}
			}
			for (final NodeData node : ACCNodes.keySet()) {
				for (final NodeData node2 : ACCNodes.get(node)) {
					if (node2.keep) {
						i++;
					}
				}
			}
			mLogger.info("Nodes before: " + i);
			for (final NodeData nodes : allNodes) {
				nodes.keep = false;
				nodes.keep_Hard = false;
			}
			for (final NodeData errorNode : errorNodes2) {
				deadEndRemoveWalker(errorNode, true);
			}
			i = 0;
			for (final NodeData node : completeTree.keySet()) {
				for (final NodeData node2 : completeTree.get(node)) {
					if (node2.keep) {
						i++;
					}
				}
			}
			for (final NodeData node : ACCNodes.keySet()) {
				for (final NodeData node2 : ACCNodes.get(node)) {
					if (node2.keep) {
						i++;
					}
				}
			}
			mLogger.info("Nodes After: " + i);
			/*
			 * toBeDeletedNodes.removeAll(toBeKeepedNodes); for(NodeData nodeToBeDelete : toBeDeletedNodes){ Transition
			 * removeTran = null; if(nodeToBeDelete.identicalCover){ if(nodeToBeDelete.parentNode!=null){ for(Transition
			 * tran: nodeToBeDelete.parentNode.outgoingTransition){ if(tran.getSucc() == nodeToBeDelete.coveredBy){
			 * removeTran = tran; break; } } nodeToBeDelete.parentNode.outgoingTransition.remove(removeTran); } }else{
			 * if(nodeToBeDelete.parentNode!=null){ for(Transition tran: nodeToBeDelete.parentNode.outgoingTransition){
			 * if(tran.getSucc() == nodeToBeDelete){ removeTran = tran; break; } }
			 * nodeToBeDelete.parentNode.outgoingTransition.remove(removeTran); } }
			 * if(completeTree.contains(nodeToBeDelete)){ completeTree.remove(nodeToBeDelete); }else{
			 * if(coveredNodes.contains(nodeToBeDelete)){ coveredNodes.remove(nodeToBeDelete); } }
			 * if(nodeToBeDelete.parentNode!=null){ nodeToBeDelete.parentNode.DeadEndsRemoved = true; } }
			 * allNodes.removeAll(toBeDeletedNodes);
			 */
		}

		private void deadEndRemoveWalker(final NodeData node, final boolean hard) {
			assert node != null;
			if (!node.keep) {
				node.keep_Hard = hard;
				node.keep = true;
				// toBeKeepedNodes.add(node);
				for (final NodeData coveringNode : node.covering) {
					if (coveringNode.identicalCover) {
						deadEndRemoveWalker(coveringNode, hard);
					} else {
						deadEndRemoveWalker(coveringNode, false);
					}
				}
				if (node.parentNode != null) {
					deadEndRemoveWalker(node.parentNode, hard);
				}
			} else {
				if (hard && !node.keep_Hard) {
					node.keep_Hard = hard;
					for (final NodeData coveringNode : node.covering) {
						if (coveringNode.identicalCover) {
							deadEndRemoveWalker(coveringNode, hard);
						}
					}
					if (node.parentNode != null) {
						deadEndRemoveWalker(node.parentNode, hard);
					}
				}
			}
		}

		public Set<LETTER> getAlphabet() {
			return letter;
		}

		public Set<NodeData> getInitialStates() {
			return initialNodes;
		}

		public LinkedList<Transition> internalSuccessors(final NodeData node)
				throws AutomataOperationCanceledException {
			/*
			 * if(node.coveredBy!=null){ HashSet<NodeData> n = new HashSet<NodeData>(); n.add(node); finishACCover(n); }
			 */
			return node.outgoingTransition;
		}

		public LinkedList<Transition> internalSuccessors(final NodeData node, final LETTER let)
				throws AutomataOperationCanceledException {
			/*
			 * if(node.coveredBy!=null){ HashSet<NodeData> n = new HashSet<NodeData>(); n.add(node); finishACCover(n); }
			 */
			final LinkedList<Transition> result = new LinkedList<>();
			for (final Transition tran : node.outgoingTransition) {
				if (tran.getLetter().equals(let)) {
					result.add(tran);
				}
			}
			return result;
		}
	}

	class Transition implements ITransitionlet<LETTER, STATE> {
		private final LETTER letter;
		private final NodeData succ;

		public Transition(final LETTER let, final NodeData node) {
			letter = let;
			succ = node;
		}

		@Override
		public LETTER getLetter() {
			return letter;
		}

		public NodeData getSucc() {
			return succ;
		}
	}

	class NodeData {
		public boolean DeadEndsRemoved;
		public boolean keep, keep_Hard;
		public int hash;
		public NodeData coveredBy = null;
		public HashSet<NodeData> ACCPotentialCoverBy;
		public boolean accepting;
		public NodeData parentNode;
		public boolean identicalCover;
		public HashSet<NodeData> covering;
		public NodeData aState;
		public STATE correspondingAState;
		public HashSet<STATE> bStates;
		public LinkedList<Transition> outgoingTransition;
		public NestedRun<LETTER, STATE> word;

		public NodeData() {
			keep = true;
			keep_Hard = false;
			identicalCover = false;
			DeadEndsRemoved = false;
			bStates = new HashSet<>();
			word = null;
			covering = new HashSet<>();
			ACCPotentialCoverBy = new HashSet<>();
			outgoingTransition = new LinkedList<>();
			hash = 0;
			accepting = false;
		}
	}

	@SuppressWarnings({ "unchecked", "rawtypes" })
	public IncrementalInclusionCheck2DeadEndRemovalAdvanceCover_2Stacks_multipleCounterExamplesAtOnce(
			final AutomataLibraryServices services, final IDeterminizeStateFactory<STATE> sf,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> a, final List<INwaOutgoingLetterAndTransitionProvider<LETTER, STATE>> b,
			final boolean acc) throws AutomataLibraryException {
		super(services, a);
		IncrementalInclusionCheck2DeadEndRemovalAdvanceCover_2Stacks_multipleCounterExamplesAtOnce
				.abortIfContainsCallOrReturn(a);
		counterExampleFlag = 0;
		macc = acc;
		localServiceProvider = services;
		localStateFactory = sf;
		mLogger.info(startMessage());
		local_mA = a;
		local_mB = new ArrayList<>();
		local_mB2 = new ArrayList<>();
		union_mBs = new LinkedList<>();
		current_mB = null;
		prvPAutomaton = new LinkedList<>();
		workingAutomata = new PseudoAutomata(local_mA);
		prvPAutomaton.add(workingAutomata);
		for (final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> bn : b) {
			try {
				super.addSubtrahend(bn);
			} catch (final AutomataLibraryException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			local_mB.add(bn);
			local_mB2.add(bn);
			if (current_mB == null) {
				current_mB = bn;
			} else {
				current_mB = new NfaUnion(localServiceProvider, localStateFactory, current_mB, bn).getResult();
			}
		}
		if (!getResult()) {
			workingAutomata = new PseudoAutomata(workingAutomata, current_mB);
			prvPAutomaton.add(workingAutomata);
		}
		union_mBs.add(current_mB);
		current_mB = null;
		mLogger.info(exitMessage());
	}

	@SuppressWarnings({ "unchecked", "rawtypes" })
	public IncrementalInclusionCheck2DeadEndRemovalAdvanceCover_2Stacks_multipleCounterExamplesAtOnce(
			final AutomataLibraryServices services, final IDeterminizeStateFactory<STATE> sf,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> a, final List<INwaOutgoingLetterAndTransitionProvider<LETTER, STATE>> b)
			throws AutomataLibraryException {
		super(services, a);
		IncrementalInclusionCheck2DeadEndRemovalAdvanceCover_2Stacks_multipleCounterExamplesAtOnce
				.abortIfContainsCallOrReturn(a);
		counterExampleFlag = 0;
		macc = true;
		localServiceProvider = services;
		localStateFactory = sf;
		mLogger.info(startMessage());
		local_mA = a;
		local_mB = new ArrayList<>();
		local_mB2 = new ArrayList<>();
		union_mBs = new LinkedList<>();
		current_mB = null;
		prvPAutomaton = new LinkedList<>();
		workingAutomata = new PseudoAutomata(local_mA);
		prvPAutomaton.add(workingAutomata);
		for (final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> bn : b) {
			try {
				super.addSubtrahend(bn);
			} catch (final AutomataLibraryException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			if (current_mB == null) {
				current_mB = bn;
			} else {
				current_mB = new NfaUnion(localServiceProvider, localStateFactory, current_mB, bn).getResult();
			}
			local_mB.add(bn);
			local_mB2.add(bn);

		}
		if (!getResult() && current_mB != null) {
			workingAutomata = new PseudoAutomata(workingAutomata, current_mB);
			prvPAutomaton.add(workingAutomata);
			union_mBs.add(current_mB);
			current_mB = null;
		}
		mLogger.info(exitMessage());
	}

	@Override
	public void addSubtrahend(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> nwa) throws AutomataLibraryException {
		super.addSubtrahend(nwa);
		local_mB.add(nwa);
		local_mB2.add(nwa);
		if (current_mB == null) {
			current_mB = nwa;
		} else {
			current_mB = new NfaUnion(localServiceProvider, localStateFactory, current_mB, nwa).getResult();
		}
		if (workingAutomata.errorNodes.peekFirst() == null || counterExampleFlag == 2) {
			mLogger.info(startMessage());
			counterExampleFlag = 0;
			workingAutomata = new PseudoAutomata(workingAutomata, current_mB);
			prvPAutomaton.add(workingAutomata);
			union_mBs.add(current_mB);
			current_mB = null;
			mLogger.info(exitMessage());
		}
	}

	@Override
	public NestedRun<LETTER, STATE> getCounterexample() {
		if (workingAutomata.errorNodes.peekFirst() != null) {
			if (counterExampleFlag == 0) {
				counterExampleFlag++;
				return workingAutomata.errorNodes.poll().word;
			} else {
				counterExampleFlag++;
				return workingAutomata.errorNodes.pollLast().word;
			}
		} else {
			return null;
		}

	}

	@Override
	public String getOperationName() {
		return "IncrementalInclusionCheck2DeadEndRemovalAdvanceCover_2Stacks_multipleCounterExamplesAtOnce";
	}

	@Override
	public String startMessage() {
		return "Start " + getOperationName();
	}

	@Override
	public String exitMessage() {
		/*
		 * int i = 0, j = 0; for(INestedWordAutomatonSimple<LETTER, STATE> automata:local_mB){ try { if(!(new
		 * IsDeterministic<LETTER, STATE>(localServiceProvider,automata)).getResult()){ i++; } } catch
		 * (AutomataLibraryException e) { // TODO Auto-generated catch block e.printStackTrace(); } }
		 */
		if (!getResult()) {
			mLogger.info("counterExample: " + workingAutomata.errorNodes.peekFirst().word.getWord().toString());
		}
		mLogger.info("Total: " + totalNodes + " node(s)");
		mLogger.info("Total ACC: " + totalAACNodes + " node(s)");
		mLogger.info("Total IC: " + totalCoveredNodes + " node(s)");
		mLogger.info("Total Unique: " + totalUniqueNodes + " node(s)");
		mLogger.info("Total Iterations: " + prvPAutomaton.size() + " iterations");
		mLogger.info("Total B Automaton: " + local_mB2.size() + " ");
		/*
		 * mLogger.info("Total B Automaton: "+local_mB.size()); mLogger.info("Total non-Deterministic B Automaton: "+i);
		 * i = 0; HashSet<STATE> visitedStates,currentStates,nextStates; for(INestedWordAutomatonSimple<LETTER, STATE>
		 * automata:local_mB){ try { if(!(new IsDeterministic<LETTER,
		 * STATE>(localServiceProvider,automata)).getResult()){ visitedStates = new HashSet<STATE>(); currentStates =
		 * new HashSet<STATE>(); nextStates = new HashSet<STATE>(); nextStates.addAll((Collection<? extends STATE>)
		 * automata.getInitialStates()); do{ currentStates.clear(); currentStates.addAll(nextStates);
		 * nextStates.clear(); for(STATE state:currentStates){ if(!visitedStates.contains(state)){ i++;
		 * visitedStates.add(state); if(!stateDeterministicCheck(automata,state)){ j++; }
		 * for(OutgoingInternalTransition<LETTER, STATE> tran : automata.internalSuccessors(state)){
		 * nextStates.add(tran.getSucc()); } } } }while(!nextStates.isEmpty()); } } catch (AutomataLibraryException e) {
		 * // TODO Auto-generated catch block e.printStackTrace(); } } if(i!=0){ mLogger.info("Total States: "+i);
		 * mLogger.info("Total non-Deterministic States:"+j); mLogger.info("non-Determinism: "+((j*1.0)/(i*1.0))); }
		 */
		return "Exit " + getOperationName();
	}

	private boolean stateDeterministicCheck(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> automata,
			final STATE state) {
		final HashSet<LETTER> visitedLetters = new HashSet<>();
		for (final OutgoingInternalTransition<LETTER, STATE> tran : automata.internalSuccessors(state)) {
			if (visitedLetters.contains(tran.getLetter())) {
				return false;
			} else {
				visitedLetters.add(tran.getLetter());
			}
		}
		return true;
	}

	@Override
	public Boolean getResult() {
		if (workingAutomata.errorNodes.peekFirst() == null) {
			return true;
		} else {
			return false;
		}
	}

	@Override
	public boolean checkResult(final IIncrementalInclusionStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		boolean checkResult;
		if (getCounterexample() != null) {
			checkResult = compareInclusionCheckResult(localServiceProvider, stateFactory, local_mA, local_mB2,
					getCounterexample());
		} else {
			checkResult = compareInclusionCheckResult(localServiceProvider, stateFactory, local_mA, local_mB2, null);
		}
		return checkResult;

	}

	/**
	 * Compare the result of an inclusion check with an inclusion check based on a emptiness/difference operations. The
	 * NestedRun ctrEx is the result of an inclusion check whose inputs are an automaton <b>a</b> and and a list of
	 * automata b. If the language of <b>a</b> is included in the union of all languages of the automata b then ctrEx is
	 * null, otherwise ctrEx is a run of <b>a</b> that is a counterexample to the inclusion. This method returns true if
	 * the difference-based inclusion check comes up with the same result, i.e., if it find a counterexample if ctrEx is
	 * non-null and if it does not find a counterexample if ctrEX is null. Note that if inclusion does not hold, there
	 * may be several counterexamples. Dies method does NOT require that both methods return exactly the same
	 * counterexample.
	 */
	public static <LETTER, STATE> boolean compareInclusionCheckResult(final AutomataLibraryServices services,
			final IIncrementalInclusionStateFactory<STATE> stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> a, final List<INwaOutgoingLetterAndTransitionProvider<LETTER, STATE>> b,
			final NestedRun<LETTER, STATE> ctrEx) throws AutomataLibraryException {
		final InclusionViaDifference<LETTER, STATE, ?> ivd = new InclusionViaDifference<>(services, stateFactory, a);
		// add all b automata
		for (final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> bi : b) {
			ivd.addSubtrahend(bi);
		}
		// obtain counterexample, counterexample is null if inclusion holds
		final NestedRun<LETTER, STATE> ivdCounterexample = ivd.getCounterexample();
		// return true iff both counterexamples are null or both counterexamples
		// are non-null.
		boolean result;
		if (ivdCounterexample == null) {
			if (ctrEx == null) {
				result = true;
			} else {
				result = false;
			}
		} else {
			if (ctrEx == null) {
				result = false;
			} else {
				result = true;
			}
		}
		return result;
	}

	public static <LETTER, STATE> void abortIfContainsCallOrReturn(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> a) {
		if (!NestedWordAutomataUtils.isFiniteAutomaton(a)) {
			throw new UnsupportedOperationException("Operation does not support call or return");
		}
	}
}
