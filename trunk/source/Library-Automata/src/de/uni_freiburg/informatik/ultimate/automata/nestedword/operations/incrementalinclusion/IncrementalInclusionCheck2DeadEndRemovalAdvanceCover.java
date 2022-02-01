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
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.ITransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;

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
public class IncrementalInclusionCheck2DeadEndRemovalAdvanceCover<LETTER, STATE>
		extends AbstractIncrementalInclusionCheck<LETTER, STATE>
		implements IOperation<LETTER, STATE, IIncrementalInclusionStateFactory<STATE>> {
	public int hashTotal = 0, hashSec = 0, hashFail = 0;
	public int counter_run = 0, counter_total_nodes = 0;
	public PseudoAutomata workingAutomata;
	public int nodeNumberBeforeDelete = 0;
	public int totalNodes = 0, totalAACNodes = 0, totalCoveredNodes = 0, totalUniqueNodes = 0;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> local_mA;
	private final List<INwaOutgoingLetterAndTransitionProvider<LETTER, STATE>> local_mB;
	private final List<INwaOutgoingLetterAndTransitionProvider<LETTER, STATE>> local_mB2;
	private final AutomataLibraryServices localServiceProvider;
	private final boolean macc;

	class PseudoAutomata {
		public INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> associatedAutomata;
		public PseudoAutomata prvPAutomata;
		public Set<LETTER> letter;
		public HashSet<NodeData> allNodes;
		public LinkedList<NodeData> errorNodes;
		// public LinkedList<NodeData> completeTree,coveredNodes,ACCNodes;
		public LinkedList<NodeData> coveredNodes, ACCNodes;
		public HashMap<NodeData, LinkedList<NodeData>> completedNodes, currentNodes;
		public HashSet<NodeData> initialNodes;

		public PseudoAutomata(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> a)
				throws AutomataOperationCanceledException {
			associatedAutomata = a;
			prvPAutomata = null;
			letter = a.getAlphabet();
			allNodes = new HashSet<>();
			errorNodes = new LinkedList<>();
			completedNodes = new HashMap<>();
			coveredNodes = new LinkedList<>();
			ACCNodes = new LinkedList<>();
			currentNodes = expand(true, true);
			initialNodes = new HashSet<>();
			for (final NodeData key : currentNodes.keySet()) {
				initialNodes.addAll(currentNodes.get(key));
			}
			do {
				if (cover(macc)) {
					break;
				}
				currentNodes = expand(true, false);
			} while (true);
		}

		public PseudoAutomata(final PseudoAutomata preAutomata, final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> bn)
				throws AutomataOperationCanceledException {
			associatedAutomata = bn;
			prvPAutomata = preAutomata;
			allNodes = new HashSet<>();
			errorNodes = new LinkedList<>();
			completedNodes = new HashMap<>();
			coveredNodes = new LinkedList<>();
			ACCNodes = new LinkedList<>();
			letter = prvPAutomata.getAlphabet();
			if (!letter.equals(bn.getAlphabet())) {
				mLogger.info("Alphabet inconsistent");
				return;
			}
			if (!prvPAutomata.ACCNodes.isEmpty()) {
				prvPAutomata.finishACCover();
			}
			prvPAutomata.deadendRemove();
			currentNodes = expand(false, true);
			initialNodes = new HashSet<>();
			initialNodes = new HashSet<>();
			for (final NodeData key : currentNodes.keySet()) {
				initialNodes.addAll(currentNodes.get(key));
			}
			do {
				// calculateAcceptingStates();
				if (cover(macc)) {
					break;
				}
				currentNodes = expand(false, false);
			} while (true);
		}

		@SuppressWarnings("unchecked")
		public HashMap<NodeData, LinkedList<NodeData>> expand(final boolean iteration1, final boolean init)
				throws AutomataOperationCanceledException {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}
			final HashMap<NodeData, LinkedList<NodeData>> newNodes = new HashMap<>();
			NodeData tempNodeData;
			if (iteration1) {
				if (init) {
					for (final STATE initStateA : associatedAutomata.getInitialStates()) {
						tempNodeData = new NodeData();
						totalNodes++;
						if (associatedAutomata.isFinal(initStateA)) {
							tempNodeData.accepting = true;
							errorNodes.add(tempNodeData);
						} else {
							tempNodeData.accepting = false;
						}
						tempNodeData.parentNode = null;
						tempNodeData.aState = null;
						tempNodeData.bStates.add(initStateA);
						tempNodeData.correspondingAState = initStateA;
						tempNodeData.hash = initStateA.hashCode();
						tempNodeData.word = new NestedRun<>(initStateA);
						if (!newNodes.containsKey(tempNodeData.aState)) {
							newNodes.put(tempNodeData.aState, new LinkedList<NodeData>());
						}
						newNodes.get(tempNodeData.aState).add(tempNodeData);
						allNodes.add(tempNodeData);
					}
				} else {
					for (final NodeData key : currentNodes.keySet()) {
						for (final NodeData preNode : currentNodes.get(key)) {
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
										tempNodeData.word = new NestedRun<>(
												preNode.word.getWord()
														.concatenate(new NestedWord<>(ATransition.getLetter(), -2)),
												newStateSequence);
										if (!newNodes.containsKey(tempNodeData.aState)) {
											newNodes.put(tempNodeData.aState, new LinkedList<NodeData>());
										}
										newNodes.get(tempNodeData.aState).add(tempNodeData);
										allNodes.add(tempNodeData);
									}
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
							if (tempNodeData.aState.accepting) {
								tempNodeData.accepting = true;
								for (final STATE state : tempNodeData.bStates) {
									if (associatedAutomata.isFinal(state)) {
										tempNodeData.accepting = false;
										break;
									}
								}
								if (tempNodeData.accepting == true) {
									errorNodes.add(tempNodeData);
								}
							} else {
								tempNodeData.accepting = false;
							}
							if (!newNodes.containsKey(tempNodeData.aState)) {
								newNodes.put(tempNodeData.aState, new LinkedList<NodeData>());
							}
							newNodes.get(tempNodeData.aState).add(tempNodeData);
							allNodes.add(tempNodeData);
						}
					}
				} else {
					for (final NodeData key : currentNodes.keySet()) {
						for (final NodeData preNode : currentNodes.get(key)) {
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
												tempNodeData.hash =
														tempNodeData.hash | BTransition.getSucc().hashCode();
											}
										}
										final ArrayList<STATE> newStateSequence =
												(ArrayList<STATE>) preNode.word.getStateSequence().clone();
										newStateSequence.add(tempNodeData.correspondingAState);
										tempNodeData.word = new NestedRun<>(preNode.word.getWord()
												.concatenate(new NestedWord<>(tran.getLetter(), -2)), newStateSequence);
										if (tempNodeData.aState.accepting) {
											tempNodeData.accepting = true;
											for (final STATE state : tempNodeData.bStates) {
												if (associatedAutomata.isFinal(state)) {
													tempNodeData.accepting = false;
													break;
												}
											}
											if (tempNodeData.accepting == true) {
												errorNodes.add(tempNodeData);
											}
										} else {
											tempNodeData.accepting = false;
										}
										if (!newNodes.containsKey(tempNodeData.aState)) {
											newNodes.put(tempNodeData.aState, new LinkedList<NodeData>());
										}
										newNodes.get(tempNodeData.aState).add(tempNodeData);
										allNodes.add(tempNodeData);
									}
								}
							}
						}
					}
				}
			}
			return newNodes;
		}

		/*
		 * public void calculateAcceptingStates() throws OperationCanceledException{ if
		 * (!mServices.getProgressMonitorService().continueProcessing()) { throw new
		 * OperationCanceledException(this.getClass()); } for(NodeData key:currentNodes.keySet()){ for(NodeData
		 * currentNodeSet1:currentNodes.get(key)){ if(currentNodeSet1.aState.accepting){ currentNodeSet1.accepting =
		 * true; for(STATE state : currentNodeSet1.bStates){ if(associatedAutomata.isFinal(state)){
		 * currentNodeSet1.accepting = false; break; } } if(currentNodeSet1.accepting == true){
		 * errorNodes.add(currentNodeSet1); } }else{ currentNodeSet1.accepting = false; } } } }
		 */

		public boolean cover(final boolean acc) throws AutomataOperationCanceledException {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}
			// cover() will need to write appropriate outgoing transition for previous nodes
			boolean newNodeInCompleteTree = false;
			boolean containsAllbnState = false;
			// NodeData currentNodeSet1 = null,potenialACCCandidate = null;
			NodeData potenialACCCandidate = null;
			// LinkedList<NodeData> toBeDeleteed = new LinkedList<NodeData>();
			// int i,j;
			// for(i=0;i<currentTree.size();i++){
			// currentNodeSet1 = currentTree.get(i);
			for (final NodeData key : currentNodes.keySet()) {
				for (final NodeData currentNodeSet1 : currentNodes.get(key)) {
					containsAllbnState = false;
					potenialACCCandidate = null;
					if (completedNodes.containsKey(currentNodeSet1.aState)) {
						for (final NodeData completeNodeSet : completedNodes.get(currentNodeSet1.aState)) {
							if (acc) {
								hashTotal++;
								if (completeNodeSet.hash == (currentNodeSet1.hash & completeNodeSet.hash)
										&& currentNodeSet1.bStates.size() >= completeNodeSet.bStates.size()) {
									// if((currentNodeSet1.bStates.size() >= completeNodeSet.bStates.size())){
									// hashtotal++;
									// if(completeNodeSet.hash!=(currentNodeSet1.hash&completeNodeSet.hash)){
									// hashsec ++;
									// }
									if (currentNodeSet1.bStates.containsAll(completeNodeSet.bStates)) {
										hashSec++;
										if (currentNodeSet1.bStates.size() == completeNodeSet.bStates.size()) {
											containsAllbnState = true;
											totalCoveredNodes++;
											currentNodeSet1.coveredBy = completeNodeSet;
											currentNodeSet1.identicalCover = true;
											completeNodeSet.covering.add(currentNodeSet1);
											if (currentNodeSet1.parentNode != null) {
												currentNodeSet1.parentNode.outgoingTransition.add(new Transition(
														currentNodeSet1.word
																.getSymbol(currentNodeSet1.word.getLength() - 2),
														completeNodeSet));
											}
											coveredNodes.add(currentNodeSet1);
											// toBeDeleteed.add(currentNodeSet1);
											break;
										} else {
											if (potenialACCCandidate == null || potenialACCCandidate.bStates
													.size() > completeNodeSet.bStates.size()) {
												potenialACCCandidate = completeNodeSet;
											}
										}
									} else {
										hashFail++;
									}
								}
							} else {
								hashTotal++;
								if (completeNodeSet.hash == (currentNodeSet1.hash & completeNodeSet.hash)
										&& currentNodeSet1.bStates.size() == completeNodeSet.bStates.size()) {
									// if((currentNodeSet1.bStates.size() == completeNodeSet.bStates.size())){
									// hashtotal++;
									// if(completeNodeSet.hash!=(currentNodeSet1.hash&completeNodeSet.hash)){
									// hashsec ++;
									// }
									if (currentNodeSet1.bStates.containsAll(completeNodeSet.bStates)) {
										hashSec++;
										containsAllbnState = true;
										totalCoveredNodes++;
										currentNodeSet1.coveredBy = completeNodeSet;
										currentNodeSet1.identicalCover = true;
										completeNodeSet.covering.add(currentNodeSet1);
										if (currentNodeSet1.parentNode != null) {
											currentNodeSet1.parentNode.outgoingTransition
													.add(new Transition(
															currentNodeSet1.word
																	.getSymbol(currentNodeSet1.word.getLength() - 2),
															completeNodeSet));
										}
										coveredNodes.add(currentNodeSet1);
										// toBeDeleteed.add(currentNodeSet1);
										break;
									} else {
										hashFail++;
									}
								}
							}
						}
					}
					if (acc && !containsAllbnState) {
						for (final NodeData completeNodeSet : ACCNodes) {
							hashTotal++;
							if (completeNodeSet.aState == currentNodeSet1.aState
									&& completeNodeSet.hash == (currentNodeSet1.hash & completeNodeSet.hash)
									&& currentNodeSet1.bStates.size() == completeNodeSet.bStates.size()) {
								// if(completeNodeSet.aState== currentNodeSet1.aState&&(currentNodeSet1.bStates.size()
								// == completeNodeSet.bStates.size())){
								// hashtotal++;
								// if(completeNodeSet.hash!=(currentNodeSet1.hash&completeNodeSet.hash)){
								// hashsec ++;
								// }
								if (currentNodeSet1.bStates.containsAll(completeNodeSet.bStates)) {
									hashSec++;
									containsAllbnState = true;
									currentNodeSet1.coveredBy = completeNodeSet;
									currentNodeSet1.identicalCover = true;
									completeNodeSet.covering.add(currentNodeSet1);
									if (currentNodeSet1.parentNode != null) {
										currentNodeSet1.parentNode.outgoingTransition.add(new Transition(
												currentNodeSet1.word.getSymbol(currentNodeSet1.word.getLength() - 2),
												completeNodeSet));
									}
									coveredNodes.add(currentNodeSet1);
									totalCoveredNodes++;
									// toBeDeleteed.add(currentNodeSet1);
									break;
								} else {
									hashFail++;
								}
							}
						}
					}
					if (acc && !containsAllbnState) {
						for (final NodeData currentNodeSet2 : currentNodes.get(key)) {
							// if(currentNodeSet1!=currentNodeSet2&&(currentNodeSet2.coveredBy ==
							// null)&&(currentNodeSet1.aState ==
							// currentNodeSet2.aState)&&(currentNodeSet2.hash==(currentNodeSet1.hash&currentNodeSet2.hash)&&(currentNodeSet1.bStates.size()
							// > currentNodeSet2.bStates.size()))){
							hashTotal++;
							if (currentNodeSet1 != currentNodeSet2 && currentNodeSet2.coveredBy == null
									&& currentNodeSet2.hash == (currentNodeSet1.hash & currentNodeSet2.hash)
									&& currentNodeSet1.bStates.size() > currentNodeSet2.bStates.size()) {
								if (potenialACCCandidate == null
										|| potenialACCCandidate.bStates.size() > currentNodeSet2.bStates.size()) {
									if (currentNodeSet1.bStates.containsAll(currentNodeSet2.bStates)) {
										hashSec++;
										potenialACCCandidate = currentNodeSet2;
									} else {
										hashFail++;
									}
								}
							}
						}
					}
					if (!containsAllbnState) {
						if (potenialACCCandidate == null || acc == false) {
							newNodeInCompleteTree = true;
							if (!completedNodes.containsKey(currentNodeSet1.aState)) {
								completedNodes.put(currentNodeSet1.aState, new LinkedList<NodeData>());
							}
							completedNodes.get(currentNodeSet1.aState).addFirst(currentNodeSet1);
							totalUniqueNodes++;
							if (currentNodeSet1.parentNode != null) {
								currentNodeSet1.parentNode.outgoingTransition.add(new Transition(
										currentNodeSet1.word.getSymbol(currentNodeSet1.word.getLength() - 2),
										currentNodeSet1));
							}
						} else {
							totalAACNodes++;
							currentNodeSet1.coveredBy = potenialACCCandidate;
							currentNodeSet1.identicalCover = false;
							potenialACCCandidate.covering.add(currentNodeSet1);
							if (currentNodeSet1.parentNode != null) {
								currentNodeSet1.parentNode.outgoingTransition.add(new Transition(
										currentNodeSet1.word.getSymbol(currentNodeSet1.word.getLength() - 2),
										currentNodeSet1));
							}
							ACCNodes.add(currentNodeSet1);
							// toBeDeleteed.add(currentNodeSet1);
						}
					}
				}
			}
			// currentTree.removeAll(toBeDeleteed);
			return !newNodeInCompleteTree;
		}

		public void finishACCover() throws AutomataOperationCanceledException {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}
			assert !ACCNodes.isEmpty();
			currentNodes.clear();
			for (final NodeData node : ACCNodes) {
				node.coveredBy.covering.remove(node);
				node.coveredBy = null;
				completedNodes.get(node.aState).add(node);
				if (!currentNodes.containsKey(node.aState)) {
					currentNodes.put(node.aState, new LinkedList<NodeData>());
				}
				currentNodes.get(node.aState).add(node);
			}
			ACCNodes.clear();
			totalUniqueNodes += totalAACNodes;
			totalAACNodes = 0;
			do {
				if (prvPAutomata == null) {
					currentNodes = expand(true, false);
					if (cover(false)) {
						break;
					}
				} else {
					currentNodes = expand(false, false);
					// calculateAcceptingStates();
					if (cover(false)) {
						break;
					}
				}
			} while (true);
		}

		// private HashSet<NodeData> toBeKeepedNodes;

		public void deadendRemove() {
			// toBeKeepedNodes = new HashSet<NodeData>();
			// HashSet<NodeData> toBeDeletedNodes = new HashSet<NodeData>(allNodes);
			int i = 0;
			for (final NodeData node : completedNodes.keySet()) {
				i += completedNodes.get(node).size();
			}
			mLogger.info("Nodes before: " + (i + ACCNodes.size()));
			for (final NodeData nodes : allNodes) {
				nodes.keep = false;
			}
			for (final NodeData errorNode : errorNodes) {
				deadEndRemoveWalker(errorNode);
			}
			i = 0;
			for (final NodeData node : completedNodes.keySet()) {
				for (final NodeData node2 : completedNodes.get(node)) {
					if (node2.keep == true) {
						i++;
					}
				}
			}
			for (final NodeData node2 : ACCNodes) {
				if (node2.keep == true) {
					i++;
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

		private void deadEndRemoveWalker(final NodeData node) {
			assert node != null;
			if (!node.keep) {
				node.keep = true;
				// toBeKeepedNodes.add(node);
				for (final NodeData coveringNode : node.covering) {
					deadEndRemoveWalker(coveringNode);
				}
				if (node.parentNode != null) {
					deadEndRemoveWalker(node.parentNode);
				}
			}
		}

		public Set<LETTER> getAlphabet() {
			return letter;
		}

		public Set<NodeData> getInitialStates() {
			return initialNodes;
		}

		public LinkedList<Transition> internalSuccessors(final NodeData node) {
			return node.outgoingTransition;
		}

		public LinkedList<Transition> internalSuccessors(final NodeData node, final LETTER let) {
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
		public boolean keep;
		public int hash;
		public NodeData coveredBy = null;
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
			identicalCover = false;
			DeadEndsRemoved = false;
			bStates = new HashSet<>();
			word = null;
			covering = new HashSet<>();
			outgoingTransition = new LinkedList<>();
			hash = 0;
			accepting = false;
		}
	}

	public IncrementalInclusionCheck2DeadEndRemovalAdvanceCover(final AutomataLibraryServices services,
			final IDeterminizeStateFactory<STATE> sf, final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> a,
			final List<INwaOutgoingLetterAndTransitionProvider<LETTER, STATE>> b, final boolean acc)
			throws AutomataLibraryException {
		super(services, a);
		IncrementalInclusionCheck2DeadEndRemovalAdvanceCover.abortIfContainsCallOrReturn(a);
		macc = acc;
		localServiceProvider = services;
		mLogger.info(startMessage());
		local_mA = a;
		local_mB = new ArrayList<>();
		local_mB2 = new ArrayList<>();
		workingAutomata = new PseudoAutomata(local_mA);
		for (final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> bn : b) {
			try {
				super.addSubtrahend(bn);
				if (!getResult()) {
					workingAutomata = new PseudoAutomata(workingAutomata, bn);
				}
			} catch (final AutomataLibraryException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			local_mB.add(bn);
			local_mB2.add(bn);

		}
		mLogger.info(exitMessage());
	}

	public IncrementalInclusionCheck2DeadEndRemovalAdvanceCover(final AutomataLibraryServices services,
			final IDeterminizeStateFactory<STATE> sf, final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> a,
			final List<INwaOutgoingLetterAndTransitionProvider<LETTER, STATE>> b) throws AutomataLibraryException {
		super(services, a);
		IncrementalInclusionCheck2DeadEndRemovalAdvanceCover.abortIfContainsCallOrReturn(a);
		macc = true;
		localServiceProvider = services;
		mLogger.info(startMessage());
		local_mA = a;
		local_mB = new ArrayList<>();
		local_mB2 = new ArrayList<>();
		workingAutomata = new PseudoAutomata(local_mA);
		for (final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> bn : b) {
			try {
				super.addSubtrahend(bn);
				if (!getResult()) {
					workingAutomata = new PseudoAutomata(workingAutomata, bn);
				}
			} catch (final AutomataLibraryException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			local_mB.add(bn);
			local_mB2.add(bn);

		}
		mLogger.info(exitMessage());
	}

	@Override
	public void addSubtrahend(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> nwa) throws AutomataLibraryException {
		mLogger.info(startMessage());
		super.addSubtrahend(nwa);
		local_mB.add(nwa);
		local_mB2.add(nwa);
		if (!getResult()) {
			workingAutomata = new PseudoAutomata(workingAutomata, nwa);
		}
		mLogger.info(exitMessage());
	}

	@Override
	public NestedRun<LETTER, STATE> getCounterexample() {
		if (workingAutomata.errorNodes.peekFirst() != null) {
			return workingAutomata.errorNodes.peekFirst().word;
		} else {
			return null;
		}

	}

	@Override
	public String startMessage() {
		return "Start " + getOperationName();
	}

	@Override
	public String exitMessage() {
		if (!getResult()) {
			mLogger.info("counterExample: " + getCounterexample().getWord().toString());
		}
		mLogger.info("Total: " + totalNodes + " node(s)");
		mLogger.info("Total ACC: " + totalAACNodes + " node(s)");
		mLogger.info("Total IC: " + totalCoveredNodes + " node(s)");
		mLogger.info("Total Unique: " + totalUniqueNodes + " node(s)");
		mLogger.info("Total Hash: " + hashTotal + " node(s)");
		mLogger.info("Sec Hash: " + hashSec + " node(s)");
		mLogger.info("Fail Hash: " + hashFail + " node(s)");
		return "Exit " + getOperationName();
	}

	@Override
	public Boolean getResult() {
		return getCounterexample() == null;
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
