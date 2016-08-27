/*
 * Copyright (C) 2014-2015 Jeffery Hsu (a71128@gmail.com)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.incrementalinclusion.AbstractIncrementalInclusionCheck;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.incrementalinclusion.InclusionViaDifference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * 
 * This is an implementation of incremental inclusion check based on the Bn baseline Algorithm.<br/>
 * We use InclusionViaDIfference to check its correctness.
 * 
 * @author jefferyyjhsu@iis.sinica.edu.tw
 *
 * @param <LETTER>
 * @param <STATE>
 */

public class IncrementalInclusionCheck2<LETTER,STATE> extends AbstractIncrementalInclusionCheck<LETTER,STATE> implements IOperation<LETTER, STATE>  {
	public int counter_run = 0, counter_total_nodes = 0 ;
	private final INestedWordAutomatonSimple<LETTER, STATE> local_mA;
	private final List<INestedWordAutomatonSimple<LETTER, STATE>> local_mB;
	private final List<INestedWordAutomatonSimple<LETTER,STATE>> local_mB2;
	private final IStateFactory<STATE> localStateFactory;
	private final AutomataLibraryServices localServiceProvider;
	public HashMap<STATE,HashSet<NodeData<LETTER,STATE>>> completeTree,currentTree,coveredNodes;
	NestedRun<LETTER,STATE> result;
	class NodeData<A,B>{
		public int hash;
		public boolean covered = false;
		public HashMap<INestedWordAutomatonSimple<A,B>,HashSet<B>> bStates;
		public NestedRun<A,B> word;
		public NodeData(){
			bStates = new HashMap<INestedWordAutomatonSimple<A,B>,HashSet<B>>();
			word = null;
		}
		public NodeData(HashMap<INestedWordAutomatonSimple<A,B>,HashSet<B>> data){
			bStates = data;
			word = null;
		}
		public NodeData(NestedRun<A,B> data){
			bStates = new HashMap<INestedWordAutomatonSimple<A,B>,HashSet<B>>();
			word = data;
		}
		public NodeData(HashMap<INestedWordAutomatonSimple<A,B>,HashSet<B>> data1,NestedRun<A,B> data2){
			bStates = data1;
			word = data2;
		}
	}
	@Override
	public void addSubtrahend(INestedWordAutomatonSimple<LETTER, STATE> nwa) throws AutomataLibraryException {
		mLogger.info(startMessage());
		super.addSubtrahend(nwa);
		local_mB.add(nwa);
		local_mB2.add(nwa);
		HashMap<STATE,HashSet<NodeData<LETTER,STATE>>> bufferedTree = null;
		HashMap<STATE,HashSet<NodeData<LETTER,STATE>>> bufferedTree2 = null;
		/*counter_total_nodes = 0;
		if(result!=null){
			run();
		}*/
		if(result!=null){
			addBStates(nwa);
			do{
				counter_run++;
				if(exceptionRun()||cover()){
					break;
				}
				if (!mServices.getProgressMonitorService().continueProcessing()) {
	                throw new AutomataOperationCanceledException(this.getClass());
				}
				bufferedTree = null;
				for(final LETTER alphabet:local_mA.getAlphabet()){
					if(bufferedTree ==null){
						bufferedTree = expand(alphabet);
					}
					else{
						bufferedTree2 = expand(alphabet);
						for(final STATE state:bufferedTree2.keySet()){
							if(bufferedTree.containsKey(state)){
								bufferedTree.get(state).addAll(bufferedTree2.get(state));
							}
							else{
								bufferedTree.put(state, new HashSet<NodeData<LETTER,STATE>>());
								bufferedTree.get(state).addAll(bufferedTree2.get(state));
							}
						}
					}
			}
			currentTree = bufferedTree;
			}while(true);
		}
		mLogger.info(exitMessage());
	}
	public IncrementalInclusionCheck2(AutomataLibraryServices services, IStateFactory<STATE> sf,
			INestedWordAutomatonSimple<LETTER, STATE> a, List<INestedWordAutomatonSimple<LETTER,STATE>> b) throws AutomataLibraryException{
		super(services,a);
		IncrementalInclusionCheck2.abortIfContainsCallOrReturn(a);
		localServiceProvider = services;
		localStateFactory = sf;
		mLogger.info(startMessage());
		local_mA =  a;
		local_mB = new ArrayList<INestedWordAutomatonSimple<LETTER, STATE>>();
		local_mB2 = new ArrayList<INestedWordAutomatonSimple<LETTER, STATE>>(b);
		for(final INestedWordAutomatonSimple<LETTER,STATE> bn : b){
				try {
					super.addSubtrahend(bn);
				} catch (final AutomataLibraryException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			local_mB.add(bn);
		}
		run();
		mLogger.info(exitMessage());
	}
	
	@SuppressWarnings("unchecked")
	public void run() throws AutomataLibraryException{
		/*try {
			local_mA = (new Determinize<LETTER,STATE> (localServiceProvider,localStateFactory,local_mA)).getResult();
		} catch (OperationCanceledException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}*/
		HashMap<STATE,HashSet<NodeData<LETTER,STATE>>> bufferedTree = null;
		HashMap<STATE,HashSet<NodeData<LETTER,STATE>>> bufferedTree2 = null;
		coveredNodes = new HashMap<STATE,HashSet<NodeData<LETTER,STATE>>>();
		result = null;
		completeTree = null;
		currentTree = null;
		for(final INestedWordAutomatonSimple<LETTER,STATE> B:local_mB){
			if(!local_mA.getAlphabet().containsAll(B.getAlphabet())){
				mLogger.info("Alphabet inconsistent");
				return;
			}
		}
		do{
			counter_run++;
			if(currentTree==null){
				currentTree = expand(null);
				if(exceptionRun()||cover()){
				break;
				}
			}
			else{
				if (!mServices.getProgressMonitorService().continueProcessing()) {
		                throw new AutomataOperationCanceledException(this.getClass());
		        }
				bufferedTree = null;
				for(final LETTER alphabet:local_mA.getAlphabet()){
					if(bufferedTree ==null){
						bufferedTree = expand(alphabet);
					}
					else{
						bufferedTree2 = expand(alphabet);
						for(final STATE state:bufferedTree2.keySet()){
							if(bufferedTree.containsKey(state)){
								bufferedTree.get(state).addAll(bufferedTree2.get(state));
							}
							else{
								bufferedTree.put(state, new HashSet<NodeData<LETTER,STATE>>());
								bufferedTree.get(state).addAll(bufferedTree2.get(state));
							}
						}
					}
				}
				currentTree = bufferedTree;
				if(exceptionRun()||cover()){
				break;
				}
			}
		}while(true);
			
		/*Set<STATE> newBState;
		boolean getConflict = false;
		boolean nextRun;
		for(INestedWordAutomaton<LETTER,STATE> B:local_mB){
			if(!local_mA.getAlphabet().containsAll(B.getAlphabet())){
				mLogger.info("Alphabet inconsistent");
				return;
			}
		}
		currentTree = new HashMap<STATE,NodeData<LETTER,STATE>>();
		for(STATE state:local_mA.getInitialStates()){
			currentTree.put(state, new NodeData<LETTER,STATE>(new HashMap<INestedWordAutomaton<LETTER,STATE>,HashSet<STATE>>(), new NestedRun<LETTER,STATE>(state)));
		}
		for(INestedWordAutomaton<LETTER,STATE> automata:local_mB){
			for(STATE state:automata.getInitialStates()){
				for(STATE key:currentTree.keySet()){
					if(!currentTree.get(key).bStates.containsKey(automata)){
						currentTree.get(key).bStates.put(automata,new HashSet<STATE>());
					}
					currentTree.get(key).bStates.get(automata).add(state);
				}
			}
		}
		for(STATE state:local_mA.getFinalStates()){
			if(currentTree.keySet().contains(state)){
				getConflict = true;
				for(INestedWordAutomaton<LETTER, STATE> automata:currentTree.get(state).bStates.keySet()){
					for(STATE B_finalState:automata.getFinalStates()){	
						if(currentTree.get(state).bStates.get(automata).contains(B_finalState)){
							getConflict = false;
						}
					}
				}
				if(getConflict == true){
					result = currentTree.get(state).word;
					return;
				}
			}
		}
		completeTree = new HashMap<STATE,HashSet<NodeData<LETTER,STATE>>>();
		for(STATE state:currentTree.keySet()){
			if(!completeTree.keySet().contains(state)){
				completeTree.put(state, new HashSet<NodeData<LETTER,STATE>>());
			}
			completeTree.get(state).add(currentTree.get(state));
		}
		nextTree = new HashMap<STATE,NodeData<LETTER,STATE>>();
		for(STATE state : currentTree.keySet()){
			for(LETTER alphabet:local_mA.getAlphabet()){
				for(OutgoingInternalTransition<LETTER, STATE> successingState:local_mA.internalSuccessors(state, alphabet)){
					nextTree.put(successingState.getSucc(), new NodeData<LETTER, STATE>(new NestedRun<LETTER, STATE>(state,alphabet,0,successingState.getSucc())));
					for(INestedWordAutomaton<LETTER, STATE> automata: currentTree.get(state).bStates.keySet()){
						newBState = new HashSet<STATE>();
						for(STATE orginalBState:currentTree.get(state).bStates.get(automata)){
							for(OutgoingInternalTransition<LETTER, STATE> successingBState:local_mB.get(local_mB.indexOf(orginalBState)).internalSuccessors(orginalBState, alphabet)){
								newBState.add(successingBState.getSucc());
							}
						}
						nextTree.get(successingState.getSucc()).bStates.put(automata,(HashSet<STATE>) newBState);
					}
				}
			}
		}
		currentTree = nextTree;*/
		
	}
	@SuppressWarnings("unchecked")
	private HashMap<STATE,HashSet<NodeData<LETTER,STATE>>> expand(LETTER alp){
		final HashMap<STATE,HashSet<NodeData<LETTER,STATE>>> nextNodes = new HashMap<STATE,HashSet<NodeData<LETTER,STATE>>>();
		HashMap<INestedWordAutomatonSimple<LETTER,STATE>,HashSet<STATE>> bStates = null;;
		NodeData<LETTER,STATE> tempBNodeData = null;
		int tempHash;
		if(alp==null){
			tempHash = 0;
			bStates = new HashMap<INestedWordAutomatonSimple<LETTER,STATE>,HashSet<STATE>>();
			for(final INestedWordAutomatonSimple<LETTER,STATE> automata:local_mB){
				bStates.put(automata, new HashSet<STATE>());
				for(final STATE Bstate:automata.getInitialStates()){
					bStates.get(automata).add(Bstate);
					tempHash = tempHash | Bstate.hashCode();
				}
			}
			for(final STATE state:local_mA.getInitialStates()){
				nextNodes.put(state, new HashSet<NodeData<LETTER,STATE>>());
				tempBNodeData = new NodeData<LETTER,STATE>(new NestedRun<LETTER,STATE>(state));
				tempBNodeData.hash = tempHash;
				tempBNodeData.bStates = (HashMap<INestedWordAutomatonSimple<LETTER, STATE>, HashSet<STATE>>) bStates.clone();
				counter_total_nodes++;
				nextNodes.get(state).add(tempBNodeData);
			}
		}
		else{
			for(final STATE state:currentTree.keySet()){
				for(final NodeData<LETTER,STATE> currentNodeSet:currentTree.get(state)){
					tempHash = 0;
					bStates = new HashMap<INestedWordAutomatonSimple<LETTER,STATE>,HashSet<STATE>>();
					for(final INestedWordAutomatonSimple<LETTER,STATE> automata:currentNodeSet.bStates.keySet()){
						bStates.put(automata, new HashSet<STATE>());
						for(final STATE Bstate:currentNodeSet.bStates.get(automata)){
							for(final OutgoingInternalTransition<LETTER, STATE> BTransition:automata.internalSuccessors(Bstate, alp)){
								bStates.get(automata).add(BTransition.getSucc());
								tempHash = tempHash | BTransition.getSucc().hashCode();
							}
						}
					}
					for(final OutgoingInternalTransition<LETTER, STATE> ATransition:local_mA.internalSuccessors(state,alp)){
						@SuppressWarnings("unchecked")
						final
						ArrayList<STATE> newStateSequence = (ArrayList<STATE>) currentNodeSet.word.getStateSequence().clone();
						newStateSequence.add(ATransition.getSucc());
						tempBNodeData = new NodeData<LETTER,STATE>(new NestedRun<LETTER,STATE>(currentNodeSet.word.getWord().concatenate(new NestedWord<LETTER>(ATransition.getLetter(),-2)),newStateSequence));
						tempBNodeData.hash = tempHash;
						tempBNodeData.bStates = new HashMap<INestedWordAutomatonSimple<LETTER, STATE>, HashSet<STATE>>();
						for(final INestedWordAutomatonSimple<LETTER, STATE> automata: bStates.keySet()){
							tempBNodeData.bStates.put(automata, (HashSet<STATE>) bStates.get(automata).clone());
						}
						counter_total_nodes++;
						if(!nextNodes.containsKey(ATransition.getSucc())){
							nextNodes.put(ATransition.getSucc(), new HashSet<NodeData<LETTER,STATE>>());
						}
						nextNodes.get(ATransition.getSucc()).add(tempBNodeData);	
					}
				}
			}
		}
		return nextNodes;
	}
	private boolean cover(){
		boolean newNodeInCompleteTree = false;
		boolean containsAllbnState = false;
		final HashMap<STATE,HashSet<NodeData<LETTER,STATE>>> toBeDeleteed = new HashMap<STATE,HashSet<NodeData<LETTER,STATE>>>();
		for(final STATE currentAState : currentTree.keySet()){
			for(final NodeData<LETTER,STATE> currentNodeSet1:currentTree.get(currentAState)){
//				if(!currentNodeSet1.covered){
					containsAllbnState = false;
/*					for(NodeData<LETTER,STATE> currentNodeSet2:currentTree.get(currentAState)){
						if(currentNodeSet1!=currentNodeSet2&&!(currentNodeSet2.covered)&&(currentNodeSet2.hash==(currentNodeSet1.hash&currentNodeSet2.hash))){
						//if(currentNodeSet1!=currentNodeSet2&&!(currentNodeSet2.covered)){	
							containsAllbnState = true;
							for(INestedWordAutomatonSimple<LETTER,STATE> bn:currentNodeSet2.bStates.keySet()){
								if(!currentNodeSet1.bStates.get(bn).containsAll(currentNodeSet2.bStates.get(bn))){
									containsAllbnState=false;
								}
							}
							if(containsAllbnState){
								break;
							}
						}
					}
					if(containsAllbnState){
						currentNodeSet1.covered = true;
						if(!coveredNodes.containsKey(currentAState)){
							coveredNodes.put(currentAState, new HashSet<NodeData<LETTER,STATE>>());
						}
						if(!toBeDeleteed.containsKey(currentAState)){
							toBeDeleteed.put(currentAState, new HashSet<NodeData<LETTER,STATE>>());
						}
						coveredNodes.get(currentAState).add(currentNodeSet1);
						toBeDeleteed.get(currentAState).add(currentNodeSet1);
					}else{*/
						if(completeTree!=null){
							if(completeTree.keySet().contains(currentAState)){
								for(final NodeData<LETTER,STATE> completeNodeSet:completeTree.get(currentAState)){
									if(completeNodeSet.hash==(currentNodeSet1.hash&completeNodeSet.hash)){
									//if(true){
										containsAllbnState = true;
										for(final INestedWordAutomatonSimple<LETTER,STATE> bn:currentNodeSet1.bStates.keySet()){
											if(!currentNodeSet1.bStates.get(bn).containsAll(completeNodeSet.bStates.get(bn))){
												containsAllbnState=false;
											}
										}
										if(containsAllbnState){
											break;
										}
									}																	
								}
							}
							else{
								containsAllbnState=false;
								completeTree.put(currentAState, new HashSet<NodeData<LETTER,STATE>>());
							}
						}
						else{
							completeTree = new HashMap<STATE,HashSet<NodeData<LETTER,STATE>>>();
							containsAllbnState=false;
							completeTree.put(currentAState, new HashSet<NodeData<LETTER,STATE>>());
						}
						if(!containsAllbnState){
							newNodeInCompleteTree = true;
							completeTree.get(currentAState).add(currentNodeSet1);
						}
						else{
							currentNodeSet1.covered = true;
							if(!coveredNodes.containsKey(currentAState)){
								coveredNodes.put(currentAState, new HashSet<NodeData<LETTER,STATE>>());
							}
							if(!toBeDeleteed.containsKey(currentAState)){
								toBeDeleteed.put(currentAState, new HashSet<NodeData<LETTER,STATE>>());
							}
							coveredNodes.get(currentAState).add(currentNodeSet1);
							toBeDeleteed.get(currentAState).add(currentNodeSet1);
						}
					}
//				}
//			}
		}
		for(final STATE currentAState : toBeDeleteed.keySet()){
			for(final NodeData<LETTER,STATE> currentNodeSet1:toBeDeleteed.get(currentAState)){
				currentTree.get(currentAState).remove(currentNodeSet1);
			}
		}
/*		for(STATE currentAState : currentTree.keySet()){
			for(NodeData<LETTER,STATE> currentNodeSet:currentTree.get(currentAState)){
				if(!currentNodeSet.covered){
					if(completeTree!=null){
						if(completeTree.keySet().contains(currentAState)){
							for(NodeData<LETTER,STATE> completeNodeSet:completeTree.get(currentAState)){
								containsAllbnState = true;
								for(INestedWordAutomatonSimple<LETTER,STATE> bn:currentNodeSet.bStates.keySet()){
									if(!currentNodeSet.bStates.get(bn).containsAll(completeNodeSet.bStates.get(bn))){
										containsAllbnState=false;
									}
								}
								if(containsAllbnState){
									break;
								}
							}
						}
						else{
							containsAllbnState=false;
							completeTree.put(currentAState, new HashSet<NodeData<LETTER,STATE>>());
						}
					}
					else{
						completeTree = new HashMap<STATE,HashSet<NodeData<LETTER,STATE>>>();
						containsAllbnState=false;
						completeTree.put(currentAState, new HashSet<NodeData<LETTER,STATE>>());
					}
					if(!containsAllbnState){
						newNodeInCompleteTree = true;
						completeTree.get(currentAState).add(currentNodeSet);
					}
					else{
						currentNodeSet.covered = true;
					}
				}
				}
		}*/
		return !newNodeInCompleteTree;
	}
	private boolean exceptionRun(){
		result = null;
		boolean foundFinal = false;
		for(final STATE currentAstate : currentTree.keySet()){
			if(local_mA.isFinal(currentAstate)){
				for(final NodeData<LETTER,STATE> currentNodeSet:currentTree.get(currentAstate)){
					foundFinal = false;
					for(final INestedWordAutomatonSimple<LETTER,STATE> bn:currentNodeSet.bStates.keySet()){
						for(final STATE bnState:currentNodeSet.bStates.get(bn)){
							if(bn.isFinal(bnState)){
								foundFinal = true;
								break;
							}
						}
						if(foundFinal){
							break;
						}
					}
					if(!foundFinal){
						result = currentNodeSet.word;
						break;
					}
				}
			}
			if (result!=null){
				break;
			}
		}
		return result!=null;
	}
	
/*	private boolean breakCheck(){
		result = null;
		boolean foundFinal = false;
		boolean newNodeInCompleteTree = false;
		boolean containsAllbnState = false;
		HashMap<STATE,HashSet<NodeData<LETTER,STATE>>> toBeDeleteed = new HashMap<STATE,HashSet<NodeData<LETTER,STATE>>>();
		for(STATE currentAState : currentTree.keySet()){
			for(NodeData<LETTER,STATE> currentNodeSet1:currentTree.get(currentAState)){
				if(local_mA.isFinal(currentAState)){
					foundFinal = false;
					for(INestedWordAutomatonSimple<LETTER,STATE> bn:currentNodeSet1.bStates.keySet()){
						for(STATE bnState:currentNodeSet1.bStates.get(bn)){
							if(bn.isFinal(bnState)){
								foundFinal = true;
								break;
							}
						}
						if(foundFinal){
							break;
						}
					}
					if(!foundFinal){
						result = currentNodeSet1.word;
						return true;
					}
				}
				if(!currentNodeSet1.covered){
					containsAllbnState = false;
					for(NodeData<LETTER,STATE> currentNodeSet2:currentTree.get(currentAState)){
						if(currentNodeSet1!=currentNodeSet2&&!(currentNodeSet2.covered)){
							containsAllbnState = true;
							for(INestedWordAutomatonSimple<LETTER,STATE> bn:currentNodeSet2.bStates.keySet()){
								if(!currentNodeSet1.bStates.get(bn).containsAll(currentNodeSet2.bStates.get(bn))){
									containsAllbnState=false;
								}
							}
							if(containsAllbnState){
								break;
							}
						}
					}
					if(containsAllbnState){
						currentNodeSet1.covered = true;
						if(!coveredNodes.containsKey(currentAState)){
							coveredNodes.put(currentAState, new HashSet<NodeData<LETTER,STATE>>());
						}
						if(!toBeDeleteed.containsKey(currentAState)){
							toBeDeleteed.put(currentAState, new HashSet<NodeData<LETTER,STATE>>());
						}
						coveredNodes.get(currentAState).add(currentNodeSet1);
						toBeDeleteed.get(currentAState).add(currentNodeSet1);
					}else{
						if(completeTree!=null){
							if(completeTree.keySet().contains(currentAState)){
								for(NodeData<LETTER,STATE> completeNodeSet:completeTree.get(currentAState)){
									containsAllbnState = true;
									for(INestedWordAutomatonSimple<LETTER,STATE> bn:currentNodeSet1.bStates.keySet()){
										if(!currentNodeSet1.bStates.get(bn).containsAll(completeNodeSet.bStates.get(bn))){
											containsAllbnState=false;
										}
									}
									if(containsAllbnState){
										break;
									}
								}
							}
							else{
								containsAllbnState=false;
								completeTree.put(currentAState, new HashSet<NodeData<LETTER,STATE>>());
							}
						}
						else{
							completeTree = new HashMap<STATE,HashSet<NodeData<LETTER,STATE>>>();
							containsAllbnState=false;
							completeTree.put(currentAState, new HashSet<NodeData<LETTER,STATE>>());
						}
						if(!containsAllbnState){
							newNodeInCompleteTree = true;
							completeTree.get(currentAState).add(currentNodeSet1);
						}
						else{
							currentNodeSet1.covered = true;
							if(!coveredNodes.containsKey(currentAState)){
								coveredNodes.put(currentAState, new HashSet<NodeData<LETTER,STATE>>());
							}
							if(!toBeDeleteed.containsKey(currentAState)){
								toBeDeleteed.put(currentAState, new HashSet<NodeData<LETTER,STATE>>());
							}
							coveredNodes.get(currentAState).add(currentNodeSet1);
							toBeDeleteed.get(currentAState).add(currentNodeSet1);
						}
					}
				}
			}
		}
		for(STATE currentAState : toBeDeleteed.keySet()){
			for(NodeData<LETTER,STATE> currentNodeSet1:toBeDeleteed.get(currentAState)){
				currentTree.get(currentAState).remove(currentNodeSet1);
			}
		}
		return !newNodeInCompleteTree;
		
	}*/
	
	@Override
	public NestedRun<LETTER,STATE> getCounterexample(){
		return result;
	}
	@Override
	public String operationName() {
		return "IncrementalInclusionCheck2";
	}
	@Override
	public String startMessage() {
		return "Start " + operationName();
	}
	
	@Override
	public String exitMessage() {
		mLogger.info("total:"+counter_total_nodes+"nodes");
		mLogger.info(counter_total_nodes+"nodes in the end");
		mLogger.info("total:"+counter_run+"runs");
		return "Exit " + operationName();
	}
	@Override
	public Boolean getResult(){
		return result == null;
	}
	@Override
	public boolean checkResult(IStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		final boolean checkResult = compareInclusionCheckResult(localServiceProvider, 
				localStateFactory, local_mA, local_mB2, result);
		return checkResult;
//		if(((result==null)&&(new IncrementalInclusionCheck2<LETTER, STATE>(localServiceProvider,localStateFactory,local_mA,local_mB2).getResult()==null))||((result!=null)&&(new IncrementalInclusionCheck2<LETTER, STATE>(localServiceProvider,localStateFactory,local_mA,local_mB2).getResult()!=null))){
//			return true;
//		}
//		else{
//			return false;
//		}
	}
	
	/**
	 * Compare the result of an inclusion check with an inclusion check based
	 * on a emptiness/difference operations.
	 * The NestedRun ctrEx is the result of an inclusion check whose inputs
	 * are an automaton <b>a</b> and and a list of automata b.
	 * If the language of <b>a</b> is included in the union of all languages of the
	 * automata b then ctrEx is null, otherwise ctrEx is a run of <b>a</b> that
	 * is a counterexample to the inclusion.
	 * This method returns true if the difference-based inclusion check comes
	 * up with the same result, i.e., if it find a counterexample if ctrEx is
	 * non-null and if it does not find a counterexample if ctrEX is null.
	 * Note that if inclusion does not hold, there may be several 
	 * counterexamples. Dies method does NOT require that both methods return
	 * exactly the same counterexample. 
	 */
	public static <LETTER, STATE> boolean compareInclusionCheckResult(
			AutomataLibraryServices services, 
			IStateFactory<STATE> stateFactory, 
			INestedWordAutomatonSimple<LETTER, STATE> a, 
			List<INestedWordAutomatonSimple<LETTER, STATE>> b, 
			NestedRun<LETTER,STATE> ctrEx) throws AutomataLibraryException {
		final InclusionViaDifference<LETTER, STATE> ivd = 
				new InclusionViaDifference<LETTER, STATE>(services, stateFactory, a);
		// add all b automata
		for (final INestedWordAutomatonSimple<LETTER, STATE> bi : b) {
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
	private HashSet<STATE> NestedRunStates(INestedWordAutomatonSimple<LETTER,STATE> bn,NestedRun<LETTER,STATE> word){
		HashSet<STATE> curStaSet = null;
		Iterable<OutgoingInternalTransition<LETTER,STATE>>nextStaSet = null;
		HashSet<STATE> newStaSet;
		curStaSet = new HashSet<STATE>();
		curStaSet.addAll((Set<STATE>)bn.getInitialStates());
		if(word.getWord().length()!=0){
			for(final LETTER alphabet:word.getWord().asList()){
				newStaSet = new HashSet<STATE>();
				for(final STATE OState:curStaSet){
					nextStaSet = bn.internalSuccessors(OState, alphabet);
					for(final OutgoingInternalTransition<LETTER,STATE> newState:nextStaSet){
						newStaSet.add(newState.getSucc());
					}
				}
				curStaSet.clear();
				curStaSet = newStaSet;
			}
		}
		return curStaSet;
	}
	private void addBStates(INestedWordAutomatonSimple<LETTER,STATE> nwa){
		HashSet<STATE> newStates = null;
		if(completeTree!=null){
			for(final STATE aSTATE:completeTree.keySet()){
				for(final NodeData<LETTER,STATE> node:completeTree.get(aSTATE)){
					node.bStates.put(nwa, new HashSet<STATE>());
					newStates = NestedRunStates(nwa,node.word);
					node.bStates.get(nwa).addAll(newStates);
					for(final STATE s:newStates){
						node.hash = node.hash | s.hashCode();
					}
				}
			}
		}
		for(final STATE aSTATE:coveredNodes.keySet()){
			for(final NodeData<LETTER,STATE> node:coveredNodes.get(aSTATE)){
				if(!currentTree.containsKey(aSTATE)){
					currentTree.put(aSTATE,new HashSet<NodeData<LETTER,STATE>>());
				}
				currentTree.get(aSTATE).add(node);
			}
			coveredNodes.get(aSTATE).clear();
		}
		
		for(final STATE aSTATE:currentTree.keySet()){
			for(final NodeData<LETTER,STATE> node:currentTree.get(aSTATE)){
				node.covered = false;
				node.bStates.put(nwa, new HashSet<STATE>());
				newStates = NestedRunStates(nwa,node.word);
				node.bStates.get(nwa).addAll(newStates);
				for(final STATE s:newStates){
					node.hash = node.hash | s.hashCode();
				}
			}
		}
	}
	public static <LETTER, STATE> void abortIfContainsCallOrReturn(INestedWordAutomatonSimple<LETTER, STATE> a) {
		if (!a.getCallAlphabet().isEmpty() || !a.getReturnAlphabet().isEmpty()) {
			throw new UnsupportedOperationException("Operation does not support call or return");
		}
	}
}
