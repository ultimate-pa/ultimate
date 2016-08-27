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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

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

public class IncrementalInclusionCheck2DeadEndRemoval<LETTER,STATE> extends AbstractIncrementalInclusionCheck<LETTER,STATE> implements IOperation<LETTER, STATE>  {
	public int counter_run = 0, counter_total_nodes = 0 ;
	private final INestedWordAutomatonSimple<LETTER, STATE> local_mA;
	private final List<INestedWordAutomatonSimple<LETTER, STATE>> local_mB;
	private final List<INestedWordAutomatonSimple<LETTER,STATE>> local_mB2;
	private final IStateFactory<STATE> localStateFactory;
	private final AutomataLibraryServices localServiceProvider;
	public HashSet<NodeData<LETTER,STATE>> allNodes;
	public LinkedList<NodeData<LETTER,STATE>>errorNodes,currentTree,alreadyDeltedNodes;
	public LinkedList<NodeData<LETTER,STATE>> completeTree,coveredNodes;
	public int nodeNumberBeforeDelete = 0;
	class NodeData<A,B>{
		public boolean DeadEndsRemoved;
		public boolean keep;
		public int hash;
		public boolean covered = false;
		public NodeData<A,B> parentNode;
		public HashSet<NodeData<A,B>> covering;
		public B aState;
		public HashMap<INestedWordAutomatonSimple<A,B>,HashSet<B>> bStates;
		public NestedRun<A,B> word;
		public NodeData(){
			bStates = new HashMap<INestedWordAutomatonSimple<A,B>,HashSet<B>>();
			word = null;
			covering = new HashSet<NodeData<A,B>>();
		}
		public NodeData(HashMap<INestedWordAutomatonSimple<A,B>,HashSet<B>> data){
			bStates = data;
			word = null;
			DeadEndsRemoved = false;
			covering = new HashSet<NodeData<A,B>>();
		}
		public NodeData(NestedRun<A,B> data){
			bStates = new HashMap<INestedWordAutomatonSimple<A,B>,HashSet<B>>();
			word = data;
			DeadEndsRemoved = false;
			covering = new HashSet<NodeData<A,B>>();
		}
		public NodeData(HashMap<INestedWordAutomatonSimple<A,B>,HashSet<B>> data1,NestedRun<A,B> data2){
			bStates = data1;
			word = data2;
			DeadEndsRemoved = false;
			covering = new HashSet<NodeData<A,B>>();
		}
	}
	@Override
	public void addSubtrahend(INestedWordAutomatonSimple<LETTER, STATE> nwa) throws AutomataLibraryException {
		mLogger.info(startMessage());
		@SuppressWarnings({ "unchecked", "rawtypes" })
		final
		INestedWordAutomatonSimple<LETTER, STATE> tempB = (new RemoveDeadEnds(localServiceProvider, nwa)).getResult();
		super.addSubtrahend(tempB);
		local_mB.add(tempB);
		local_mB2.add(tempB);
		LinkedList<NodeData<LETTER,STATE>> bufferedTree = null;
		/*counter_total_nodes = 0;
		if(result!=null){
			run();
		}*/
		if(errorNodes.peekFirst()!=null){
			addBStates(tempB);
			do{
				counter_run++;
				if(cover()){
					//if(errorNodes.peekFirst() != null){
						deadEndRemove();
					//}
					break;
				}
				if (!mServices.getProgressMonitorService().continueProcessing()) {
	                throw new AutomataOperationCanceledException(this.getClass());
				}
				bufferedTree = null;
				bufferedTree = expand(false);
				currentTree = bufferedTree;
				exceptionRun();
			}while(true);
		}
		mLogger.info(exitMessage());
	}
	@SuppressWarnings({ "unchecked", "rawtypes" })
	public IncrementalInclusionCheck2DeadEndRemoval(AutomataLibraryServices services, IStateFactory<STATE> sf,
			INestedWordAutomatonSimple<LETTER, STATE> a, List<INestedWordAutomatonSimple<LETTER,STATE>> b) throws AutomataLibraryException{
		super(services,a);
		IncrementalInclusionCheck2DeadEndRemoval.abortIfContainsCallOrReturn(a);
		localServiceProvider = services;
		localStateFactory = sf;
		mLogger.info(startMessage());
		local_mA =  (new RemoveDeadEnds(localServiceProvider, a)).getResult();
		local_mB = new ArrayList<INestedWordAutomatonSimple<LETTER, STATE>>();
		local_mB2 = new ArrayList<INestedWordAutomatonSimple<LETTER, STATE>>();
		for(final INestedWordAutomatonSimple<LETTER,STATE> bn : b){
			@SuppressWarnings({ "unchecked", "rawtypes" })
			final
			INestedWordAutomatonSimple<LETTER, STATE> tempB = (new RemoveDeadEnds(localServiceProvider, bn)).getResult();
			try {
				super.addSubtrahend(tempB);
			} catch (final AutomataLibraryException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			local_mB.add(tempB);
			local_mB2.add(tempB);
		}
		run();
		mLogger.info(exitMessage());
	}
	/*
	@SuppressWarnings("unchecked")
	public void run() throws AutomataLibraryException{
		/*try {
			local_mA = (new Determinize<LETTER,STATE> (localServiceProvider,localStateFactory,local_mA)).getResult();
		} catch (OperationCanceledException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		LinkedHashMap<STATE,LinkedList<NodeData<LETTER,STATE>>> bufferedTree = null;
		LinkedHashMap<STATE,LinkedList<NodeData<LETTER,STATE>>> bufferedTree2 = null;
		coveredNodes = new LinkedHashMap<STATE,LinkedList<NodeData<LETTER,STATE>>>();
		allNodes = new HashSet<NodeData<LETTER,STATE>>();
		errorNodes = new LinkedList<NodeData<LETTER,STATE>>();
		completeTree = null;
		currentTree = null;
		for(INestedWordAutomatonSimple<LETTER,STATE> B:local_mB){
			if(!local_mA.getAlphabet().containsAll(B.getAlphabet())){
				mLogger.info("Alphabet inconsistent");
				return;
			}
		}
		do{
			counter_run++;
			if(currentTree==null){
				currentTree = expand(null);
				exceptionRun();
				if(cover()){
					if(errorNodes.peekFirst() != null){
						deadEndRemove();
					}
					break;
				}
			}
			else{
				if (!mServices.getProgressMonitorService().continueProcessing()) {
		                throw new OperationCanceledException(this.getClass());
		        }
				bufferedTree = null;
				for(LETTER alphabet:local_mA.getAlphabet()){
					if(bufferedTree ==null){
						bufferedTree = expand(alphabet);
					}
					else{
						bufferedTree2 = expand(alphabet);
						for(STATE state:bufferedTree2.keySet()){
							if(bufferedTree.containsKey(state)){
								bufferedTree.get(state).addAll(bufferedTree2.get(state));
							}
							else{
								bufferedTree.put(state, new LinkedList<NodeData<LETTER,STATE>>());
								bufferedTree.get(state).addAll(bufferedTree2.get(state));
							}
						}
					}
				}
				currentTree = bufferedTree;
				exceptionRun();
				if(cover()){
					if(errorNodes.peekFirst() != null){
						deadEndRemove();
					}
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
		currentTree = nextTree;
		
	}*/
	@SuppressWarnings("unchecked")
	public void run() throws AutomataLibraryException{
		/*try {
			local_mA = (new Determinize<LETTER,STATE> (localServiceProvider,localStateFactory,local_mA)).getResult();
		} catch (OperationCanceledException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}*/
		LinkedList<NodeData<LETTER,STATE>> bufferedTree = null;
		coveredNodes = new LinkedList<NodeData<LETTER,STATE>>();
		allNodes = new HashSet<NodeData<LETTER,STATE>>();
		alreadyDeltedNodes = new LinkedList<NodeData<LETTER,STATE>>();
		errorNodes = new LinkedList<NodeData<LETTER,STATE>>();
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
				currentTree = expand(true);
				exceptionRun();
				if(cover()){
					//if(errorNodes.peekFirst() != null){
						deadEndRemove();
					//}
					break;
				}
			}
			else{
				if (!mServices.getProgressMonitorService().continueProcessing()) {
		                throw new AutomataOperationCanceledException(this.getClass());
		        }
				bufferedTree = expand(false);
				currentTree = bufferedTree;
				exceptionRun();
				if(cover()){
					//if(errorNodes.peekFirst() != null){
						deadEndRemove();
					//}
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
	private LinkedList<NodeData<LETTER,STATE>> expand(boolean init){
		final LinkedList<NodeData<LETTER,STATE>> nextNodes = new LinkedList<NodeData<LETTER,STATE>>();
		HashMap<INestedWordAutomatonSimple<LETTER,STATE>,HashSet<STATE>> bStates = null;;
		NodeData<LETTER,STATE> tempNodeData = null;
		int tempHash;
		if(init==true){
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
				tempNodeData = new NodeData<LETTER,STATE>(new NestedRun<LETTER,STATE>(state));
				tempNodeData.parentNode = null;
				tempNodeData.hash = tempHash;
				tempNodeData.bStates = (HashMap<INestedWordAutomatonSimple<LETTER, STATE>, HashSet<STATE>>) bStates.clone();
				counter_total_nodes++;
				tempNodeData.aState = state;
				allNodes.add(tempNodeData);
				nextNodes.add(tempNodeData);
			}
		}
		else{
			for(final NodeData<LETTER,STATE> currentNodeSet:currentTree){
				for(final OutgoingInternalTransition<LETTER, STATE> ATransition:local_mA.internalSuccessors(currentNodeSet.aState)){
					boolean alreadyExisted = false;
					tempHash = 0;
					bStates = new HashMap<INestedWordAutomatonSimple<LETTER,STATE>,HashSet<STATE>>();
					for(final INestedWordAutomatonSimple<LETTER,STATE> automata:currentNodeSet.bStates.keySet()){
						bStates.put(automata, new HashSet<STATE>());
						for(final STATE Bstate:currentNodeSet.bStates.get(automata)){
							for(final OutgoingInternalTransition<LETTER, STATE> BTransition:automata.internalSuccessors(Bstate, ATransition.getLetter())){
								bStates.get(automata).add(BTransition.getSucc());
								tempHash = tempHash | BTransition.getSucc().hashCode();
							}
						}
					}
					final ArrayList<STATE> newStateSequence = (ArrayList<STATE>) currentNodeSet.word.getStateSequence().clone();
					newStateSequence.add(ATransition.getSucc());
					tempNodeData = new NodeData<LETTER,STATE>(new NestedRun<LETTER,STATE>(currentNodeSet.word.getWord().concatenate(new NestedWord<LETTER>(ATransition.getLetter(),-2)),newStateSequence));
					tempNodeData.aState = ATransition.getSucc();
					tempNodeData.parentNode = currentNodeSet;
					tempNodeData.hash = tempHash;
					tempNodeData.bStates = new HashMap<INestedWordAutomatonSimple<LETTER, STATE>, HashSet<STATE>>();
					for(final INestedWordAutomatonSimple<LETTER, STATE> automata: bStates.keySet()){
						tempNodeData.bStates.put(automata, (HashSet<STATE>) bStates.get(automata).clone());
					}
					for(final NodeData<LETTER,STATE> deletedNode : alreadyDeltedNodes){
						if(deletedNode.aState.equals(tempNodeData.aState)){
							alreadyExisted = true;
							for(final INestedWordAutomatonSimple<LETTER, STATE> automata : deletedNode.bStates.keySet()){
								if(!deletedNode.bStates.get(automata).equals(tempNodeData.bStates.get(automata))){
									alreadyExisted = false;
									break;
								}
							}
							if(alreadyExisted){
								break;
							}
						}
					}
					if(!alreadyExisted){
						counter_total_nodes++;
						allNodes.add(tempNodeData);
						nextNodes.add(tempNodeData);	
					}
				}
			}
		}
		return nextNodes;
	}
	/*@SuppressWarnings("unchecked")
	private LinkedHashMap<STATE,LinkedList<NodeData<LETTER,STATE>>> expand(LETTER alp){
		LinkedHashMap<STATE,LinkedList<NodeData<LETTER,STATE>>> nextNodes = new LinkedHashMap<STATE,LinkedList<NodeData<LETTER,STATE>>>();
		HashMap<INestedWordAutomatonSimple<LETTER,STATE>,HashSet<STATE>> bStates = null;;
		NodeData<LETTER,STATE> tempBNodeData = null;
		int tempHash;
		if(alp==null){
			tempHash = 0;
			bStates = new HashMap<INestedWordAutomatonSimple<LETTER,STATE>,HashSet<STATE>>();
			for(INestedWordAutomatonSimple<LETTER,STATE> automata:local_mB){
				bStates.put(automata, new HashSet<STATE>());
				for(STATE Bstate:automata.getInitialStates()){
					bStates.get(automata).add(Bstate);
					tempHash = tempHash | Bstate.hashCode();
				}
			}
			for(STATE state:local_mA.getInitialStates()){
				nextNodes.put(state, new LinkedList<NodeData<LETTER,STATE>>());
				tempBNodeData = new NodeData<LETTER,STATE>(new NestedRun<LETTER,STATE>(state));
				tempBNodeData.parentNode = null;
				tempBNodeData.hash = tempHash;
				tempBNodeData.bStates = (HashMap<INestedWordAutomatonSimple<LETTER, STATE>, HashSet<STATE>>) bStates.clone();
				counter_total_nodes++;
				tempBNodeData.aState = state;
				allNodes.add(tempBNodeData);
				nextNodes.get(state).add(tempBNodeData);
			}
		}
		else{
			for(STATE state:currentTree.keySet()){
				for(NodeData<LETTER,STATE> currentNodeSet:currentTree.get(state)){
					tempHash = 0;
					bStates = new HashMap<INestedWordAutomatonSimple<LETTER,STATE>,HashSet<STATE>>();
					for(INestedWordAutomatonSimple<LETTER,STATE> automata:currentNodeSet.bStates.keySet()){
						bStates.put(automata, new HashSet<STATE>());
						for(STATE Bstate:currentNodeSet.bStates.get(automata)){
							for(OutgoingInternalTransition<LETTER, STATE> BTransition:automata.internalSuccessors(Bstate, alp)){
								bStates.get(automata).add(BTransition.getSucc());
								tempHash = tempHash | BTransition.getSucc().hashCode();
							}
						}
					}
					for(OutgoingInternalTransition<LETTER, STATE> ATransition:local_mA.internalSuccessors(state,alp)){
						@SuppressWarnings("unchecked")
						ArrayList<STATE> newStateSequence = (ArrayList<STATE>) currentNodeSet.word.getStateSequence().clone();
						newStateSequence.add(ATransition.getSucc());
						tempBNodeData = new NodeData<LETTER,STATE>(new NestedRun<LETTER,STATE>(currentNodeSet.word.getWord().concatenate(new NestedWord<LETTER>(ATransition.getLetter(),-2)),newStateSequence));
						tempBNodeData.aState = ATransition.getSucc();
						tempBNodeData.parentNode = currentNodeSet;
						tempBNodeData.hash = tempHash;
						tempBNodeData.bStates = new HashMap<INestedWordAutomatonSimple<LETTER, STATE>, HashSet<STATE>>();
						for(INestedWordAutomatonSimple<LETTER, STATE> automata: bStates.keySet()){
							tempBNodeData.bStates.put(automata, (HashSet<STATE>) bStates.get(automata).clone());
						}
						counter_total_nodes++;
						if(!nextNodes.containsKey(ATransition.getSucc())){
							nextNodes.put(ATransition.getSucc(), new LinkedList<NodeData<LETTER,STATE>>());
						}
						allNodes.add(tempBNodeData);
						nextNodes.get(ATransition.getSucc()).add(tempBNodeData);	
					}
				}
			}
		}
		return nextNodes;
	}*/
	private boolean cover(){
		boolean newNodeInCompleteTree = false;
		boolean containsAllbnState = false;
		final LinkedList<NodeData<LETTER,STATE>> toBeDeleteed = new LinkedList<NodeData<LETTER,STATE>>();
		int i,j;
		//for(NodeData<LETTER,STATE> currentNodeSet1:currentTree){
		for(i=0;i<currentTree.size();i++){	
			final NodeData<LETTER,STATE> currentNodeSet1 = currentTree.get(i);
			containsAllbnState = false;
			if(completeTree!=null){
				for(final NodeData<LETTER,STATE> completeNodeSet:completeTree){
					if((currentNodeSet1.aState.equals(completeNodeSet.aState))&&completeNodeSet.hash==(currentNodeSet1.hash&completeNodeSet.hash)&&(currentNodeSet1.bStates.size() == completeNodeSet.bStates.size())){
					//if(true){
						containsAllbnState = true;
						for(final INestedWordAutomatonSimple<LETTER,STATE> bn:currentNodeSet1.bStates.keySet()){
							if(!currentNodeSet1.bStates.get(bn).equals(completeNodeSet.bStates.get(bn))){
								containsAllbnState=false;
							}
						}
						if(containsAllbnState){
							completeNodeSet.covering.add(currentNodeSet1);
							break;
						}
					}																	
				}
			}
			else{
				containsAllbnState=false;
				completeTree = new LinkedList<NodeData<LETTER,STATE>>();
			}
			if(containsAllbnState){
				currentNodeSet1.covered = true;
				coveredNodes.add(currentNodeSet1);
				toBeDeleteed.add(currentNodeSet1);
			}else{
				containsAllbnState = false;
				//for(NodeData<LETTER,STATE> currentNodeSet2:currentTree){
				//如果改變cover規則記得改回來!
				for(j = 0;j<i;j++){
					final NodeData<LETTER,STATE> currentNodeSet2 = currentTree.get(j);
					if(currentNodeSet1!=currentNodeSet2&&!(currentNodeSet2.covered)&&(currentNodeSet1.aState.equals(currentNodeSet2.aState))&&(currentNodeSet2.hash==(currentNodeSet1.hash&currentNodeSet2.hash)&&(currentNodeSet2.bStates.size() == currentNodeSet1.bStates.size()))){
					//if(currentNodeSet1!=currentNodeSet2&&!(currentNodeSet2.covered)){	
						containsAllbnState = true;
						for(final INestedWordAutomatonSimple<LETTER,STATE> bn:currentNodeSet2.bStates.keySet()){
							if(!currentNodeSet1.bStates.get(bn).equals(currentNodeSet2.bStates.get(bn))){
								containsAllbnState=false;
							}
						}
						if(containsAllbnState){
							currentNodeSet2.covering.add(currentNodeSet1);
							break;
						}
					}
				}
				if(!containsAllbnState){
					newNodeInCompleteTree = true;
					completeTree.add(currentNodeSet1);
				}
				else{
					currentNodeSet1.covered = true;
					coveredNodes.add(currentNodeSet1);
					toBeDeleteed.add(currentNodeSet1);
				}
			}
		}
		currentTree.removeAll(toBeDeleteed);
		return !newNodeInCompleteTree;
		/*
		boolean newNodeInCompleteTree = false;
		boolean containsAllbnState = false;
		HashMap<STATE,HashSet<NodeData<LETTER,STATE>>> toBeDeleteed = new HashMap<STATE,HashSet<NodeData<LETTER,STATE>>>();
		for(STATE currentAState : currentTree.keySet()){
			for(NodeData<LETTER,STATE> currentNodeSet1:currentTree.get(currentAState)){
				containsAllbnState = false;
				for(NodeData<LETTER,STATE> currentNodeSet2:currentTree.get(currentAState)){
					if(currentNodeSet1!=currentNodeSet2&&!(currentNodeSet2.covered)&&(currentNodeSet2.hash==(currentNodeSet1.hash&currentNodeSet2.hash))){
					//if(currentNodeSet1!=currentNodeSet2&&!(currentNodeSet2.covered)){	
						containsAllbnState = true;
						for(INestedWordAutomatonSimple<LETTER,STATE> bn:currentNodeSet2.bStates.keySet()){
							if(!currentNodeSet1.bStates.get(bn).containsAll(currentNodeSet2.bStates.get(bn))){
								containsAllbnState=false;
							}
						}
						if(containsAllbnState){
							currentNodeSet2.covering.add(currentNodeSet1);
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
								if(completeNodeSet.hash==(currentNodeSet1.hash&completeNodeSet.hash)){
								//if(true){
									containsAllbnState = true;
									for(INestedWordAutomatonSimple<LETTER,STATE> bn:currentNodeSet1.bStates.keySet()){
										if(!currentNodeSet1.bStates.get(bn).containsAll(completeNodeSet.bStates.get(bn))){
											containsAllbnState=false;
										}
									}
									if(containsAllbnState){
										completeNodeSet.covering.add(currentNodeSet1);
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
			}
		}
		for(STATE currentAState : toBeDeleteed.keySet()){
			currentTree.get(currentAState).removeAll(toBeDeleteed.get(currentAState));
		}
		return !newNodeInCompleteTree;
		*/
	}
	private boolean exceptionRun(){
		boolean foundFinal = false;
		for(final NodeData<LETTER,STATE> currentNodeSet:currentTree){
			if(local_mA.isFinal(currentNodeSet.aState)){
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
					errorNodes.add(currentNodeSet);
				}
			}
		}
		return errorNodes.peek() != null;
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
		if(errorNodes.peekFirst()!=null){
			return errorNodes.peekFirst().word;
		}
		else{
			return null;
		}
	}
	@Override
	public String operationName() {
		return "IncrementalInclusionCheck2DeadEndRemovalDeadEndRemoval";
	}
	@Override
	public String startMessage() {
		return "Start " + operationName();
	}
	
	@Override
	public String exitMessage() {
		if(errorNodes.peekFirst()!=null){
			mLogger.info("counterExample: "+errorNodes.peekFirst().word.getWord().toString());
		}
		mLogger.info("Total error: "+errorNodes.size()+" errors");
		mLogger.info("total:"+counter_total_nodes+"nodes");
		mLogger.info("total:"+allNodes.size()+"nodes");
		mLogger.info(completeTree.size()+"nodes in the end");
		mLogger.info("total:"+counter_run+"runs");
		return "Exit " + operationName();
	}
	@Override
	public Boolean getResult(){
		return errorNodes.peekFirst() == null;
	}
	@Override
	public boolean checkResult(IStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		boolean checkResult;
		if(errorNodes.peekFirst() != null){
			checkResult = compareInclusionCheckResult(localServiceProvider, 
					localStateFactory, local_mA, local_mB2, errorNodes.peekFirst().word);
		}
		else{
			checkResult = compareInclusionCheckResult(localServiceProvider, 
					localStateFactory, local_mA, local_mB2, null);
		}
		return checkResult;
//		if(((result==null)&&(new IncrementalInclusionCheck2DeadEndRemovalDeadEndRemoval<LETTER, STATE>(localServiceProvider,localStateFactory,local_mA,local_mB2).getResult()==null))||((result!=null)&&(new IncrementalInclusionCheck2DeadEndRemovalDeadEndRemoval<LETTER, STATE>(localServiceProvider,localStateFactory,local_mA,local_mB2).getResult()!=null))){
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
		for(final STATE state : bn.getInitialStates()){
			curStaSet.add(state);
		}
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
	private HashSet<NodeData<LETTER,STATE>> toBeKeepedNodes;
	private void deadEndRemove(){
		mLogger.info("Node size before delete: "+completeTree.size());
		nodeNumberBeforeDelete = completeTree.size();
		toBeKeepedNodes = new HashSet<NodeData<LETTER,STATE>>();
		int i = 0;
		HashSet<NodeData<LETTER,STATE>> toBeDeletedNodes = new HashSet<NodeData<LETTER,STATE>>(allNodes);
		for(final NodeData<LETTER,STATE> node : allNodes){
			node.keep = false;
		}
		for(final NodeData<LETTER,STATE> errorNode : errorNodes){
			deadEndRemoveWalker(errorNode);
		}
		toBeDeletedNodes.removeAll(toBeKeepedNodes);
		for(final NodeData<LETTER,STATE> nodeToBeDelete : toBeDeletedNodes){
			for(final NodeData<LETTER,STATE> uncoverNode : nodeToBeDelete.covering){
				uncoverNode.covered = false;
			}
			nodeToBeDelete.covering.clear();
			if(completeTree.contains(nodeToBeDelete)){
				completeTree.remove(nodeToBeDelete);
				alreadyDeltedNodes.add(nodeToBeDelete);
				i++;
			}
			else{
				if(coveredNodes.contains(nodeToBeDelete)){
					coveredNodes.remove(nodeToBeDelete);
				}
			}
			if(nodeToBeDelete.parentNode!=null){
				nodeToBeDelete.parentNode.DeadEndsRemoved = true;
			}
		}
		allNodes.removeAll(toBeDeletedNodes);
		mLogger.info("DeadEndRemove removes " + i + "nodes.");
		mLogger.info("Node size after delete: "+completeTree.size());
		toBeDeletedNodes = null;
		toBeKeepedNodes = null;
	}
	
	private void deadEndRemoveWalker(NodeData<LETTER,STATE> node){
		assert node !=null;
		if(!node.keep){
			node.keep = true;
			toBeKeepedNodes.add(node);
			for(final NodeData<LETTER,STATE> coveringNode : node.covering){
				deadEndRemoveWalker(coveringNode);
			}
			if(node.parentNode != null){
				deadEndRemoveWalker(node.parentNode);
			}
		}
	}
	
	private void addBStates(INestedWordAutomatonSimple<LETTER,STATE> nwa){
		HashSet<STATE> newStates = null;
		if(completeTree!=null){
			for(final NodeData<LETTER,STATE> node:completeTree){
				node.bStates.put(nwa, new HashSet<STATE>());
				newStates = NestedRunStates(nwa,node.word);
				node.bStates.get(nwa).addAll(newStates);
				for(final STATE s:newStates){
					node.hash = node.hash | s.hashCode();
				}
				if(node.covering!=null){
					node.covering.clear();
				}
			}
		}
		currentTree.addAll(coveredNodes);
		coveredNodes.clear();
		for(final NodeData<LETTER,STATE> node:currentTree){
			node.covered = false;
			node.bStates.put(nwa, new HashSet<STATE>());
			newStates = NestedRunStates(nwa,node.word);
			node.bStates.get(nwa).addAll(newStates);
			for(final STATE s:newStates){
				node.hash = node.hash | s.hashCode();
			}
		}
		checkErrorNodesAfterAddingB();
	}
	
	private void checkErrorNodesAfterAddingB(){
		boolean foundFinal = false;
		final HashSet<NodeData<LETTER,STATE>> toBeDeletedNodes = new HashSet<NodeData<LETTER,STATE>>();
		for(final NodeData<LETTER,STATE> checkingNode : errorNodes){
			foundFinal = false;
			for(final INestedWordAutomatonSimple<LETTER,STATE> bn:checkingNode.bStates.keySet()){
				for(final STATE bnState:checkingNode.bStates.get(bn)){
					if(bn.isFinal(bnState)){
						foundFinal = true;
						break;
					}
				}
				if(foundFinal){
					toBeDeletedNodes.add(checkingNode);
					break;
				}
			}
		}
		errorNodes.removeAll(toBeDeletedNodes);
		return;
		
	}
	public static <LETTER, STATE> void abortIfContainsCallOrReturn(INestedWordAutomatonSimple<LETTER, STATE> a) {
		if (!a.getCallAlphabet().isEmpty() || !a.getReturnAlphabet().isEmpty()) {
			throw new UnsupportedOperationException("Operation does not support call or return");
		}
	}
}
