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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.incrementalinclusion.AbstractIncrementalInclusionCheck;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;

/**
 * 
 * This is an implementation of incremental inclusion check based on the Rn Algorithm.(trace base version) <br/>
 * Rn sets are always empty when nodes are being created when expanding trees.
 * We use InclusionViaDIfference to check its correctness.
 * 
 * @author jefferyyjhsu@iis.sinica.edu.tw
 *
 * @param <LETTER>
 * @param <STATE>
 */

public class IncrementalInclusionCheck3_2<LETTER,STATE> extends AbstractIncrementalInclusionCheck<LETTER,STATE> implements IOperation<LETTER, STATE> {
	public int counter_run = 0, counter_total_nodes = 0 ;
	private final INestedWordAutomatonSimple<LETTER, STATE> local_mA;
	private final List<INestedWordAutomatonSimple<LETTER, STATE>> local_mB;
	private final ArrayList<INestedWordAutomatonSimple<LETTER,STATE>> local_mB2;
	private final StateFactory<STATE> localStateFactory;
	private final AutomataLibraryServices localServiceProvider;
	private ArrayList<STATE> newBnStates;
	//public HashMap<STATE,ArrayList<NodeData<LETTER,STATE>>> completeTree,currentTree,terminalNodes;
	//public HashMap<STATE,HashMap<NodeData<LETTER,STATE>,ArrayList<NodeData<LETTER,STATE>>>> coverage;
	NestedRun<LETTER,STATE> result;
	ArrayList<Leaf<LETTER,STATE>> startingLeafs = null,currentTerminalLeafs = null, completeLeafSet;
	HashSet<Leaf<LETTER,STATE>> bufferedLeaf;
	class Leaf<LET,STA>{
		public HashMap<LETTER,HashSet<Leaf<LET,STA>>> nextLeaf;
		public HashSet<Leaf<LET,STA>> covering,ParentLeafs;
		public Leaf<LET,STA> directParentLeaf,orginLeaf,coveredBy;
		public HashMap<INestedWordAutomatonSimple<LET,STA>,HashSet<STA>> bStates;
		public NestedRun<LET,STA> word;
		public STA aState;
		public Leaf(final STA a,final NestedRun<LET,STA> wd) {
			coveredBy = null;
			covering = new HashSet<Leaf<LET,STA>>();
			ParentLeafs = new HashSet<Leaf<LET,STA>>();
			nextLeaf = new HashMap<LETTER,HashSet<Leaf<LET,STA>>>();
			bStates = new HashMap<INestedWordAutomatonSimple<LET,STA>,HashSet<STA>>();
			aState = a;
			word = wd;
		}
		public void setOrgin(final Leaf<LET,STA> org){
			orginLeaf = org;
		}
		public void setParent(final Leaf<LET,STA> par){
			directParentLeaf = par;
			if(par!=null){
				ParentLeafs.addAll(par.ParentLeafs);
				ParentLeafs.add(par);
			}
		}
	}
	/*class NodeData<A,B>{
		public HashMap<INestedWordAutomaton<A,B>,HashSet<B>> bStates;
		public NestedRun<A,B> word;
		private boolean covered;
		public NodeData(){
			bStates = new HashMap<INestedWordAutomaton<A,B>,HashSet<B>>();
			word = null;
			covered = false;
		}
		public NodeData(HashMap<INestedWordAutomaton<A,B>,HashSet<B>> data){
			bStates = data;
			word = null;
			covered = false;
		}
		public NodeData(NestedRun<A,B> data){
			bStates = new HashMap<INestedWordAutomaton<A,B>,HashSet<B>>();
			word = data;
			covered = false;
		}
		public NodeData(HashMap<INestedWordAutomaton<A,B>,HashSet<B>> data1,NestedRun<A,B> data2){
			bStates = data1;
			word = data2;
			covered = false;
		}
	}*/
	@Override
	public void addSubtrahend(final INestedWordAutomatonSimple<LETTER, STATE> nwa) throws AutomataLibraryException {
		super.addSubtrahend(nwa);
		mLogger.info(startMessage());
		local_mB.add(nwa);
		local_mB2.add(nwa);
		run2(nwa);
		mLogger.info(exitMessage());
		//completeLeafSet = new ArrayList<Leaf<LETTER,STATE>>();
		//startingLeafs = null;
		//currentTerminalLeafs = null;
		//run();
	}
	public IncrementalInclusionCheck3_2(final AutomataLibraryServices services, final StateFactory<STATE> sf,
			final INestedWordAutomatonSimple<LETTER, STATE> a, final List<INestedWordAutomatonSimple<LETTER,STATE>> b) throws AutomataLibraryException{
		super(services,a);
		IncrementalInclusionCheck2.abortIfContainsCallOrReturn(a);
		localServiceProvider = services;
		localStateFactory = sf;
		mLogger.info(startMessage());
		completeLeafSet = new ArrayList<Leaf<LETTER,STATE>>();
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
	public void run2(final INestedWordAutomatonSimple<LETTER, STATE> nwa) throws AutomataOperationCanceledException{
		if(!local_mA.getAlphabet().containsAll(nwa.getAlphabet())){
			mLogger.info("Alphabet inconsistent");
			return;
		}
		if(result!=null){
			do{
				if (!mServices.getProgressMonitorService().continueProcessing()) {
	                throw new AutomataOperationCanceledException(this.getClass());
				}
				counter_run++;
				if(refine_exceptionRun()||cover()){
					break;
				}
				bufferedLeaf = null;
				for(final LETTER alphabet:local_mA.getAlphabet()){
					if(bufferedLeaf == null){
						bufferedLeaf = new HashSet<Leaf<LETTER,STATE>>();
						bufferedLeaf.addAll(expand(alphabet));
					}
					else{
						bufferedLeaf.addAll(expand(alphabet));
					}
				}
				currentTerminalLeafs.clear();
				currentTerminalLeafs.addAll(bufferedLeaf);
			}while(true);
		}
	}
	@SuppressWarnings("unchecked")
	public void run() throws AutomataLibraryException{
		result = null;
		for(final INestedWordAutomatonSimple<LETTER,STATE> B:local_mB){
			if(!local_mA.getAlphabet().containsAll(B.getAlphabet())){
				mLogger.info("Alphabet inconsistent");
				return;
			}
		}
		do{
			counter_run++;
			if(currentTerminalLeafs==null){
				currentTerminalLeafs = expand(null);
				startingLeafs = (ArrayList<Leaf<LETTER, STATE>>) currentTerminalLeafs.clone();
				if(refine_exceptionRun()||cover()){
					break;
				}
			}
			else{
				if (!mServices.getProgressMonitorService().continueProcessing()) {
	                throw new AutomataOperationCanceledException(this.getClass());
				}
				bufferedLeaf = null;
				for(final LETTER alphabet:local_mA.getAlphabet()){
					if(bufferedLeaf == null){
						bufferedLeaf = new HashSet<Leaf<LETTER,STATE>>();
						bufferedLeaf.addAll(expand(alphabet));
					}
					else{
						bufferedLeaf.addAll(expand(alphabet));
					}
				}
				currentTerminalLeafs.clear();
				currentTerminalLeafs.addAll(bufferedLeaf);
				if(refine_exceptionRun()||cover()){
					break;
				}
			}
		}while(true);
	}
	@SuppressWarnings("unchecked")
	private ArrayList<Leaf<LETTER,STATE>> expand(final LETTER alphabet){
		final ArrayList<Leaf<LETTER,STATE>> nextTerminal = new ArrayList<Leaf<LETTER,STATE>>();
		Leaf<LETTER,STATE> newLeaf = null;
		if(alphabet == null){
			for(final STATE state:local_mA.getInitialStates()){
				newLeaf = new Leaf<LETTER,STATE>(state,new NestedRun<LETTER,STATE>(state));
				newLeaf.setOrgin(newLeaf);
				newLeaf.setParent(null);
				newLeaf.bStates = new HashMap<INestedWordAutomatonSimple<LETTER,STATE>,HashSet<STATE>>();
				nextTerminal.add(newLeaf);
				counter_total_nodes++;
				completeLeafSet.add(newLeaf);
			}
		}
		else{
			for(final Leaf<LETTER,STATE> oldLeaf:currentTerminalLeafs){
				if (oldLeaf.coveredBy==null){
					for(final OutgoingInternalTransition<LETTER, STATE> ATransition:local_mA.internalSuccessors(oldLeaf.aState, alphabet)){
						final ArrayList<STATE> newStateSequence = (ArrayList<STATE>) oldLeaf.word.getStateSequence().clone();
						newStateSequence.add(ATransition.getSucc());
						newLeaf = new Leaf<LETTER,STATE>(ATransition.getSucc(),new NestedRun<LETTER,STATE>(oldLeaf.word.getWord().concatenate(new NestedWord<LETTER>(alphabet,-2)),newStateSequence));
						newLeaf.setOrgin(oldLeaf.orginLeaf);
						newLeaf.setParent(oldLeaf);
						newLeaf.bStates = new HashMap<INestedWordAutomatonSimple<LETTER,STATE>,HashSet<STATE>>();
						if(!oldLeaf.nextLeaf.keySet().contains(alphabet)){
							oldLeaf.nextLeaf.put(alphabet, new HashSet<Leaf<LETTER,STATE>>());
						}
						oldLeaf.nextLeaf.get(alphabet).add(newLeaf);
						completeLeafSet.add(newLeaf);
						counter_total_nodes++;
						nextTerminal.add(newLeaf);
					}
				}
				else{
					nextTerminal.add(oldLeaf);
				}
			}
		}
		return nextTerminal;
	}
	private boolean cover(){
		boolean newNodeInCompleteTree = false;
		boolean containsAllbnState = false;
		Leaf<LETTER,STATE> BufCurLeaf2 = null;
		for(final Leaf<LETTER,STATE> curLeaf1 : currentTerminalLeafs){
			containsAllbnState = false;
			if(curLeaf1.coveredBy == null){
				for(final Leaf<LETTER,STATE> curLeaf2 : completeLeafSet){
					BufCurLeaf2 = curLeaf2;
					if(curLeaf2.coveredBy == null&&curLeaf1!=curLeaf2&&curLeaf1.aState.equals(curLeaf2.aState)){
						containsAllbnState = true;
						for(final INestedWordAutomatonSimple<LETTER,STATE> bn:curLeaf2.bStates.keySet()){
							if(curLeaf1.bStates.keySet().contains(bn)){
								if(!curLeaf1.bStates.get(bn).containsAll(curLeaf2.bStates.get(bn))){
									containsAllbnState=false;
								}
							}
							else{
								containsAllbnState = false;
							}
							if(!containsAllbnState){
								break;
							}
						}
						if(containsAllbnState){
							break;
						}
					}
				}
				if(containsAllbnState){
					curLeaf1.coveredBy = BufCurLeaf2;
					BufCurLeaf2.covering.add(curLeaf1);
				}
				else{
					newNodeInCompleteTree = true;
				}
			}
		}
		
		return !newNodeInCompleteTree;
	}
	private boolean refine_exceptionRun(){
		final HashSet<Leaf<LETTER,STATE>> newEdge = new HashSet<Leaf<LETTER,STATE>>(),toBeRemoved = new HashSet<Leaf<LETTER,STATE>>(), toBeRemovedBuffer = new HashSet<Leaf<LETTER,STATE>>();
		boolean firstRound = true;
		int i;
		Leaf<LETTER,STATE> cursorLeaf = null,cursorLeaf2 = null,newEdgeLeaf = null;
		final HashSet<INestedWordAutomatonSimple<LETTER,STATE>> CHKedBn = new HashSet<INestedWordAutomatonSimple<LETTER,STATE>>();
		boolean chkExpandedBn = true;
		result = null;
		boolean foundFinal = false;
		for(final Leaf<LETTER,STATE> curLeaf :currentTerminalLeafs){
			if(local_mA.isFinal(curLeaf.aState)){
				CHKedBn.clear();
				chkExpandedBn = true;
				foundFinal = false;
				for(final INestedWordAutomatonSimple<LETTER,STATE> bn:curLeaf.bStates.keySet()){
					for(final STATE bnState:curLeaf.bStates.get(bn)){
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
					cursorLeaf2=curLeaf.directParentLeaf;
					while(cursorLeaf2!=null){
						for(final INestedWordAutomatonSimple<LETTER,STATE> bn:cursorLeaf2.bStates.keySet()){
							if(!CHKedBn.contains(bn)){
								CHKedBn.add(bn);
								if(NestedRunAcceptanceChk(bn,curLeaf.word)){
									chkExpandedBn = false;
									foundFinal = true;
									i = newBnStates.size()-1;
									cursorLeaf = curLeaf;
									firstRound = true;
									newEdgeLeaf = null;
									while(cursorLeaf!=null){
										if(!cursorLeaf.bStates.containsKey(bn)||!cursorLeaf.bStates.get(bn).contains(newBnStates.get(i))){
											if(!cursorLeaf.bStates.containsKey(bn)){
												cursorLeaf.bStates.put(bn,new HashSet<STATE>());
											}
											cursorLeaf.bStates.get(bn).add(newBnStates.get(i));
											for(final Leaf<LETTER,STATE> orgCover:cursorLeaf.covering){
												orgCover.coveredBy = null;
											}
											cursorLeaf.covering.clear();
											if(firstRound == false&&CoveringCheck(cursorLeaf)){
												newEdgeLeaf = cursorLeaf;
											}
										}
										else{
											break;
										}
										cursorLeaf = cursorLeaf.directParentLeaf;
										firstRound = false;
										i--;
									}
									if(newEdgeLeaf!=null){
										newEdge.add(newEdgeLeaf);
									}
									break;
								}
							}
						}
						if(foundFinal==true){
							break;
						}
						cursorLeaf2=cursorLeaf2.directParentLeaf;
					}
					if(chkExpandedBn){
						for(final INestedWordAutomatonSimple<LETTER,STATE> bn:local_mB){
							if(!CHKedBn.contains(bn)){
								if(NestedRunAcceptanceChk(bn,curLeaf.word)){
									foundFinal = true;
									i = newBnStates.size()-1;
									cursorLeaf = curLeaf;
									firstRound = true;
									newEdgeLeaf = null;
									while(cursorLeaf!=null){
										if(!cursorLeaf.bStates.containsKey(bn)||!cursorLeaf.bStates.get(bn).contains(newBnStates.get(i))){
											if(!cursorLeaf.bStates.containsKey(bn)){
												cursorLeaf.bStates.put(bn,new HashSet<STATE>());
											}
											cursorLeaf.bStates.get(bn).add(newBnStates.get(i));
											for(final Leaf<LETTER,STATE> orgCover:cursorLeaf.covering){
												orgCover.coveredBy = null;
											}
											cursorLeaf.covering.clear();
											if(firstRound == false&&CoveringCheck(cursorLeaf)){
												newEdgeLeaf = cursorLeaf;
											}
										}
										else{
											break;
										}
										cursorLeaf = cursorLeaf.directParentLeaf;
										firstRound = false;
										i--;
									}
									if(newEdgeLeaf!=null){
										newEdge.add(newEdgeLeaf);
									}
									break;
								}
							}
						}
					}
					if(!foundFinal){
						result = curLeaf.word;
						break;
					}
				}
			}
		}
		if(result==null){
			for(final Leaf<LETTER,STATE> cursorLeaf3:newEdge){
				toBeRemoved.addAll(childrenLeafWalker(cursorLeaf3));
			}
			for(final Leaf<LETTER,STATE> cursorLeaf3:newEdge){
				if(toBeRemoved.contains(cursorLeaf3)){
					toBeRemovedBuffer.add(cursorLeaf3);
				}
			}
			newEdge.removeAll(toBeRemovedBuffer);
			toBeRemovedBuffer.clear();
			for(final Leaf<LETTER,STATE> cursorLeaf3 :currentTerminalLeafs){
				if(toBeRemoved.contains(cursorLeaf3)){
					toBeRemovedBuffer.add(cursorLeaf3);
				}
			}
			for(final Leaf<LETTER,STATE> cursorLeaf3:newEdge){
				cursorLeaf3.nextLeaf.clear();
			}
			for(final Leaf<LETTER,STATE> cursorLeaf3:toBeRemovedBuffer){
				for(final Leaf<LETTER,STATE> cursorLeaf4:cursorLeaf3.covering){
					cursorLeaf4.coveredBy=null;
				}
			}
			for(final Leaf<LETTER,STATE> cursorLeaf3:toBeRemoved){
				for(final Leaf<LETTER,STATE> cursorLeaf4:cursorLeaf3.covering){
					cursorLeaf4.coveredBy=null;
				}
			}
			currentTerminalLeafs.removeAll(toBeRemovedBuffer);
			completeLeafSet.removeAll(toBeRemoved);
			currentTerminalLeafs.addAll(newEdge);
		}
		return result!=null;
	}
	private HashSet<Leaf<LETTER,STATE>> childrenLeafWalker (final Leaf<LETTER,STATE> curLeaf){
		final HashSet<Leaf<LETTER,STATE>> leafSet = new HashSet<Leaf<LETTER,STATE>>();
		for(final LETTER alphabet:curLeaf.nextLeaf.keySet()){
			for(final Leaf<LETTER,STATE> childrenLeaf:curLeaf.nextLeaf.get(alphabet)){
				leafSet.add(childrenLeaf);
				leafSet.addAll(childrenLeafWalker(childrenLeaf));
			}
		}
		return leafSet;
	}
	@SuppressWarnings("unchecked")
	private ArrayList<STATE> NestedRunStates(final INestedWordAutomatonSimple<LETTER,STATE> bn,final NestedRun<LETTER,STATE> word){
		final ArrayList<HashSet<STATE>> result = new ArrayList<HashSet<STATE>>();
		final ArrayList<STATE> result2 = new ArrayList<STATE>(word.getLength());
		HashSet<STATE> curStaSet = null;
		Iterable<OutgoingInternalTransition<LETTER,STATE>>nextStaSet = null;
		final List<LETTER> wordList = word.getWord().asList();
		boolean breakLoop = false;
		HashSet<STATE> newStaSet;
		curStaSet = new HashSet<STATE>();
		curStaSet.addAll((HashSet<STATE>)bn.getInitialStates());
		result.add((HashSet<STATE>) curStaSet.clone());
		int i;
		if(word.getWord().length()!=0){
			for(final LETTER alphabet:wordList){
				newStaSet = new HashSet<STATE>();
				for(final STATE OState:curStaSet){
					nextStaSet = bn.internalSuccessors(OState, alphabet);
					for(final OutgoingInternalTransition<LETTER,STATE> newState:nextStaSet){
						newStaSet.add(newState.getSucc());
					}
				}
				curStaSet.clear();
				curStaSet = newStaSet;
				result.add((HashSet<STATE>) curStaSet.clone());
			}
		}
		for(i=0;i<result.size();i++){
			result2.add(null);
		}
		i = result.size()-1;
		while(i>=0){
			if(i==result.size()-1){
				for(final STATE s:result.get(i)){
					if(bn.isFinal(s)){
						result2.set(i, s);
						break;
					}
				}
			}
			else{
				for(final STATE s: result.get(i)){
					breakLoop = false;
					nextStaSet = bn.internalSuccessors(s, wordList.get(i));
					for(final OutgoingInternalTransition<LETTER,STATE> newState:nextStaSet){
						if(newState.getSucc().equals(result2.get(i+1))){
							result2.set(i,s);
							breakLoop = true;
							break;
						}
					}
					if(breakLoop){
						break;
					}
				}
			}
			i--;
		}
		return result2;
	}
	@SuppressWarnings("unchecked")
	private boolean NestedRunAcceptanceChk(final INestedWordAutomatonSimple<LETTER,STATE> bn,final NestedRun<LETTER,STATE> word){
		final ArrayList<HashSet<STATE>> staSetList = new ArrayList<HashSet<STATE>>();
		newBnStates = new ArrayList<STATE>(word.getLength());
		int i;
		boolean result = false,breakLoop = false;
		final List<LETTER> wordList = word.getWord().asList();
		HashSet<STATE> curStaSet = null;
		Iterable<OutgoingInternalTransition<LETTER,STATE>>nextStaSet = null;
		HashSet<STATE> newStaSet;
		curStaSet = new HashSet<STATE>();
		curStaSet.addAll((HashSet<STATE>)bn.getInitialStates());
		staSetList.add((HashSet<STATE>) curStaSet.clone());
		if(word.getWord().length()!=0){
			for(final LETTER alphabet:wordList){
				newStaSet = new HashSet<STATE>();
				for(final STATE OState:curStaSet){
					nextStaSet = bn.internalSuccessors(OState, alphabet);
					for(final OutgoingInternalTransition<LETTER,STATE> newState:nextStaSet){
						newStaSet.add(newState.getSucc());
					}
				}
				curStaSet.clear();
				curStaSet = newStaSet;
				staSetList.add((HashSet<STATE>) curStaSet.clone());
				//curStaSet = nextStaSet;
			}
		}
		for(final STATE state:curStaSet){
			if(bn.isFinal(state)){
				result = true;
				break;
			}
		}
		if(result == true){
			for(i=0;i<staSetList.size();i++){
				newBnStates.add(null);
			}
			i = staSetList.size()-1;
			while(i>=0){
				if(i==staSetList.size()-1){
					for(final STATE s:staSetList.get(i)){
						if(bn.isFinal(s)){
							newBnStates.set(i, s);
							break;
						}
					}
				}
				else{
					for(final STATE s: staSetList.get(i)){
						breakLoop = false;
						nextStaSet = bn.internalSuccessors(s, wordList.get(i));
						for(final OutgoingInternalTransition<LETTER,STATE> newState:nextStaSet){
							if(newState.getSucc().equals(newBnStates.get(i+1))){
								newBnStates.set(i,s);
								breakLoop = true;
								break;
							}
						}
						if(breakLoop){
							break;
						}
					}
				}
				i--;
			}
		}
		return result;
	}
	public boolean CoveringCheck(final Leaf<LETTER,STATE> checkingLeaf){
		boolean containsAllbnState = false;
		for(final Leaf<LETTER,STATE> curLeaf2 : completeLeafSet){
			if(curLeaf2.coveredBy == null&&checkingLeaf!=curLeaf2&&checkingLeaf.aState.equals(curLeaf2.aState)&&!curLeaf2.ParentLeafs.contains(checkingLeaf)){
				containsAllbnState = true;
				for(final INestedWordAutomatonSimple<LETTER,STATE> bn:curLeaf2.bStates.keySet()){
					if(checkingLeaf.bStates.keySet().contains(bn)){
						if(!checkingLeaf.bStates.get(bn).containsAll(curLeaf2.bStates.get(bn))){
							containsAllbnState=false;
						}
					}
					else{
						containsAllbnState = false;
					}
					if(!containsAllbnState){
						break;
					}
				}
				if(containsAllbnState){
					break;
				}
			}
		}
		return containsAllbnState;
	}
	@Override
	public NestedRun<LETTER,STATE> getCounterexample(){
		return result;
	}
	@Override
	public String operationName() {
		return "IncrementalInclusionCheck3_2.";
	}
	@Override
	public String startMessage() {
		return "Start " + operationName();
	}
	
	@Override
	public String exitMessage() {
		mLogger.info("total:"+counter_total_nodes+"nodes");
		mLogger.info(completeLeafSet.size()+"nodes in the end");
		mLogger.info("total:"+counter_run+"runs");
		return "Exit " + operationName();
	}
	/*public Boolean getResult() throws OperationCanceledException{
		return checkResult(localStateFactory);
	}*/
	@Override
	public Boolean getResult() {
		return result == null;
	}
	@Override
	public boolean checkResult(final StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		final boolean checkResult = IncrementalInclusionCheck2.compareInclusionCheckResult(
				localServiceProvider, localStateFactory, local_mA, local_mB2, result);
		return checkResult;
//		//INestedWordAutomatonSimple<LETTER, STATE> a;
//		if(getResult().equals((new IncrementalInclusionCheck2<LETTER, STATE>(localServiceProvider,localStateFactory,local_mA,local_mB2)).getResult())){
//		//if(getResult2().equals((new InclusionViaDifference(localServiceProvider,localStateFactory,).getCounterexample().getLength()==0))){
//			return true;
//		}
//		else{
//			return false;
//		}
	}
}
