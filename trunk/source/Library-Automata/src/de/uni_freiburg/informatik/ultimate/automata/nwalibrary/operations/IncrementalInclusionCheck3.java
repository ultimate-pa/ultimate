package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.incremental_inclusion.AbstractIncrementalInclusionCheck;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

/**
 * 
 * This is an implementation of incremental inclusion check based on the Rn Algorithm.<br/>
 * Rn sets are always empty when nodes are being created when expanding trees.
 * We use InclusionViaDIfference to check its correctness.
 * 
 * @author jefferyyjhsu@iis.sinica.edu.tw
 *
 * @param <LETTER>
 * @param <STATE>
 */

public class IncrementalInclusionCheck3<LETTER,STATE> extends AbstractIncrementalInclusionCheck<LETTER,STATE> implements IOperation<LETTER, STATE> {

	private static Logger s_Logger;
	private INestedWordAutomatonSimple<LETTER, STATE> local_m_A;
	private List<INestedWordAutomatonSimple<LETTER, STATE>> local_m_B;
	private ArrayList<INestedWordAutomatonSimple<LETTER,STATE>> local_m_B2;
	private StateFactory<STATE> localStateFactory;
	private IUltimateServiceProvider localServiceProvider;
	//public HashMap<STATE,ArrayList<NodeData<LETTER,STATE>>> completeTree,currentTree,terminalNodes;
	//public HashMap<STATE,HashMap<NodeData<LETTER,STATE>,ArrayList<NodeData<LETTER,STATE>>>> coverage;
	NestedRun<LETTER,STATE> result;
	ArrayList<Leaf<LETTER,STATE>> startingLeafs = null,currentTerminalLeafs = null, completeLeafSet;
	HashSet<Leaf<LETTER,STATE>> bufferedLeaf;
	class Leaf<LET,STA>{
		public HashMap<LETTER,HashSet<Leaf<LET,STA>>> nextLeaf;
		public HashSet<Leaf<LET,STA>> covering;
		public Leaf<LET,STA> directParentLeaf,orginLeaf,coveredBy;
		public HashMap<INestedWordAutomatonSimple<LET,STA>,HashSet<STA>> bStates;
		public NestedRun<LET,STA> word;
		public STA aState;
		public Leaf(STA a,NestedRun<LET,STA> wd) {
			coveredBy = null;
			covering = new HashSet<Leaf<LET,STA>>();
			nextLeaf = new HashMap<LETTER,HashSet<Leaf<LET,STA>>>();
			bStates = new HashMap<INestedWordAutomatonSimple<LET,STA>,HashSet<STA>>();
			aState = a;
			word = wd;
		}
		public void setOrgin(Leaf<LET,STA> org){
			orginLeaf = org;
		}
		public void setParent(Leaf<LET,STA> par){
			directParentLeaf = par;
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
	public void addSubtrahend(INestedWordAutomatonSimple<LETTER, STATE> nwa) throws AutomataLibraryException {
		super.addSubtrahend(nwa);
		local_m_B.add(nwa);
		local_m_B2.add(nwa);
		run();
	}
	public IncrementalInclusionCheck3(IUltimateServiceProvider services, StateFactory<STATE> sf,
			INestedWordAutomatonSimple<LETTER, STATE> a, ArrayList<INestedWordAutomatonSimple<LETTER,STATE>> b){
		super(services,a);
		localServiceProvider = services;
		localStateFactory = sf;
		s_Logger = NestedWordAutomata.getLogger();
		s_Logger.info(startMessage());
		completeLeafSet = new ArrayList<Leaf<LETTER,STATE>>();
		local_m_A =  a;
		local_m_B = new ArrayList<INestedWordAutomatonSimple<LETTER, STATE>>();
		local_m_B2 = new ArrayList<INestedWordAutomatonSimple<LETTER, STATE>>(b);
		for(INestedWordAutomatonSimple<LETTER,STATE> bn : b){
			try {
				super.addSubtrahend(bn);
			} catch (AutomataLibraryException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			local_m_B.add((INestedWordAutomatonSimple<LETTER, STATE>) bn);
		}
		run();
		s_Logger.info(exitMessage());
	}
	@SuppressWarnings("unchecked")
	public void run(){
		result = null;
		for(INestedWordAutomatonSimple<LETTER,STATE> B:local_m_B){
			if(!local_m_A.getAlphabet().containsAll(B.getAlphabet())){
				s_Logger.info("Alphabet inconsistent");
				return;
			}
		}
		do{
			if(currentTerminalLeafs==null){
				currentTerminalLeafs = expand(null);
				startingLeafs = (ArrayList<IncrementalInclusionCheck3<LETTER, STATE>.Leaf<LETTER, STATE>>) currentTerminalLeafs.clone();
				if(refine_exceptionRun()||cover()){
					break;
				}
			}
			else{
				bufferedLeaf = null;
				for(LETTER alphabet:local_m_A.getAlphabet()){
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
	private ArrayList<Leaf<LETTER,STATE>> expand(LETTER alphabet){
		ArrayList<Leaf<LETTER,STATE>> nextTerminal = new ArrayList<Leaf<LETTER,STATE>>();
		Leaf<LETTER,STATE> newLeaf = null;
		if(alphabet == null){
			for(STATE state:local_m_A.getInitialStates()){
				newLeaf = new Leaf<LETTER,STATE>(state,new NestedRun<LETTER,STATE>(state));
				newLeaf.setOrgin(newLeaf);
				newLeaf.setParent(null);
				newLeaf.bStates = new HashMap<INestedWordAutomatonSimple<LETTER,STATE>,HashSet<STATE>>();
				nextTerminal.add(newLeaf);
				completeLeafSet.add(newLeaf);
			}
		}
		else{
			for(Leaf<LETTER,STATE> oldLeaf:currentTerminalLeafs){
				if (oldLeaf.coveredBy==null){
					for(OutgoingInternalTransition<LETTER, STATE> ATransition:local_m_A.internalSuccessors(oldLeaf.aState, alphabet)){
						ArrayList<STATE> newStateSequence = (ArrayList<STATE>) oldLeaf.word.getStateSequence().clone();
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
						nextTerminal.add(newLeaf);
					}	
				}
				else{
					newLeaf = oldLeaf;
					nextTerminal.add(newLeaf);
				}
			}
		}
		return nextTerminal;
	}
	private boolean cover(){
		boolean newNodeInCompleteTree = false;
		boolean containsAllbnState = false;
		Leaf<LETTER,STATE> BufCurLeaf2 = null;
		for(Leaf<LETTER,STATE> curLeaf1 : currentTerminalLeafs){
			containsAllbnState = false;
			if(curLeaf1.coveredBy == null){
				for(Leaf<LETTER,STATE> curLeaf2 : completeLeafSet){
					BufCurLeaf2 = curLeaf2;
					if(curLeaf2.coveredBy == null&&curLeaf1!=curLeaf2&&curLeaf1.aState.equals(curLeaf2.aState)){
						containsAllbnState = true;
						for(INestedWordAutomatonSimple<LETTER,STATE> bn:curLeaf2.bStates.keySet()){
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
		HashSet<Leaf<LETTER,STATE>> newEdge = new HashSet<Leaf<LETTER,STATE>>(),toBeRemoved = new HashSet<Leaf<LETTER,STATE>>(), toBeRemovedBuffer = new HashSet<Leaf<LETTER,STATE>>();
		boolean firstRound = true;;
		ArrayList<HashSet<STATE>> newBnStates = null;
		int i;
		Leaf<LETTER,STATE> cursorLeaf = null,cursorLeaf2 = null,newEdgeLeaf = null;
		HashSet<INestedWordAutomatonSimple<LETTER,STATE>> CHKedBn = new HashSet<INestedWordAutomatonSimple<LETTER,STATE>>();
		boolean chkExpandedBn = true;
		result = null;
		boolean foundFinal = false;
		for(Leaf<LETTER,STATE> curLeaf :currentTerminalLeafs){
			if(local_m_A.isFinal(curLeaf.aState)){
				CHKedBn.clear();
				chkExpandedBn = true;
				foundFinal = false;
				for(INestedWordAutomatonSimple<LETTER,STATE> bn:curLeaf.bStates.keySet()){
					for(STATE bnState:curLeaf.bStates.get(bn)){
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
						for(INestedWordAutomatonSimple<LETTER,STATE> bn:cursorLeaf2.bStates.keySet()){
							if(!curLeaf.bStates.keySet().contains(bn)&&!CHKedBn.contains(bn)){
								CHKedBn.add(bn);
								if(NestedRunAcceptanceChk(bn,curLeaf.word)){
									chkExpandedBn = false;
									foundFinal = true;
									newBnStates = NestedRunStates(bn,curLeaf.word);
									i = newBnStates.size()-1;
									cursorLeaf = curLeaf;
									firstRound = true;
									newEdgeLeaf = null;
									while(cursorLeaf!=null){
										if(!cursorLeaf.bStates.containsKey(bn)){
											if(firstRound == false){
												newEdgeLeaf = cursorLeaf;
											}
											cursorLeaf.bStates.put(bn, newBnStates.get(i));
											for(Leaf<LETTER,STATE> orgCover:cursorLeaf.covering){
												orgCover.coveredBy = null;
											}
											cursorLeaf.covering.clear();
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
						for(INestedWordAutomatonSimple<LETTER,STATE> bn:local_m_B){
							if(!curLeaf.bStates.keySet().contains(bn)&&!CHKedBn.contains(bn)){
								if(NestedRunAcceptanceChk(bn,curLeaf.word)){
									foundFinal = true;
									newBnStates = NestedRunStates(bn,curLeaf.word);
									i = newBnStates.size()-1;
									cursorLeaf = curLeaf;
									firstRound = true;
									newEdgeLeaf = null;
									while(cursorLeaf!=null){
										if(!cursorLeaf.bStates.containsKey(bn)){
											if(firstRound == false){
												newEdgeLeaf = cursorLeaf;
											}
											cursorLeaf.bStates.put(bn, newBnStates.get(i));
											for(Leaf<LETTER,STATE> orgCover:cursorLeaf.covering){
												orgCover.coveredBy = null;
											}
											cursorLeaf.covering.clear();
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
			for(Leaf<LETTER,STATE> cursorLeaf3:newEdge){
				toBeRemoved.addAll(childrenLeafWalker(cursorLeaf3));
			}
			for(Leaf<LETTER,STATE> cursorLeaf3:newEdge){
				if(toBeRemoved.contains(cursorLeaf3)){
					toBeRemovedBuffer.add(cursorLeaf3);
				}
			}
			newEdge.removeAll(toBeRemovedBuffer);
			toBeRemovedBuffer.clear();
			for(Leaf<LETTER,STATE> cursorLeaf3 :currentTerminalLeafs){
				if(toBeRemoved.contains(cursorLeaf3)){
					toBeRemovedBuffer.add(cursorLeaf3);
				}
			}
			currentTerminalLeafs.removeAll(toBeRemovedBuffer);
			completeLeafSet.removeAll(toBeRemoved);
			currentTerminalLeafs.addAll(newEdge);
		}
		return result!=null;
	}
	private HashSet<Leaf<LETTER,STATE>> childrenLeafWalker (Leaf<LETTER,STATE> curLeaf){
		HashSet<Leaf<LETTER,STATE>> leafSet = new HashSet<Leaf<LETTER,STATE>>();
		for(LETTER alphabet:curLeaf.nextLeaf.keySet()){
			for(Leaf<LETTER,STATE> childrenLeaf:curLeaf.nextLeaf.get(alphabet)){
				leafSet.add(childrenLeaf);
				leafSet.addAll(childrenLeafWalker(childrenLeaf));
			}
		}
		return leafSet;
	}
	@SuppressWarnings("unchecked")
	private ArrayList<HashSet<STATE>> NestedRunStates(INestedWordAutomatonSimple<LETTER,STATE> bn,NestedRun<LETTER,STATE> word){
		ArrayList<HashSet<STATE>> result = new ArrayList<HashSet<STATE>>();
		HashSet<STATE> curStaSet = null;
		Iterable<OutgoingInternalTransition<LETTER,STATE>>nextStaSet = null;
		HashSet<STATE> newStaSet;
		curStaSet = new HashSet<STATE>();
		curStaSet.addAll((HashSet<STATE>)bn.getInitialStates());
		result.add((HashSet<STATE>) curStaSet.clone());
		if(word.getWord().length()!=0){
			for(LETTER alphabet:word.getWord().asList()){
				newStaSet = new HashSet<STATE>();
				for(STATE OState:curStaSet){
					nextStaSet = bn.internalSuccessors(OState, alphabet);
					for(OutgoingInternalTransition<LETTER,STATE> newState:nextStaSet){
						newStaSet.add(newState.getSucc());
					}
				}
				curStaSet.clear();
				curStaSet = newStaSet;
				result.add((HashSet<STATE>) curStaSet.clone());
			}
		}
		return result;
	}
	@SuppressWarnings("unchecked")
	private boolean NestedRunAcceptanceChk(INestedWordAutomatonSimple<LETTER,STATE> bn,NestedRun<LETTER,STATE> word){
		boolean result = false;
		HashSet<STATE> curStaSet = null;
		Iterable<OutgoingInternalTransition<LETTER,STATE>>nextStaSet = null;
		HashSet<STATE> newStaSet;
		curStaSet = new HashSet<STATE>();
		curStaSet.addAll((HashSet<STATE>)bn.getInitialStates());
		if(word.getWord().length()!=0){
			for(LETTER alphabet:word.getWord().asList()){
				newStaSet = new HashSet<STATE>();
				for(STATE OState:curStaSet){
					nextStaSet = bn.internalSuccessors(OState, alphabet);
					for(OutgoingInternalTransition<LETTER,STATE> newState:nextStaSet){
						newStaSet.add(newState.getSucc());
					}
				}
				curStaSet.clear();
				curStaSet = newStaSet;
				//curStaSet = nextStaSet;
			}
		}
		for(STATE state:curStaSet){
			if(bn.isFinal(state)){
				result = true;
				break;
			}
		}
		return result;
	}
	public NestedRun<LETTER,STATE> getCounterexample(){
		return result;
	}
	@Override
	public String operationName() {
		return "IncrementalInclusionCheck3.";
	}
	@Override
	public String startMessage() {
		return "Start " + operationName();
	}
	
	@Override
	public String exitMessage() {
		return "Exit " + operationName();
	}
	/*public Boolean getResult() throws OperationCanceledException{
		return checkResult(localStateFactory);
	}*/
	public Boolean getResult() throws OperationCanceledException{
		return result == null;
	}
	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		boolean checkResult = IncrementalInclusionCheck2.compareInclusionCheckResult(
				localServiceProvider, localStateFactory, local_m_A, local_m_B2, result);
		return checkResult;
//		//INestedWordAutomatonSimple<LETTER, STATE> a;
//		if(getResult().equals((new IncrementalInclusionCheck2<LETTER, STATE>(localServiceProvider,localStateFactory,local_m_A,local_m_B2)).getResult())){
//		//if(getResult2().equals((new InclusionViaDifference(localServiceProvider,localStateFactory,).getCounterexample().getLength()==0))){
//			return true;
//		}
//		else{
//			return false;
//		}
	}
}
