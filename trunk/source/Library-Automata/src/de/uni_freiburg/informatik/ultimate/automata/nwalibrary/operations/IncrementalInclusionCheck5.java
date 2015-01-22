package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayList;
import java.util.Collection;
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
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IncrementalInclusionCheck3.Leaf;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.incremental_inclusion.AbstractIncrementalInclusionCheck;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

/**
 * 
 * This is an implementation of incremental inclusion check based on the Rn Algorithm with force covering.<br/>
 * Unlike IncrementalInclusionCheck3, initial Rn set of each new node will be the expansion of its parent node's Rn set.<br/>
 * We use InclusionViaDIfference to check its correctness.
 * 
 * @author jefferyyjhsu@iis.sinica.edu.tw
 *
 * @param <LETTER>
 * @param <STATE>
 */

public class IncrementalInclusionCheck5<LETTER,STATE> extends AbstractIncrementalInclusionCheck<LETTER,STATE> implements IOperation<LETTER, STATE> {
	public int counter_run = 0, counter_total_nodes = 0 ;
	private int counter;
	private static Logger s_Logger;
	private INestedWordAutomatonSimple<LETTER, STATE> local_m_A;
	private List<INestedWordAutomatonSimple<LETTER, STATE>> local_m_B;
	private ArrayList<INestedWordAutomatonSimple<LETTER,STATE>> local_m_B2;
	private StateFactory<STATE> localStateFactory;
	private IUltimateServiceProvider localServiceProvider;
	//private int counter;
	//public HashMap<STATE,ArrayList<NodeData<LETTER,STATE>>> completeTree,currentTree,terminalNodes;
	//public HashMap<STATE,HashMap<NodeData<LETTER,STATE>,ArrayList<NodeData<LETTER,STATE>>>> coverage;
	NestedRun<LETTER,STATE> result;
	ArrayList<Leaf<LETTER,STATE>> startingLeafs = null,currentTerminalLeafs = null, completeLeafSet;
	HashSet<Leaf<LETTER,STATE>> bufferedLeaf;
	class Leaf<LET,STA>{
		public HashMap<LETTER,HashSet<Leaf<LET,STA>>> nextLeaf;
		public HashSet<Leaf<LET,STA>> covering,ParentLeafs;
		public Leaf<LET,STA> directParentLeaf,orginLeaf,coveredBy;
		public HashMap<INestedWordAutomatonSimple<LET,STA>,HashSet<STA>> bStates,completeBStates;
		public NestedRun<LET,STA> word;
		public STA aState;
		public Leaf(STA a,NestedRun<LET,STA> wd) {
			coveredBy = null;
			covering = new HashSet<Leaf<LET,STA>>();
			ParentLeafs = new HashSet<Leaf<LET,STA>>();
			nextLeaf = new HashMap<LETTER,HashSet<Leaf<LET,STA>>>();
			bStates = new HashMap<INestedWordAutomatonSimple<LET,STA>,HashSet<STA>>();
			completeBStates = new HashMap<INestedWordAutomatonSimple<LET,STA>,HashSet<STA>>();
			aState = a;
			word = wd;
		}
		public void setOrgin(Leaf<LET,STA> org){
			orginLeaf = org;
		}
		public void setParent(Leaf<LET,STA> par){
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
	public void addSubtrahend(INestedWordAutomatonSimple<LETTER, STATE> nwa) throws AutomataLibraryException {
		super.addSubtrahend(nwa);
		local_m_B.add(nwa);
		local_m_B2.add(nwa);
		run2(nwa);
		s_Logger.info("total:"+counter_total_nodes+"nodes");
		s_Logger.info(completeLeafSet.size()+"nodes in the end");
		s_Logger.info("total:"+counter_run+"runs");
	}
	public IncrementalInclusionCheck5(IUltimateServiceProvider services, StateFactory<STATE> sf,
			INestedWordAutomatonSimple<LETTER, STATE> a, List<INestedWordAutomatonSimple<LETTER,STATE>> b) throws OperationCanceledException{
		super(services,a);
		counter = 0;
		IncrementalInclusionCheck2.abortIfContainsCallOrReturn(a);
		//counter = 0;
		localServiceProvider = services;
		localStateFactory = sf;
		s_Logger = NestedWordAutomata.getLogger();
		
		s_Logger.info(startMessage());
		completeLeafSet = new ArrayList<Leaf<LETTER,STATE>>();
		local_m_A = a;
		local_m_B = new ArrayList<INestedWordAutomatonSimple<LETTER, STATE>>();
		local_m_B2 = new ArrayList<INestedWordAutomatonSimple<LETTER, STATE>>(b);
		for(INestedWordAutomatonSimple<LETTER,STATE> bn : b){
			try {
				super.addSubtrahend(bn);
			} catch (AutomataLibraryException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			local_m_B.add(bn);
		}
		run();
		s_Logger.info(exitMessage());
	}
	@SuppressWarnings("unchecked")
	public void run2(INestedWordAutomatonSimple<LETTER, STATE> nwa) throws OperationCanceledException{
		if(!local_m_A.getAlphabet().containsAll(nwa.getAlphabet())){
			s_Logger.info("Alphabet inconsistent");
			return;
		}
		completeBStatesAdder(null,nwa);
		if(result!=null){
			do{
				if (!m_Services.getProgressMonitorService().continueProcessing()) {
	                throw new OperationCanceledException();
				}
				counter_run++;
				if(refine_exceptionRun()||cover()){
					break;
				}
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
			}while(true);
		}
	}
	@SuppressWarnings("unchecked")
	public void run() throws OperationCanceledException{
		result = null;
		for(INestedWordAutomatonSimple<LETTER,STATE> B:local_m_B){
			if(!local_m_A.getAlphabet().containsAll(B.getAlphabet())){
				s_Logger.info("Alphabet inconsistent");
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
				if (!m_Services.getProgressMonitorService().continueProcessing()) {
	                throw new OperationCanceledException();
				}
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
		//s_Logger.info(counter++);
		Iterable<OutgoingInternalTransition<LETTER,STATE>>nextStaSet = null;
		ArrayList<Leaf<LETTER,STATE>> nextTerminal = new ArrayList<Leaf<LETTER,STATE>>();
		HashSet<STATE> newStaSet;
		Leaf<LETTER,STATE> newLeaf = null;
		if(alphabet == null){
			for(STATE state:local_m_A.getInitialStates()){
				newLeaf = new Leaf<LETTER,STATE>(state,new NestedRun<LETTER,STATE>(state));
				newLeaf.setOrgin(newLeaf);
				newLeaf.setParent(null);
				newLeaf.bStates = new HashMap<INestedWordAutomatonSimple<LETTER,STATE>,HashSet<STATE>>();
				newLeaf.completeBStates = new HashMap<INestedWordAutomatonSimple<LETTER,STATE>,HashSet<STATE>>();
				for(INestedWordAutomatonSimple<LETTER,STATE> bn:local_m_B){
					newLeaf.completeBStates.put(bn, (HashSet<STATE>) bn.getInitialStates());
				}
				nextTerminal.add(newLeaf);
				counter_total_nodes++;
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
						/*if(oldLeaf.bStates.keySet().size()!=0){
						//if(true){
							for(INestedWordAutomatonSimple<LETTER,STATE> bn:oldLeaf.bStates.keySet()){
							//for(INestedWordAutomaton<LETTER,STATE> bn:local_m_B){
								newLeaf.bStates.put(bn, new HashSet<STATE>());
								newStaSet = new HashSet<STATE>();
								for(STATE state:oldLeaf.bStates.get(bn)){
									nextStaSet = bn.internalSuccessors(state, alphabet);
									for(OutgoingInternalTransition<LETTER,STATE> newState:nextStaSet){
										newStaSet.add(newState.getSucc());
									}
								}
								newLeaf.bStates.get(bn).addAll((Collection<? extends STATE>) newStaSet.clone());
							}
						}*/
						for(INestedWordAutomatonSimple<LETTER,STATE> bn:local_m_B){
							newLeaf.completeBStates.put(bn, new HashSet<STATE>());
							newStaSet = new HashSet<STATE>();
							for(STATE state:oldLeaf.completeBStates.get(bn)){
								nextStaSet = bn.internalSuccessors(state, alphabet);
								for(OutgoingInternalTransition<LETTER,STATE> newState:nextStaSet){
									newStaSet.add(newState.getSucc());
								}
							}
							newLeaf.completeBStates.get(bn).addAll((Collection<? extends STATE>) newStaSet.clone());
						}
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
					newLeaf = oldLeaf;
					nextTerminal.add(newLeaf);
				}
			}
		}
		return nextTerminal;
	}
	private boolean cover(){
		ArrayList<HashSet<STATE>> newBnStates = null;
		int i;
		boolean newNodeInCompleteTree = false,forceCoveringExecuted = false;
		boolean containsAllbnState = false;
		Leaf<LETTER,STATE> BufCurLeaf2 = null, cursorLeaf = null;
		do{
			newNodeInCompleteTree = false;
			forceCoveringExecuted = false;
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
						containsAllbnState = false;
						for(Leaf<LETTER,STATE> curLeaf2 : completeLeafSet){
							BufCurLeaf2 = curLeaf2;
							if(curLeaf2.coveredBy == null&&curLeaf1!=curLeaf2&&curLeaf1.aState.equals(curLeaf2.aState)){
								containsAllbnState = true;
								for(INestedWordAutomatonSimple<LETTER,STATE> bn:curLeaf2.bStates.keySet()){
									if(curLeaf1.completeBStates.keySet().contains(bn)){
										if(!curLeaf1.completeBStates.get(bn).containsAll(curLeaf2.bStates.get(bn))){
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
							for(INestedWordAutomatonSimple<LETTER,STATE> bn:BufCurLeaf2.bStates.keySet()){
								if(!curLeaf1.bStates.containsKey(bn)){
									newBnStates = NestedRunStates(bn,curLeaf1.word);
									i = newBnStates.size()-1;
									cursorLeaf = curLeaf1;
									while(cursorLeaf!=null){
										if(!cursorLeaf.bStates.containsKey(bn)){
											cursorLeaf.bStates.put(bn, newBnStates.get(i));
											for(Leaf<LETTER,STATE> orgCover:cursorLeaf.covering){
												forceCoveringExecuted = true; 
												orgCover.coveredBy = null;
											}
											cursorLeaf.covering.clear();
										}
										cursorLeaf = cursorLeaf.directParentLeaf;
										i--;
									}
								}
							}
							curLeaf1.coveredBy = BufCurLeaf2;
							BufCurLeaf2.covering.add(curLeaf1);
						}
						else{
							newNodeInCompleteTree = true;	
						}
					}
				}
			}
		}while(forceCoveringExecuted);
		return !newNodeInCompleteTree;
	}
	private boolean refine_exceptionRun(){
		HashSet<Leaf<LETTER,STATE>> newEdge = new HashSet<Leaf<LETTER,STATE>>(),toBeRemoved = new HashSet<Leaf<LETTER,STATE>>(), toBeRemovedBuffer = new HashSet<Leaf<LETTER,STATE>>();
		boolean firstRound = true;
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
											cursorLeaf.bStates.put(bn, newBnStates.get(i));
											for(Leaf<LETTER,STATE> orgCover:cursorLeaf.covering){
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
											cursorLeaf.bStates.put(bn, newBnStates.get(i));
											for(Leaf<LETTER,STATE> orgCover:cursorLeaf.covering){
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
			for(Leaf<LETTER,STATE> cursorLeaf3:newEdge){
				cursorLeaf3.nextLeaf.clear();
			}
			for(Leaf<LETTER,STATE> cursorLeaf3:toBeRemovedBuffer){
				for(Leaf<LETTER,STATE> cursorLeaf4:cursorLeaf3.covering){
					cursorLeaf4.coveredBy=null;
				}
			}
			for(Leaf<LETTER,STATE> cursorLeaf3:toBeRemoved){
				for(Leaf<LETTER,STATE> cursorLeaf4:cursorLeaf3.covering){
					cursorLeaf4.coveredBy=null;
				}
			}
			currentTerminalLeafs.removeAll(toBeRemovedBuffer);
			completeLeafSet.removeAll(toBeRemoved);
			currentTerminalLeafs.addAll(newEdge);
			for(Leaf<LETTER,STATE> cursorLeaf3:newEdge){
				cursorLeaf3.nextLeaf.clear();
			}
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
	private void completeBStatesAdder(Leaf<LETTER,STATE> parent, INestedWordAutomatonSimple<LETTER,STATE> nwa){
		if(parent==null){
			for(Leaf<LETTER,STATE> curLeaf :startingLeafs){
				curLeaf.completeBStates.put(nwa, new HashSet<STATE>());
				curLeaf.completeBStates.get(nwa).addAll((Collection<? extends STATE>) nwa.getInitialStates());
				if(hasChildrenLeaf(curLeaf)){
					completeBStatesAdder(curLeaf,nwa);
				}
			}
		}
		else{
			Iterable<OutgoingInternalTransition<LETTER,STATE>>nextStaSet = null;
			for(LETTER alphabet:local_m_A.getAlphabet()){
				HashSet<STATE> newBStaes = new HashSet<STATE>();
				for(STATE OState : parent.completeBStates.get(nwa)){
					nextStaSet = nwa.internalSuccessors(OState, alphabet);
					for(OutgoingInternalTransition<LETTER,STATE> newState:nextStaSet){
						newBStaes.add(newState.getSucc());
					}
				}
				if(parent.nextLeaf.get(alphabet)!=null){
					for(Leaf<LETTER,STATE> childrenLeaf:parent.nextLeaf.get(alphabet)){
						childrenLeaf.completeBStates.put(nwa, (HashSet<STATE>) newBStaes.clone());
						if(hasChildrenLeaf(childrenLeaf)){
							completeBStatesAdder(childrenLeaf,nwa);
						}
					}
				}
			}
		}
	}
	private boolean hasChildrenLeaf(Leaf<LETTER,STATE> parent){
		boolean hasChildren = false;
		for(LETTER alphabet:parent.nextLeaf.keySet()){
			if(parent.nextLeaf.get(alphabet).size()>0){
				hasChildren = true;
			}
		}
		return hasChildren;
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
	public boolean CoveringCheck(Leaf<LETTER,STATE> checkingLeaf){
		boolean containsAllbnState = false;
		for(Leaf<LETTER,STATE> curLeaf2 : completeLeafSet){
			if(curLeaf2.coveredBy == null&&checkingLeaf!=curLeaf2&&checkingLeaf.aState.equals(curLeaf2.aState)&&!curLeaf2.ParentLeafs.contains(checkingLeaf)){
				containsAllbnState = true;
				for(INestedWordAutomatonSimple<LETTER,STATE> bn:curLeaf2.bStates.keySet()){
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
	public NestedRun<LETTER,STATE> getCounterexample(){
		return result;
	}
	@Override
	public String operationName() {
		return "IncrementalInclusionCheck5.";
	}
	@Override
	public String startMessage() {
		return "Start " + operationName();
	}
	
	@Override
	public String exitMessage() {
		s_Logger.info("total:"+counter_total_nodes+"nodes");
		s_Logger.info(completeLeafSet.size()+"nodes in the end");
		s_Logger.info("total:"+counter_run+"runs");
		return "Exit " + operationName();
	}
	public Boolean getResult(){
		return result == null;
	}
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		boolean checkResult = IncrementalInclusionCheck2.compareInclusionCheckResult(
				localServiceProvider, localStateFactory, local_m_A, local_m_B2, result);
		return checkResult;
//		if(getResult().equals((new IncrementalInclusionCheck2<LETTER, STATE>(localServiceProvider,localStateFactory,local_m_A,local_m_B2)).getResult())){
//			//if(getResult2().equals((new InclusionViaDifference(localServiceProvider,localStateFactory,).getCounterexample().getLength()==0))){
//				return true;
//			}
//			else{
//				return false;
//			}
	}
}
