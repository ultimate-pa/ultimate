package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.incremental_inclusion.AbstractIncrementalInclusionCheck;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

public class IncrementalInclusionCheck2<LETTER,STATE> extends AbstractIncrementalInclusionCheck<LETTER,STATE> implements IOperation<LETTER, STATE>  {

	private static Logger s_Logger;
	private NestedWordAutomaton<LETTER, STATE> local_m_A;
	private List<NestedWordAutomaton<LETTER, STATE>> local_m_B;
	private ArrayList<INestedWordAutomaton<LETTER,STATE>> local_m_B2;
	private StateFactory<STATE> localStateFactory;
	private IUltimateServiceProvider localServiceProvider;
	public HashMap<STATE,ArrayList<NodeData<LETTER,STATE>>> completeTree,currentTree;
	NestedRun<LETTER,STATE> result;
	class NodeData<A,B>{
		public HashMap<INestedWordAutomaton<A,B>,HashSet<B>> bStates;
		public NestedRun<A,B> word;
		public NodeData(){
			bStates = new HashMap<INestedWordAutomaton<A,B>,HashSet<B>>();
			word = null;
		}
		public NodeData(HashMap<INestedWordAutomaton<A,B>,HashSet<B>> data){
			bStates = data;
			word = null;
		}
		public NodeData(NestedRun<A,B> data){
			bStates = new HashMap<INestedWordAutomaton<A,B>,HashSet<B>>();
			word = data;
		}
		public NodeData(HashMap<INestedWordAutomaton<A,B>,HashSet<B>> data1,NestedRun<A,B> data2){
			bStates = data1;
			word = data2;
		}
	}
	
	public IncrementalInclusionCheck2(IUltimateServiceProvider services, StateFactory<STATE> sf,
			INestedWordAutomatonSimple<LETTER, STATE> a, ArrayList<INestedWordAutomaton<LETTER,STATE>> b){
		super(services,a);
		localServiceProvider = services;
		localStateFactory = sf;
		s_Logger = NestedWordAutomata.getLogger();
		s_Logger.info(startMessage());
		local_m_A = (NestedWordAutomaton<LETTER, STATE>) a;
		local_m_B = new ArrayList<NestedWordAutomaton<LETTER, STATE>>();
		local_m_B2 = b;
		for(INestedWordAutomaton<LETTER,STATE> bn : b){
				try {
					addSubtrahend(bn);
				} catch (AutomataLibraryException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			local_m_B.add((NestedWordAutomaton<LETTER, STATE>) bn);
		}
		run();
		s_Logger.info(exitMessage());
	}
	
	@SuppressWarnings("unchecked")
	public void run(){
		/*try {
			local_m_A = (new Determinize<LETTER,STATE> (localServiceProvider,localStateFactory,local_m_A)).getResult();
		} catch (OperationCanceledException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}*/
		HashMap<STATE,ArrayList<NodeData<LETTER,STATE>>> bufferedTree = null;
		HashMap<STATE,ArrayList<NodeData<LETTER,STATE>>> bufferedTree2 = null;
		result = null;
		completeTree = null;
		currentTree = null;
		for(INestedWordAutomaton<LETTER,STATE> B:local_m_B){
			if(!local_m_A.getAlphabet().containsAll(B.getAlphabet())){
				s_Logger.info("Alphabet inconsistent");
				return;
			}
		}
		do{
			if(currentTree==null){
				currentTree = expand(null);
				if(cover()||exceptionRun()){
					break;
				}
			}
			else{
				bufferedTree = null;
				for(LETTER alphabet:local_m_A.getAlphabet()){
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
								bufferedTree.put(state, new ArrayList<NodeData<LETTER,STATE>>());
								bufferedTree.get(state).addAll(bufferedTree2.get(state));
							}
						}
					}
				}
				currentTree = bufferedTree;
				if(cover()||exceptionRun()){
					break;
				}
			}
		}while(true);
			
		/*Set<STATE> newBState;
		boolean getConflict = false;
		boolean nextRun;
		for(INestedWordAutomaton<LETTER,STATE> B:local_m_B){
			if(!local_m_A.getAlphabet().containsAll(B.getAlphabet())){
				s_Logger.info("Alphabet inconsistent");
				return;
			}
		}
		currentTree = new HashMap<STATE,NodeData<LETTER,STATE>>();
		for(STATE state:local_m_A.getInitialStates()){
			currentTree.put(state, new NodeData<LETTER,STATE>(new HashMap<INestedWordAutomaton<LETTER,STATE>,ArrayList<STATE>>(), new NestedRun<LETTER,STATE>(state)));
		}
		for(INestedWordAutomaton<LETTER,STATE> automata:local_m_B){
			for(STATE state:automata.getInitialStates()){
				for(STATE key:currentTree.keySet()){
					if(!currentTree.get(key).bStates.containsKey(automata)){
						currentTree.get(key).bStates.put(automata,new ArrayList<STATE>());
					}
					currentTree.get(key).bStates.get(automata).add(state);
				}
			}
		}
		for(STATE state:local_m_A.getFinalStates()){
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
		completeTree = new HashMap<STATE,ArrayList<NodeData<LETTER,STATE>>>();
		for(STATE state:currentTree.keySet()){
			if(!completeTree.keySet().contains(state)){
				completeTree.put(state, new ArrayList<NodeData<LETTER,STATE>>());
			}
			completeTree.get(state).add(currentTree.get(state));
		}
		nextTree = new HashMap<STATE,NodeData<LETTER,STATE>>();
		for(STATE state : currentTree.keySet()){
			for(LETTER alphabet:local_m_A.getAlphabet()){
				for(OutgoingInternalTransition<LETTER, STATE> successingState:local_m_A.internalSuccessors(state, alphabet)){
					nextTree.put(successingState.getSucc(), new NodeData<LETTER, STATE>(new NestedRun<LETTER, STATE>(state,alphabet,0,successingState.getSucc())));
					for(INestedWordAutomaton<LETTER, STATE> automata: currentTree.get(state).bStates.keySet()){
						newBState = new HashSet<STATE>();
						for(STATE orginalBState:currentTree.get(state).bStates.get(automata)){
							for(OutgoingInternalTransition<LETTER, STATE> successingBState:local_m_B.get(local_m_B.indexOf(orginalBState)).internalSuccessors(orginalBState, alphabet)){
								newBState.add(successingBState.getSucc());
							}
						}
						nextTree.get(successingState.getSucc()).bStates.put(automata,(ArrayList<STATE>) newBState);
					}
				}
			}
		}
		currentTree = nextTree;*/
		
	}
	private HashMap<STATE,ArrayList<NodeData<LETTER,STATE>>> expand(LETTER alphabet){
		HashMap<STATE,ArrayList<NodeData<LETTER,STATE>>> nextNodes = new HashMap<STATE,ArrayList<NodeData<LETTER,STATE>>>();
		NodeData<LETTER,STATE> tempBNodeData = null;
		if(alphabet == null){
			for(STATE state:local_m_A.getInitialStates()){
				nextNodes.put(state, new ArrayList<NodeData<LETTER,STATE>>());
				tempBNodeData = new NodeData<LETTER,STATE>(new NestedRun<LETTER,STATE>(state));
				for(INestedWordAutomaton<LETTER,STATE> automata:local_m_B){
					tempBNodeData.bStates.put(automata, new HashSet<STATE>());
					for(STATE Bstate:automata.getInitialStates()){
						tempBNodeData.bStates.get(automata).add(Bstate);
					}
				}
				nextNodes.get(state).add(tempBNodeData);
			}
		}
		else{
			for(STATE state:currentTree.keySet()){
				for(OutgoingInternalTransition<LETTER, STATE> ATransition:local_m_A.internalSuccessors(state, alphabet)){
					if(!nextNodes.containsKey(ATransition.getSucc())){
						nextNodes.put(ATransition.getSucc(), new ArrayList<NodeData<LETTER,STATE>>());
					}
					for(NodeData<LETTER,STATE> currentNodeSet:currentTree.get(state)){
						ArrayList<STATE> newStateSequence = (ArrayList<STATE>) currentNodeSet.word.getStateSequence().clone();
						newStateSequence.add(ATransition.getSucc());
						tempBNodeData = new NodeData<LETTER,STATE>(new NestedRun<LETTER,STATE>(currentNodeSet.word.getWord().concatenate(new NestedWord<LETTER>(alphabet,-2)),newStateSequence));
						for(INestedWordAutomaton<LETTER,STATE> automata:currentNodeSet.bStates.keySet()){
							tempBNodeData.bStates.put(automata, new HashSet<STATE>());
							for(STATE Bstate:currentNodeSet.bStates.get(automata)){
								for(OutgoingInternalTransition<LETTER, STATE> BTransition:local_m_B.get(local_m_B.indexOf(automata)).internalSuccessors(Bstate, alphabet)){
									tempBNodeData.bStates.get(automata).add(BTransition.getSucc());
								}
							}
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
		ArrayList<NodeData<LETTER, STATE>> NodeDataToBeDelete = new ArrayList<NodeData<LETTER, STATE>>();
		for(STATE currentAState : currentTree.keySet()){
			for(NodeData<LETTER,STATE> currentNodeSet1:currentTree.get(currentAState)){
				containsAllbnState = false;
				for(NodeData<LETTER,STATE> currentNodeSet2:currentTree.get(currentAState)){
					if(currentNodeSet1!=currentNodeSet2&&!(NodeDataToBeDelete.contains(currentNodeSet2))){
						containsAllbnState = true;
						for(INestedWordAutomaton<LETTER,STATE> bn:currentNodeSet2.bStates.keySet()){
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
					NodeDataToBeDelete.add(currentNodeSet1);
				}
			}
			for(NodeData<LETTER,STATE> toBeDelete :NodeDataToBeDelete){
				currentTree.get(currentAState).remove(toBeDelete);
			}
		}
		NodeDataToBeDelete.clear();
		for(STATE currentAState : currentTree.keySet()){
			for(NodeData<LETTER,STATE> currentNodeSet:currentTree.get(currentAState)){
				if(completeTree!=null){
					if(completeTree.keySet().contains(currentAState)){
						for(NodeData<LETTER,STATE> completeNodeSet:completeTree.get(currentAState)){
							containsAllbnState = true;
							for(INestedWordAutomaton<LETTER,STATE> bn:currentNodeSet.bStates.keySet()){
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
						completeTree.put(currentAState, new ArrayList<NodeData<LETTER,STATE>>());
					}
				}
				else{
					completeTree = new HashMap<STATE,ArrayList<NodeData<LETTER,STATE>>>();
					containsAllbnState=false;
					completeTree.put(currentAState, new ArrayList<NodeData<LETTER,STATE>>());
				}
				if(!containsAllbnState){
					newNodeInCompleteTree = true;
					completeTree.get(currentAState).add(currentNodeSet);
				}
				else{
					NodeDataToBeDelete.add(currentNodeSet);
				}
			}
			for(NodeData<LETTER,STATE> toBeDelete :NodeDataToBeDelete){
				currentTree.get(currentAState).remove(toBeDelete);
			}
		}
		return !newNodeInCompleteTree;
	}
	private boolean exceptionRun(){
		result = null;
		boolean foundFinal = false;
		for(STATE currentAstate : currentTree.keySet()){
			if(local_m_A.getFinalStates().contains(currentAstate)){
				for(NodeData<LETTER,STATE> currentNodeSet:currentTree.get(currentAstate)){
					foundFinal = false;
					for(INestedWordAutomaton<LETTER,STATE> bn:currentNodeSet.bStates.keySet()){
						for(STATE bnState:currentNodeSet.bStates.get(bn)){
							if(bn.getFinalStates().contains(bnState)){
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
		return "Exit " + operationName();
	}
	public NestedRun<LETTER,STATE> getResult(){
		return getCounterexample();
	}
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		if(((result==null)&&(new IncrementalInclusionCheck2<LETTER, STATE>(localServiceProvider,localStateFactory,local_m_A,local_m_B2).getResult()==null))||((result!=null)&&(new IncrementalInclusionCheck2<LETTER, STATE>(localServiceProvider,localStateFactory,local_m_A,local_m_B2).getResult()!=null))){
			return true;
		}
		else{
			return false;
		}
	}
}
