package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.incremental_inclusion.AbstractIncrementalInclusionCheck;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.incremental_inclusion.InclusionViaDifference;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

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
	private static Logger s_Logger;
	private INestedWordAutomatonSimple<LETTER, STATE> local_m_A;
	private List<INestedWordAutomatonSimple<LETTER, STATE>> local_m_B;
	private List<INestedWordAutomatonSimple<LETTER,STATE>> local_m_B2;
	private StateFactory<STATE> localStateFactory;
	private IUltimateServiceProvider localServiceProvider;
	public HashMap<STATE,HashSet<NodeData<LETTER,STATE>>> completeTree,currentTree;
	NestedRun<LETTER,STATE> result;
	class NodeData<A,B>{
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
		s_Logger.info(startMessage());
		super.addSubtrahend(nwa);
		local_m_B.add(nwa);
		local_m_B2.add(nwa);
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
				if (!m_Services.getProgressMonitorService().continueProcessing()) {
	                throw new OperationCanceledException();
				}
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
								bufferedTree.put(state, new HashSet<NodeData<LETTER,STATE>>());
								bufferedTree.get(state).addAll(bufferedTree2.get(state));
							}
						}
					}
			}
			currentTree = bufferedTree;
			}while(true);
		}
		s_Logger.info(exitMessage());
	}
	public IncrementalInclusionCheck2(IUltimateServiceProvider services, StateFactory<STATE> sf,
			INestedWordAutomatonSimple<LETTER, STATE> a, List<INestedWordAutomatonSimple<LETTER,STATE>> b) throws OperationCanceledException{
		super(services,a);
		IncrementalInclusionCheck2.abortIfContainsCallOrReturn(a);
		localServiceProvider = services;
		localStateFactory = sf;
		s_Logger = NestedWordAutomata.getLogger();
		s_Logger.info(startMessage());
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
			local_m_B.add(bn);
		}
		run();
		s_Logger.info(exitMessage());
	}
	
	@SuppressWarnings("unchecked")
	public void run() throws OperationCanceledException{
		/*try {
			local_m_A = (new Determinize<LETTER,STATE> (localServiceProvider,localStateFactory,local_m_A)).getResult();
		} catch (OperationCanceledException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}*/
		HashMap<STATE,HashSet<NodeData<LETTER,STATE>>> bufferedTree = null;
		HashMap<STATE,HashSet<NodeData<LETTER,STATE>>> bufferedTree2 = null;
		result = null;
		completeTree = null;
		currentTree = null;
		for(INestedWordAutomatonSimple<LETTER,STATE> B:local_m_B){
			if(!local_m_A.getAlphabet().containsAll(B.getAlphabet())){
				s_Logger.info("Alphabet inconsistent");
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
				if (!m_Services.getProgressMonitorService().continueProcessing()) {
		                throw new OperationCanceledException();
		        }
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
		for(INestedWordAutomaton<LETTER,STATE> B:local_m_B){
			if(!local_m_A.getAlphabet().containsAll(B.getAlphabet())){
				s_Logger.info("Alphabet inconsistent");
				return;
			}
		}
		currentTree = new HashMap<STATE,NodeData<LETTER,STATE>>();
		for(STATE state:local_m_A.getInitialStates()){
			currentTree.put(state, new NodeData<LETTER,STATE>(new HashMap<INestedWordAutomaton<LETTER,STATE>,HashSet<STATE>>(), new NestedRun<LETTER,STATE>(state)));
		}
		for(INestedWordAutomaton<LETTER,STATE> automata:local_m_B){
			for(STATE state:automata.getInitialStates()){
				for(STATE key:currentTree.keySet()){
					if(!currentTree.get(key).bStates.containsKey(automata)){
						currentTree.get(key).bStates.put(automata,new HashSet<STATE>());
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
		completeTree = new HashMap<STATE,HashSet<NodeData<LETTER,STATE>>>();
		for(STATE state:currentTree.keySet()){
			if(!completeTree.keySet().contains(state)){
				completeTree.put(state, new HashSet<NodeData<LETTER,STATE>>());
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
						nextTree.get(successingState.getSucc()).bStates.put(automata,(HashSet<STATE>) newBState);
					}
				}
			}
		}
		currentTree = nextTree;*/
		
	}
	private HashMap<STATE,HashSet<NodeData<LETTER,STATE>>> expand(LETTER alphabet){
		HashMap<STATE,HashSet<NodeData<LETTER,STATE>>> nextNodes = new HashMap<STATE,HashSet<NodeData<LETTER,STATE>>>();
		NodeData<LETTER,STATE> tempBNodeData = null;
		if(alphabet == null){
			for(STATE state:local_m_A.getInitialStates()){
				nextNodes.put(state, new HashSet<NodeData<LETTER,STATE>>());
				tempBNodeData = new NodeData<LETTER,STATE>(new NestedRun<LETTER,STATE>(state));
				for(INestedWordAutomatonSimple<LETTER,STATE> automata:local_m_B){
					tempBNodeData.bStates.put(automata, new HashSet<STATE>());
					for(STATE Bstate:automata.getInitialStates()){
						tempBNodeData.bStates.get(automata).add(Bstate);
					}
				}
				counter_total_nodes++;
				nextNodes.get(state).add(tempBNodeData);
			}
		}
		else{
			for(STATE state:currentTree.keySet()){
				for(OutgoingInternalTransition<LETTER, STATE> ATransition:local_m_A.internalSuccessors(state, alphabet)){
					for(NodeData<LETTER,STATE> currentNodeSet:currentTree.get(state)){
						if(!currentNodeSet.covered){
							@SuppressWarnings("unchecked")
							ArrayList<STATE> newStateSequence = (ArrayList<STATE>) currentNodeSet.word.getStateSequence().clone();
							newStateSequence.add(ATransition.getSucc());
							tempBNodeData = new NodeData<LETTER,STATE>(new NestedRun<LETTER,STATE>(currentNodeSet.word.getWord().concatenate(new NestedWord<LETTER>(alphabet,-2)),newStateSequence));
							for(INestedWordAutomatonSimple<LETTER,STATE> automata:currentNodeSet.bStates.keySet()){
								tempBNodeData.bStates.put(automata, new HashSet<STATE>());
								for(STATE Bstate:currentNodeSet.bStates.get(automata)){
									for(OutgoingInternalTransition<LETTER, STATE> BTransition:local_m_B.get(local_m_B.indexOf(automata)).internalSuccessors(Bstate, alphabet)){
										tempBNodeData.bStates.get(automata).add(BTransition.getSucc());
									}
								}
							}
							counter_total_nodes++;
							if(!nextNodes.containsKey(ATransition.getSucc())){
								nextNodes.put(ATransition.getSucc(), new HashSet<NodeData<LETTER,STATE>>());
							}
							nextNodes.get(ATransition.getSucc()).add(tempBNodeData);
						}
						else{
							if(!nextNodes.containsKey(state)){
								nextNodes.put(state, new HashSet<NodeData<LETTER,STATE>>());
							}
							if(!nextNodes.get(state).contains(currentNodeSet)){
								nextNodes.get(state).add(currentNodeSet);
							}
						}
					}
				}
			}
		}
		return nextNodes;
	}
	private boolean cover(){
		boolean newNodeInCompleteTree = false;
		boolean containsAllbnState = false;
		for(STATE currentAState : currentTree.keySet()){
			for(NodeData<LETTER,STATE> currentNodeSet1:currentTree.get(currentAState)){
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
					}	
				}
			}
		}
		for(STATE currentAState : currentTree.keySet()){
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
		}
		return !newNodeInCompleteTree;
	}
	private boolean exceptionRun(){
		result = null;
		boolean foundFinal = false;
		for(STATE currentAstate : currentTree.keySet()){
			if(local_m_A.isFinal(currentAstate)){
				for(NodeData<LETTER,STATE> currentNodeSet:currentTree.get(currentAstate)){
					foundFinal = false;
					for(INestedWordAutomatonSimple<LETTER,STATE> bn:currentNodeSet.bStates.keySet()){
						for(STATE bnState:currentNodeSet.bStates.get(bn)){
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
		s_Logger.info("total:"+counter_total_nodes+"nodes");
		s_Logger.info(counter_total_nodes+"nodes in the end");
		s_Logger.info("total:"+counter_run+"runs");
		return "Exit " + operationName();
	}
	public Boolean getResult(){
		return result == null;
	}
	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		boolean checkResult = compareInclusionCheckResult(localServiceProvider, 
				localStateFactory, local_m_A, local_m_B2, result);
		return checkResult;
//		if(((result==null)&&(new IncrementalInclusionCheck2<LETTER, STATE>(localServiceProvider,localStateFactory,local_m_A,local_m_B2).getResult()==null))||((result!=null)&&(new IncrementalInclusionCheck2<LETTER, STATE>(localServiceProvider,localStateFactory,local_m_A,local_m_B2).getResult()!=null))){
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
			IUltimateServiceProvider services, 
			StateFactory<STATE> stateFactory, 
			INestedWordAutomatonSimple<LETTER, STATE> a, 
			List<INestedWordAutomatonSimple<LETTER, STATE>> b, 
			NestedRun<LETTER,STATE> ctrEx) throws AutomataLibraryException {
		InclusionViaDifference<LETTER, STATE> ivd = 
				new InclusionViaDifference<LETTER, STATE>(services, stateFactory, a);
		// add all b automata
		for (INestedWordAutomatonSimple<LETTER, STATE> bi : b) {
			ivd.addSubtrahend(bi);
		}
		// obtain counterexample, counterexample is null if inclusion holds
		NestedRun<LETTER, STATE> ivdCounterexample = ivd.getCounterexample();
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
			}
		}
		return curStaSet;
	}
	private void addBStates(INestedWordAutomatonSimple<LETTER,STATE> nwa){
		if(completeTree!=null){
			for(STATE aSTATE:completeTree.keySet()){
				for(NodeData<LETTER,STATE> node:completeTree.get(aSTATE)){
					node.bStates.put(nwa, new HashSet<STATE>());
					node.bStates.get(nwa).addAll(NestedRunStates(nwa,node.word));
				}
			}
		}
		for(STATE aSTATE:currentTree.keySet()){
			for(NodeData<LETTER,STATE> node:currentTree.get(aSTATE)){
				node.covered = false;
				node.bStates.put(nwa, new HashSet<STATE>());
				node.bStates.get(nwa).addAll(NestedRunStates(nwa,node.word));
			}
		}
	}
	public static <LETTER, STATE> void abortIfContainsCallOrReturn(INestedWordAutomatonSimple<LETTER, STATE> a) {
		if (!a.getCallAlphabet().isEmpty() || !a.getReturnAlphabet().isEmpty()) {
			throw new UnsupportedOperationException("Operation does not support call or return");
		}
	}
}
