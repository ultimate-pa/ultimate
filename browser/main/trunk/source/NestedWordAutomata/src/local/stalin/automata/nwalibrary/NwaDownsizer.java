package local.stalin.automata.nwalibrary;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import local.stalin.automata.Activator;
import local.stalin.core.api.StalinServices;

import org.apache.log4j.Logger;

public class NwaDownsizer<S, C> {
	
	private static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	List<StateDl<S,C>> workList = new LinkedList<StateDl<S,C>>();

	
	
	void downsize(NestedWordAutomaton<S, C> nwa) {
		
		s_Logger.info("States before downsizing: " + nwa.getAllStates().size());
		int[] transBefore = nwa.transitions();
		s_Logger.info("Transitions before downsizing: " + 
			(transBefore[0]+transBefore[1]+transBefore[2]));
		
		
		for (IState<S, C> state : nwa.getAllStates()) {
			if (isUseless((StateDl<S, C>) state)) {
				workList.add((StateDl<S, C>) state);
			}
		}
		
		while(!workList.isEmpty()) {
			StateDl<S,C> removalState = workList.remove(0);
			assert nwa.allStatesRegistered();
			Set<StateDl<S, C>> uselessPredecessors = 
							removeAndGetUselessPredecessors(removalState,nwa);
			for (StateDl<S,C> state : uselessPredecessors) {
				if (!workList.contains(state)) {
					workList.add(state);
				}
			}
		}
		s_Logger.info("States after downsizing: " + nwa.getAllStates().size());
		int[] transAfter = nwa.transitions();
		s_Logger.info("Transitions after downsizing: " + 
				(transAfter[0]+transAfter[1]+transAfter[2]));
	}
	

	Set<StateDl<S,C>> removeAndGetUselessPredecessors(StateDl<S,C> state,
												NestedWordAutomaton<S, C> nwa) {
		StateDl<S,C> stateDl = (StateDl<S,C>) state;
		Set<StateDl<S,C>> uselessPredecessors = new HashSet<StateDl<S,C>>();
		
		List<S> symbolsInternal = new ArrayList<S>(state.getInSymbolsInternal());
		for(S symbol : symbolsInternal) {
			List<IState<S,C>> predecessors = 
				new ArrayList<IState<S,C>>(state.getInInternal(symbol));
			for (IState<S,C> pred : predecessors) {
				StateDl<S,C> predDl = (StateDl<S,C>) pred;
				boolean existed = predDl.delInternalTransition(symbol, state);
				assert(existed);
				if(predDl != state && isUseless(predDl)) {
					uselessPredecessors.add(predDl);
				}
			}
		}
		List<S> symbolsCall = new ArrayList<S>(state.getInSymbolsCall());
		for(S symbol : symbolsCall) {
			List<IState<S,C>> predecessors = 
				new ArrayList<IState<S,C>>(state.getInCall(symbol));
			for (IState<S,C> pred : predecessors) {
				StateDl<S,C> predDl = (StateDl<S,C>) pred;
				boolean existed = predDl.delCallTransition(symbol, state);
				assert(existed);
				if(predDl != state && isUseless(predDl)) {
					uselessPredecessors.add(predDl);
				}
			}
		}
		List<S> symbolsReturn = new ArrayList<S>(state.getInSymbolsReturn());
		for(S symbol : symbolsReturn) {
			List<IState<S,C>> linPreds = new ArrayList<IState<S,C>>(state.getInReturnLinear(symbol));
			for (IState<S,C> linPred : linPreds) {
				StateDl<S,C> linPredDl = (StateDl<S,C>) linPred;
				List<IState<S,C>> hieracPreds = new ArrayList<IState<S,C>>(stateDl.getInReturnHierarcForLinearPred(symbol,linPredDl));
				for (IState<S,C> hieracPred : hieracPreds) {
					StateDl<S, C> hieracPredDl = (StateDl<S,C>) hieracPred;
					boolean existed = hieracPredDl.delReturnTransition(symbol, linPred, state);
					assert(existed);
					if(hieracPredDl != state && isUseless(hieracPredDl)) {
						uselessPredecessors.add(hieracPredDl);
					}
				}
			}
		}

		//delete all return transitions that have state as linear predecessor
		//and are not already removed
		for(IState<S,C> scState : state.getSummaryCandidates()) {
			StateDl<S,C> scStateDl = (StateDl<S,C>) scState; 
			for (S symbol : stateDl.getSummaryCandidateSymbol(scStateDl)) {
				for (IState<S,C> hierarcPred : scStateDl.getInReturnHierarc(symbol)) {
					StateDl<S, C> hierarcPredDl = (StateDl<S,C>) hierarcPred;
					hierarcPredDl.delReturnTransition(symbol, state, scState);
				}
			}
		}
		
		for (S symbol : state.getSymbolsInternal()) {
			for (IState<S,C> succ : state.getInternalSucc(symbol)) {
				state.delInternalTransition(symbol, succ);
			}
		}
		
		for (S symbol : state.getSymbolsCall()) {
			for (IState<S,C> succ : state.getCallSucc(symbol)) {
				state.delCallTransition(symbol, succ);
			}
		}
		
		for (S symbol : state.getSymbolsReturn()) {
			for (IState<S,C> linPred : state.getReturnLinearPred(symbol)) {
				for (IState<S,C> succ : state.getReturnSucc(linPred, symbol)) {
					state.delReturnTransition(symbol, linPred, succ);
				}
			}
		}
		boolean existed = nwa.states.remove(state);
		assert (existed);
		return uselessPredecessors;
	}

	
	

	

	/**
	 * A state is useless if has no successors (other than itself) and is not
	 * accepting.
	 */
	boolean isUseless(StateDl<S,C> state) {
		if (state.isFinal()) {
			return false;
		}
		for (S symbol : state.getSymbolsInternal()) {
			for (IState<S, C> succ : state.getInternalSucc(symbol)) {
				if (succ != state) {
					return false;
				}
			}
		}
		for (S symbol : state.getSymbolsCall()) {
			for (IState<S, C> succ : state.getCallSucc(symbol)) {
				if (succ != state) {
					return false;
				}
			}
		}
		for (S symbol : state.getSymbolsReturn()) {
			for (IState<S, C> linPred : state.getReturnLinearPred(symbol)) {
				for (IState<S,C> succ : state.getReturnSucc(linPred, symbol)) {
					if (succ != state) {
						return false;
					}
				}
			}
		}
		return true;
	}

}
