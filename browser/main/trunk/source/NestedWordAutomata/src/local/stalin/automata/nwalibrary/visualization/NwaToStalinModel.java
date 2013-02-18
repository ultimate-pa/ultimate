package local.stalin.automata.nwalibrary.visualization;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

import org.apache.log4j.Logger;

import local.stalin.automata.Activator;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.NestedWordAutomaton;
import local.stalin.automata.nwalibrary.visualization.AutomatonTransition.Transition;
import local.stalin.core.api.StalinServices;
import local.stalin.model.INode;

public class NwaToStalinModel<S, C> {
	private static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	public INode getStalinModelOfNwa(NestedWordAutomaton<S, C> nwa) {
		INode graphroot = new AutomatonState("Sucessors of this node are the" +
					" initial states",false);	
		Collection<IState<S, C>> initialStates = nwa.getInitialStates();
		Map<IState<S, C>,AutomatonState> visited = 
			new HashMap<IState<S, C>,AutomatonState>();
		LinkedList<IState<S, C>> queue = 
			new LinkedList<IState<S, C>>(initialStates);
	
		// add all initial states to model - all are successors of the graphroot
		for (IState<S, C> state : initialStates) {
			AutomatonState vsn = 
				new AutomatonState(state.getContent(),state.isFinal());
			visited.put(state,vsn);
			new AutomatonTransition((AutomatonState) graphroot,
											Transition.INTERNAL,"", null, vsn);
		}
		
		while (!queue.isEmpty()) {
			IState<S, C> state = queue.removeFirst();
			AutomatonState vsn = visited.get(state);
			
			for( S symbol : nwa.getInternalAlphabet()) {
				for( IState<S, C> succState : state.getInternalSucc(symbol)) {
					AutomatonState succVSN;
					if (visited.containsKey(succState)) {
						succVSN = visited.get(succState);
					}
					else {
						succVSN = new AutomatonState(
									succState.getContent(),succState.isFinal());
						s_Logger.debug("Creating Node: " 
								+ succVSN.getPayload().getName());
						visited.put(succState,succVSN);
						queue.add(succState);
					}
					new AutomatonTransition(
								vsn,Transition.INTERNAL,symbol,null,succVSN);
				}
			}
			
			for( S symbol : nwa.getCallAlphabet()) {
				for( IState<S, C> succState : state.getCallSucc(symbol)) {
					AutomatonState succVSN;
					if (visited.containsKey(succState)) {
						succVSN = visited.get(succState);
					}
					else {
						succVSN = new AutomatonState(
									succState.getContent(),succState.isFinal());
						s_Logger.debug("Creating Node: " +
												succVSN.getPayload().getName());
						visited.put(succState,succVSN);
						queue.add(succState);
					}
					new AutomatonTransition(vsn,
										Transition.CALL,symbol,null,succVSN);
				}
			}

			for( S symbol : nwa.getReturnAlphabet()) {
				for(IState<S, C> linPredState : nwa.getAllStates()) {					
					for( IState<S, C> succState : 
									state.getReturnSucc(linPredState, symbol)) {
						AutomatonState succVSN;
						if (visited.containsKey(succState)) {
							succVSN = visited.get(succState);
						}
						else {
							succVSN = new AutomatonState(
									succState.getContent(),succState.isFinal());
							s_Logger.debug("Creating Node: " 
											+ succVSN.getPayload().getName());
							visited.put(succState,succVSN);
							queue.add(succState);
						}
						new AutomatonTransition(vsn,Transition.RETURN,symbol,
											linPredState.toString(),succVSN);
					}
				}
			}
			
		}
		return graphroot;
	}
	

}
