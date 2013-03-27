package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.visualization;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.visualization.AutomatonTransition.Transition;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.INode;

public class NwaToUltimateModel<LETTER,STATE> {
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	public IElement getUltimateModelOfNwa(INestedWordAutomaton<LETTER,STATE> nwa) {
		AutomatonState graphroot = new AutomatonState("Sucessors of this node are the" +
					" initial states",false);	
		Collection<STATE> initialStates = nwa.getInitialStates();
		Map<STATE,AutomatonState> visited = 
			new HashMap<STATE,AutomatonState>();
		LinkedList<STATE> queue = 
			new LinkedList<STATE>(initialStates);
	
		// add all initial states to model - all are successors of the graphroot
		for (STATE state : initialStates) {
			AutomatonState vsn = new AutomatonState(state,
									nwa.isFinal(state));
			visited.put(state,vsn);
			new AutomatonTransition((AutomatonState) graphroot,
											Transition.INTERNAL,"", null, vsn);
		}
		
		while (!queue.isEmpty()) {
			STATE state = queue.removeFirst();
			AutomatonState vsn = visited.get(state);
			
			for( LETTER symbol : nwa.lettersInternal(state)) {
				for( STATE succState : nwa.succInternal(state, symbol)) {
					AutomatonState succVSN;
					if (visited.containsKey(succState)) {
						succVSN = visited.get(succState);
					}
					else {
						succVSN = new AutomatonState(succState,
								nwa.isFinal(succState));
						s_Logger.debug("Creating Node: " 
								+ succVSN.getPayload().getName());
						visited.put(succState,succVSN);
						queue.add(succState);
					}
					new AutomatonTransition(
								vsn,Transition.INTERNAL,symbol,null,succVSN);
				}
			}
			
			for( LETTER symbol : nwa.lettersCall(state)) {
				for( STATE succState : nwa.succCall(state, symbol)) {
					AutomatonState succVSN;
					if (visited.containsKey(succState)) {
						succVSN = visited.get(succState);
					}
					else {
						succVSN = new AutomatonState(succState,
							nwa.isFinal(succState));
						s_Logger.debug("Creating Node: " +
												succVSN.getPayload().getName());
						visited.put(succState,succVSN);
						queue.add(succState);
					}
					new AutomatonTransition(vsn,
										Transition.CALL,symbol,null,succVSN);
				}
			}

			for( LETTER symbol : nwa.lettersReturn(state)) {
				for(STATE linPredState : nwa.getStates()) {					
					for( STATE succState : 
									nwa.succReturn(state, linPredState, symbol)) {
						AutomatonState succVSN;
						if (visited.containsKey(succState)) {
							succVSN = visited.get(succState);
						}
						else {
							succVSN = new AutomatonState(succState,
								nwa.isFinal(succState));
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
