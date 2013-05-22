package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.visualization;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.visualization.AutomatonTransition.Transition;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.IElement;

public class NwaToUltimateModel<LETTER,STATE> {
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	public IElement getUltimateModelOfNwa(INestedWordAutomaton<LETTER,STATE> nwa) {
		AutomatonState graphroot = new AutomatonState("Sucessors of this node are the" +
					" initial states",false);	
		Map<STATE,AutomatonState> constructed =	new HashMap<STATE,AutomatonState>();
		LinkedList<STATE> queue = new LinkedList<STATE>();
	
		// add all initial states to model - all are successors of the graphroot
		for (STATE state : nwa.getInitialStates()) {
			queue.add(state);
			AutomatonState vsn = new AutomatonState(state,
									nwa.isFinal(state));
			constructed.put(state,vsn);
			new AutomatonTransition((AutomatonState) graphroot,
											Transition.INTERNAL,"", null, vsn);
		}
		
		while (!queue.isEmpty()) {
			STATE state = queue.removeFirst();
			AutomatonState vsn = constructed.get(state);
			
			for (OutgoingInternalTransition<LETTER, STATE> trans : 
												nwa.internalSuccessors(state)) {
				LETTER symbol = trans.getLetter();
				STATE succState = trans.getSucc();
				AutomatonState succVSN;
				if (constructed.containsKey(succState)) {
					succVSN = constructed.get(succState);
				}
				else {
					succVSN = new AutomatonState(succState,
							nwa.isFinal(succState));
					s_Logger.debug("Creating Node: " + succVSN.toString());
					constructed.put(succState,succVSN);
					queue.add(succState);
				}
				new AutomatonTransition(vsn,Transition.INTERNAL,symbol,null,succVSN);
			}
			
			for (OutgoingCallTransition<LETTER, STATE> trans : 
													nwa.callSuccessors(state)) {
				LETTER symbol = trans.getLetter();
				STATE succState = trans.getSucc();
				AutomatonState succVSN;
				if (constructed.containsKey(succState)) {
					succVSN = constructed.get(succState);
				} else {
					succVSN = new AutomatonState(succState,
							nwa.isFinal(succState));
					s_Logger.debug("Creating Node: " + succVSN.toString());
					constructed.put(succState, succVSN);
					queue.add(succState);
				}
				new AutomatonTransition(vsn, Transition.CALL, symbol, null,	succVSN);
			}
			for(STATE hierPredState : nwa.getStates()) {
				for (OutgoingReturnTransition<LETTER, STATE> trans : 
							nwa.returnSuccessorsGivenHier(hierPredState, state)) {
					LETTER symbol = trans.getLetter();
					STATE succState = trans.getSucc();
					AutomatonState succVSN;
					if (constructed.containsKey(succState)) {
						succVSN = constructed.get(succState);
					} else {
						succVSN = new AutomatonState(succState,nwa.isFinal(succState));
						s_Logger.debug("Creating Node: " + succVSN.toString());
						constructed.put(succState, succVSN);
						queue.add(succState);
					}
					new AutomatonTransition(vsn, Transition.RETURN, symbol,
							hierPredState.toString(), succVSN);
				}
			}
		}
		return graphroot;
	}
	

}
