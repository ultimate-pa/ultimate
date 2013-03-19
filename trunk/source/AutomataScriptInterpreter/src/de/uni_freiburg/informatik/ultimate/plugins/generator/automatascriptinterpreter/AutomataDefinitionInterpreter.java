/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.NestedwordAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.PetriNetAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.PetriNetTransition;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.TransitionList.Pair;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetJulian;

import java.util.Collections;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class AutomataDefinitionInterpreter {
	
	
	Map<String,Object> m_Automata;
	
	public AutomataDefinitionInterpreter() {
		m_Automata = new HashMap<String, Object>();
	}
	
	public <T> Object interpret(AutomataDefinitions automata) throws Exception {
		List<? extends AtsASTNode> children = automata.getAutomataDefinitions();
		for (AtsASTNode n : children) {
			if (n instanceof NestedwordAutomaton) {
				interpret((NestedwordAutomaton) n);
			} else if (n instanceof PetriNetAutomaton) {
				interpret((PetriNetAutomaton) n);
			}
		}
		return null;
		
	}
	
	public <T> Object interpret(NestedwordAutomaton nwa) throws IllegalArgumentException {
		
		NestedWordAutomaton<String, String> nw = new NestedWordAutomaton<String, String>(
				                                     Collections.unmodifiableCollection(nwa.getInternalAlphabet()), 
				                                     Collections.unmodifiableCollection(nwa.getCallAlphabet()), 
				                                     Collections.unmodifiableCollection(nwa.getReturnAlphabet()), 
				                                     new StringFactory());
		
		/*
		 * Now add the states to the NestedWordAutomaton 
		 */
		List<String> initStates = nwa.getInitialStates();
		List<String> finalStates = nwa.getFinalStates();
		for (String state : nwa.getStates()) {
			if (initStates.contains(state)) {
				if (finalStates.contains(state)) {
					nw.addState(true, true, state);
				} else {
					nw.addState(true, false, state);
				}
			} else if (finalStates.contains(state)) {
				nw.addState(false, true, state);
			} else {
				nw.addState(false, false, state);
			}
		}
		
		
		/*
		 * Now add the transitions to the NestedWordAutomaton
		 */
		for (Entry<Pair<String, String>, String> entry : nwa.getInternalTransitions().entrySet()) {
			nw.addInternalTransition(entry.getKey().left, entry.getKey().right, entry.getValue());
		}
		
		for (Entry<Pair<String, String>, String> entry : nwa.getCallTransitions().entrySet()) {
			nw.addInternalTransition(entry.getKey().left, entry.getKey().right, entry.getValue());
		}
		
		for (Entry<Pair<String, String>, Pair<String, String>> entry : nwa.getReturnTransitions().entrySet()) {
			nw.addReturnTransition(entry.getKey().left, entry.getKey().right, entry.getValue().left, entry.getValue().right);
		}
		
		
		m_Automata.put(nwa.getName(), nw);
		
		return null;
		
	}
	
	public <T> Object interpret(PetriNetAutomaton pna) throws IllegalArgumentException {
		if (pna.isPetriNetJulianDefinition()) {
			PetriNetJulian<String, String> net = new PetriNetJulian<String, String>(
												Collections.unmodifiableCollection(pna.getAlphabet()), 
												new StringFactory(), false);
			Map<String, Place<String, String>> name2places = new HashMap<String, Place<String, String>>();
			// Add the places
			for (String p : pna.getPlaces()) {
				Place<String, String> place = net.addPlace(p, pna.getInitialMarkings().containsPlace(p), pna.getAcceptingPlaces().contains(p));
				name2places.put(p, place);
			}
			
			Collection<Place<String,String>> preds = new ArrayList<Place<String,String>>();
			Collection<Place<String,String>> succs = new ArrayList<Place<String,String>>();
			// Add the transitions
			for (PetriNetTransition ptrans : pna.getTransitions()) {
				preds.clear();
				succs.clear();
				for (String pred : ptrans.getPreds()) {
					if (!name2places.containsKey(pred)) {
						throw new IllegalArgumentException("undefined place:" + pred);
					} else {
						preds.add(name2places.get(pred));
					}
				}
				for (String succ : ptrans.getSuccs()) {
					if (!name2places.containsKey(succ)) {
						throw new IllegalArgumentException("undefined place:" + succ);
					} else {
						preds.add(name2places.get(succ));
					}
				}
				net.addTransition(ptrans.getSymbol(), preds, succs);
			}
			
			m_Automata.put(pna.getName(), net);
		}
		
		return null;
	}
	
	public Map<String, Object> getAutomata() {
		return m_Automata;
	}

	@Override
	public String toString() {
		StringBuilder builder = new StringBuilder();
		builder.append("AutomataDefinitionInterpreter [");
		if (m_Automata != null) {
			builder.append("#AutomataDefinitions: ");
			builder.append(m_Automata.size());
		}
		builder.append("]");
		return builder.toString();
	}
	
	
	
	

}
