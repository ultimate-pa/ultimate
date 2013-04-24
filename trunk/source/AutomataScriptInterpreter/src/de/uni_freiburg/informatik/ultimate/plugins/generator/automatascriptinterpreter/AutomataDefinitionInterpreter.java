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
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.TestFileInterpreter.LoggerSeverity;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.NestedwordAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.PetriNetAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.PetriNetTransition;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.TransitionList.Pair;
import de.uni_freiburg.informatik.ultimate.result.GenericResult.Severity;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetJulian;

import java.util.Collections;

/**
 * 
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class AutomataDefinitionInterpreter {
	
	
	Map<String,Object> m_Automata;
	ILocation m_errorLocation;
	
	public AutomataDefinitionInterpreter() {
		m_Automata = new HashMap<String, Object>();
	}
	
	/**
	 * 
	 * @param automata the definitions of automata
	 * @return null in all cases
	 */
	public void interpret(AutomataDefinitions automata) {
		List<? extends AtsASTNode> children = automata.getListOfAutomataDefinitions();
		for (AtsASTNode n : children) {
			if (n instanceof NestedwordAutomaton) {
				try {
					interpret((NestedwordAutomaton) n);
				} catch (Exception e) {
					TestFileInterpreter.printMessage(Severity.ERROR, LoggerSeverity.DEBUG, e.getMessage() 
							+ System.getProperty("line.separator") + e.getStackTrace(),
							"Exception thrown", n.getLocation());
				}

			} else if (n instanceof PetriNetAutomaton) {
				try {
					interpret((PetriNetAutomaton) n);
				} catch (Exception e) {
					TestFileInterpreter.printMessage(Severity.ERROR, LoggerSeverity.DEBUG, e.getMessage() 
							+ System.getProperty("line.separator") + e.getStackTrace(), 
							"Exception thrown", n.getLocation());
				}
			}
		}
		
	}
	
	public void interpret(NestedwordAutomaton nwa) throws IllegalArgumentException {
		m_errorLocation = nwa.getLocation();
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
		for (Entry<Pair<String, String>, Set<String>> entry : nwa.getInternalTransitions().entrySet()) {
			for (String succ : entry.getValue()) {
				nw.addInternalTransition(entry.getKey().left, entry.getKey().right, succ);
			}
			
		}
		
		for (Entry<Pair<String, String>, Set<String>> entry : nwa.getCallTransitions().entrySet()) {
			for (String succ : entry.getValue()) { 
				nw.addCallTransition(entry.getKey().left, entry.getKey().right, succ);
			}
		}
		
		for (Entry<Pair<String, String>, Pair<String, Set<String>>> entry : nwa.getReturnTransitions().entrySet()) {
			for (String succ : entry.getValue().right) {
				nw.addReturnTransition(entry.getKey().left, entry.getKey().right, entry.getValue().left, succ);
			}
			
		}
		m_Automata.put(nwa.getName(), nw);
		
	}
	
	public void interpret(PetriNetAutomaton pna) throws IllegalArgumentException {
		m_errorLocation = pna.getLocation();
		PetriNetJulian<String, String> net = new PetriNetJulian<String, String>(
				pna.getAlphabet(), 
				new StringFactory(), false);
		Map<String, Place<String, String>> name2places = new HashMap<String, Place<String, String>>();
		// Add the places
		for (String p : pna.getPlaces()) {
			Place<String, String> place = net.addPlace(p, 
					pna.getInitialMarkings().containsPlace(p), 
					pna.getAcceptingPlaces().contains(p));
			name2places.put(p, place);
		}


		// Add the transitions
		for (PetriNetTransition ptrans : pna.getTransitions()) {
			Collection<Place<String,String>> preds = new ArrayList<Place<String,String>>();
			Collection<Place<String,String>> succs = new ArrayList<Place<String,String>>();
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
					succs.add(name2places.get(succ));
				}
			}
			net.addTransition(ptrans.getSymbol(), preds, succs);
		}

		m_Automata.put(pna.getName(), net);
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

	
	public ILocation getErrorLocation() {
		return m_errorLocation;
	}
	
}
