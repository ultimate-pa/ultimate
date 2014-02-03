/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetJulian;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.TestFileInterpreter.LoggerSeverity;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AlternatingAutomatonAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataDefinitionsAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.NestedwordAutomatonAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.PetriNetAutomatonAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.PetriNetTransitionAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.TransitionListAST.Pair;
import de.uni_freiburg.informatik.ultimate.result.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.result.GenericResult.Severity;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.AlternatingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetJulian;

/**
 * 
 * @author musab@informatik.uni-freiburg.de
 * 
 * Responsible for interpretation of automata definitions.
 *
 */
public class AutomataDefinitionInterpreter {
	
	/**
	 * A map from automaton name to automaton object, which contains for each automaton, that was defined in the automata
	 * definitions an entry. 
	 */
	private Map<String,Object> m_Automata;
	/**
	 * Contains the location of current interpreting automaton.
	 */
	private ILocation m_errorLocation;
	
	public AutomataDefinitionInterpreter() {
		m_Automata = new HashMap<String, Object>();
	}
	
	/**
	 * 
	 * @param automata the definitions of automata
	 */
	public void interpret(AutomataDefinitionsAST automata) {
		List<? extends AtsASTNode> children = automata.getListOfAutomataDefinitions();
		for (AtsASTNode n : children) {
			if (n instanceof NestedwordAutomatonAST) {
				try {
					interpret((NestedwordAutomatonAST) n);
				} catch (Exception e) {
					TestFileInterpreter.printMessage(Severity.ERROR, LoggerSeverity.DEBUG, e.getMessage() 
							+ System.getProperty("line.separator") + e.getStackTrace(),
							"Exception thrown", n);
				}

			} else if (n instanceof PetriNetAutomatonAST) {
				try {
					interpret((PetriNetAutomatonAST) n);
				} catch (Exception e) {
					TestFileInterpreter.printMessage(Severity.ERROR, LoggerSeverity.DEBUG, e.getMessage() 
							+ System.getProperty("line.separator") + e.getStackTrace(), 
							"Exception thrown", n);
				}
			}
			else if (n instanceof AlternatingAutomatonAST){
				try {
					interpret((AlternatingAutomatonAST) n);
				} catch (Exception e) {
					TestFileInterpreter.printMessage(Severity.ERROR, LoggerSeverity.DEBUG, e.getMessage() 
							+ System.getProperty("line.separator") + e.getStackTrace(), 
							"Exception thrown", n.getLocation());
				}
				
			}
		}
		
	}
	
	public void interpret(AlternatingAutomatonAST aa) throws IllegalArgumentException {
		m_errorLocation = aa.getLocation();
		Set<String> Alphabet = new HashSet<String>(aa.getAlphabet());
		
		AlternatingAutomaton<String, String> saa = new AlternatingAutomaton<String, String>(
				                                     Collections.unmodifiableSet(Alphabet), 
				                                     new StringFactory());
		
		/*
		 * Now add the states to the NestedWordAutomaton 
		 */
		List<String> initStates = aa.getInitialStates();
		List<String> finalStates = aa.getFinalStates();
//		List<String> exStates = aa.getExStates();
//		List<String> uniStates = aa.getUniStates();
		
		for (String state : aa.getExStates()) {
			if (initStates.contains(state)) {
				if (finalStates.contains(state)) {
					saa.addState(true, true, true, state);
				} else {
					saa.addState(true, false, true, state);
				}
			} else if (finalStates.contains(state)) {
				saa.addState(false, true, true, state);
			} else {
				saa.addState(false, false, true, state);
			}
		}
		
		for (String state : aa.getUniStates()) {
			if (initStates.contains(state)) {
				if (finalStates.contains(state)) {
					saa.addState(true, true, false, state);
				} else {
					saa.addState(true, false, false, state);
				}
			} else if (finalStates.contains(state)) {
				saa.addState(false, true, false, state);
			} else {
				saa.addState(false, false, false, state);
			}
		}
		
		
		/*
		 * Now add the transitions to the NestedWordAutomaton
		 */
		for (Entry<Pair<String, String>, Set<String>> entry : aa.getTransitions().entrySet()) {
			for (String succ : entry.getValue()) {
				saa.addTransition(entry.getKey().left, entry.getKey().right, succ);
			}
			
		}
		
		m_Automata.put(aa.getName(), saa);
		
	}

	
	public void interpret(NestedwordAutomatonAST nwa) throws IllegalArgumentException {
		m_errorLocation = nwa.getLocation();
		Set<String> internalAlphabet = new HashSet<String>(nwa.getInternalAlphabet());
		Set<String> callAlphabet = new HashSet<String>(nwa.getCallAlphabet());
		Set<String> returnAlphabet = new HashSet<String>(nwa.getReturnAlphabet());
		
		NestedWordAutomaton<String, String> nw = new NestedWordAutomaton<String, String>(
				                                     Collections.unmodifiableSet(internalAlphabet), 
				                                     Collections.unmodifiableSet(callAlphabet), 
				                                     Collections.unmodifiableSet(returnAlphabet), 
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
		
		for ( String linPred  : nwa.getReturnTransitions().keySet()) {
			for (String hierPred : nwa.getReturnTransitions().get(linPred).keySet()) {
				for (String letter : nwa.getReturnTransitions().get(linPred).get(hierPred).keySet()) {
					for (String succ : nwa.getReturnTransitions().get(linPred).get(hierPred).get(letter)) {
						nw.addReturnTransition(linPred, hierPred, letter, succ);
					}
				}
			}
		}
		m_Automata.put(nwa.getName(), nw);
		
	}
	
	public void interpret(PetriNetAutomatonAST pna) throws IllegalArgumentException {
		m_errorLocation = pna.getLocation();
		PetriNetJulian<String, String> net = new PetriNetJulian<String, String>(
				new HashSet<String>(pna.getAlphabet()), 
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
		for (PetriNetTransitionAST ptrans : pna.getTransitions()) {
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
