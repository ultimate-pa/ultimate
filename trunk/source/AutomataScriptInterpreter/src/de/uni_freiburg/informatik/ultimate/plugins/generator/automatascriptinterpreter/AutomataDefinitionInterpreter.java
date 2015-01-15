/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating.AlternatingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating.BooleanExpression;
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
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

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
	private Map<String,Object> mAutomata;
	/**
	 * Contains the location of current interpreting automaton.
	 */
	private ILocation mErrorLocation;
	private IMessagePrinter mMessagePrinter;
	private final Logger mLogger;
	private final IUltimateServiceProvider mServices;
	
	public AutomataDefinitionInterpreter(IMessagePrinter printer, Logger logger, IUltimateServiceProvider services) {
		mAutomata = new HashMap<String, Object>();
		mMessagePrinter = printer;
		mLogger = logger;
		mServices = services;
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
					mMessagePrinter.printMessage(Severity.ERROR, LoggerSeverity.DEBUG, e.getMessage() 
							+ System.getProperty("line.separator") + e.getStackTrace(),
							"Exception thrown", n);
				}

			} else if (n instanceof PetriNetAutomatonAST) {
				try {
					interpret((PetriNetAutomatonAST) n);
				} catch (Exception e) {
					mMessagePrinter.printMessage(Severity.ERROR, LoggerSeverity.DEBUG, e.getMessage() 
							+ System.getProperty("line.separator") + e.getStackTrace(), 
							"Exception thrown", n);
				}
			}
			else if (n instanceof AlternatingAutomatonAST){
				try {
					interpret((AlternatingAutomatonAST) n);
				} catch (Exception e) {
//					mMessagePrinter.printMessage(Severity.ERROR, LoggerSeverity.DEBUG, e.getMessage() 
//							+ System.getProperty("line.separator") + e.getStackTrace(), 
//							"Exception thrown", n.getLocation());
				}
				
			}
		}
		
	}
	
	public void interpret(AlternatingAutomatonAST astNode) throws IllegalArgumentException{
		mErrorLocation = astNode.getLocation();

		HashSet<String> alphabet = new HashSet<String>(astNode.getAlphabet());
		AlternatingAutomaton<String, String> alternatingAutomaton = new AlternatingAutomaton<String, String>(alphabet, new StringFactory());
		
		List<String> states = astNode.getStates();
		List<String> finalStates = astNode.getFinalStates();
		for(String state : states){
			alternatingAutomaton.addState(state);
			if(finalStates.contains(state)){
				alternatingAutomaton.setStateFinal(state);
			}
		}

		for(Entry<Pair<String, String>, Set<String>> entry : astNode.getTransitions().entrySet()){
			String expression = entry.getValue().iterator().next();
			LinkedList<BooleanExpression> booleanExpressions = parseBooleanExpressions(alternatingAutomaton, expression);
			for(BooleanExpression booleanExpression : booleanExpressions){
				alternatingAutomaton.addTransition(entry.getKey().right, entry.getKey().left, booleanExpression);
			}
		}
		
		LinkedList<BooleanExpression> acceptingBooleanExpressions = parseBooleanExpressions(alternatingAutomaton, astNode.getAcceptingFunction());
		for(BooleanExpression booleanExpression : acceptingBooleanExpressions){
			alternatingAutomaton.addAcceptingConjunction(booleanExpression);
		}	
		
		mAutomata.put(astNode.getName(), alternatingAutomaton);
	}
	
	private static LinkedList<BooleanExpression> parseBooleanExpressions(AlternatingAutomaton<String, String> alternatingAutomaton, String expression){
		LinkedList<BooleanExpression> booleanExpressions = new LinkedList<BooleanExpression>();
		if(expression.equals("true")){
			booleanExpressions.add(new BooleanExpression(0, 0));
		}
		else if(expression.equals("false")){
			//Not supported yet
		}
		else{
			String[] disjunctiveExpressions = expression.split("\\|");
			for(String disjunctiveExpression : disjunctiveExpressions){
				String[] stateExpressions = disjunctiveExpression.split("&");
				LinkedList<String> resultStates = new LinkedList<String>();
				LinkedList<String> negatedResultStates = new LinkedList<String>();
				for(String stateExpression : stateExpressions){
					if(stateExpression.startsWith("~")){
						negatedResultStates.add(stateExpression.substring(1));
					}
					else{
						resultStates.add(stateExpression);
					}
				}
				BooleanExpression booleanExpression = alternatingAutomaton.generateDisjunction(resultStates.toArray(new String[resultStates.size()]), negatedResultStates.toArray(new String[negatedResultStates.size()]));
				booleanExpressions.add(booleanExpression);
			}
		}
		return booleanExpressions;
	}
	
	public void interpret(NestedwordAutomatonAST nwa) throws IllegalArgumentException {
		mErrorLocation = nwa.getLocation();
		Set<String> internalAlphabet = new HashSet<String>(nwa.getInternalAlphabet());
		Set<String> callAlphabet = new HashSet<String>(nwa.getCallAlphabet());
		Set<String> returnAlphabet = new HashSet<String>(nwa.getReturnAlphabet());
		
		NestedWordAutomaton<String, String> nw = new NestedWordAutomaton<String, String>(
				mServices,
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
		mAutomata.put(nwa.getName(), nw);
		
	}
	
	public void interpret(PetriNetAutomatonAST pna) throws IllegalArgumentException {
		mErrorLocation = pna.getLocation();
		PetriNetJulian<String, String> net = new PetriNetJulian<String, String>(
				mServices,
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

		mAutomata.put(pna.getName(), net);
	}
	
	public Map<String, Object> getAutomata() {
		return mAutomata;
	}

	@Override
	public String toString() {
		StringBuilder builder = new StringBuilder();
		builder.append("AutomataDefinitionInterpreter [");
		if (mAutomata != null) {
			builder.append("#AutomataDefinitions: ");
			builder.append(mAutomata.size());
		}
		builder.append("]");
		return builder.toString();
	}

	
	public ILocation getErrorLocation() {
		return mErrorLocation;
	}
	
}
