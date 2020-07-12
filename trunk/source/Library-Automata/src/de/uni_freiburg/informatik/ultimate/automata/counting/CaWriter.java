package de.uni_freiburg.informatik.ultimate.automata.counting;

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.GeneralAutomatonPrinter;

/**
 * Prints a Counting Automaton
 *
 * @author Marcel Ebbinghaus
 */

public class CaWriter<LETTER, STATE> extends GeneralAutomatonPrinter {
	
	private final CountingAutomaton<LETTER, STATE> mCa;
	private final Map<STATE, String> mStateMapping;
	private final Map<LETTER, String> mAlphabetMapping;
	
	public CaWriter(final PrintWriter writer, final String name, final CountingAutomaton<LETTER, STATE> ca) {
		super(writer);
		mCa = ca;
		mStateMapping = getStateMapping(mCa.getStates());
		mAlphabetMapping = getAlphabetMapping(mCa.getAlphabet());
		
		print("CountingAutomaton ");
		print(name);
		printAutomatonPrefix();
		printAlphabet();
		printCounter();
		printStates();
		printInitialConditions();
		printFinalConditions();
		printTransitions();
		printLastTransitionLineSeparator();
		printAutomatonSuffix();
		
		finish();
	}
	
	protected Map<STATE, String> getStateMapping(final Collection<STATE> states) {
		final Map<STATE, String> stateMapping = new HashMap<>();
		for (final STATE state : states) {
			stateMapping.put(state, quoteAndReplaceBackslashes(state));
		}
		return stateMapping;
	}
	
	protected Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet) {
		final Map<LETTER, String> alphabetMapping = new HashMap<>();
		for (final LETTER letter : alphabet) {
			alphabetMapping.put(letter, quoteAndReplaceBackslashes(letter));
		}
		return alphabetMapping;
	}
	
	private void printAlphabet() {
		printCollectionPrefix("alphabet");
		printValues(mAlphabetMapping);
		printCollectionSuffix();
	}
	
	private void printCounter() {
		printCollectionPrefix("counter");
		for (Counter counter : mCa.getCounter()) {
			printElement(counter.getCounterName());
		}
		printCollectionSuffix();
	}
	
	private void printStates() {
		printCollectionPrefix("states");
		printValues(mStateMapping);
		printCollectionSuffix();
	}
	
	private void printGuard(Guard guard) {
		switch(guard.getTermType()) {
		
		case TRUE:
			print("true");
			break;
			
		case FALSE:
			print("false");
			break;
			
		case CONSTANT:
			print('(');
			print(guard.getRelationSymbol().toString());
			print(' ');
			print(guard.getCounterLeft().getCounterName());
			print(' ');
			print(guard.getConstant().toString());
			print(')');
			break;
			
		case COUNTER:
			print('(');
			print(guard.getRelationSymbol().toString());
			print(' ');
			print(guard.getCounterLeft().getCounterName());
			print(' ');
			print(guard.getCounterRight().getCounterName());
			print(')');
			break;
			
		case SUM:
			print('(');
			print(guard.getRelationSymbol().toString());
			print(' ');
			print(guard.getCounterLeft().getCounterName());
			print(" (+ ");
			print(guard.getCounterRight().getCounterName());
			print(' ');
			print(guard.getConstant().toString());
			print("))");
			break;
		}
	}
	
	private void printSublist(ArrayList<Guard> sublist) {
		if (sublist.size() > 1) {
			print(" (and");
			for (Guard guard : sublist) {
				print(' ');
				printGuard(guard);
			}
			print(')');
		}
		else {
			for (Guard guard : sublist) {
				print(' ');
				printGuard(guard);
			}
		}
	}
	
	private void printInitialConditions() {
		printCollectionPrefix("initialConditions");
		print('\n');
		for (STATE state : mCa.getStates()) {
			printOneTransitionPrefix();
			print(mStateMapping.get(state));
			print(' ');
			print('\"');
			ArrayList<ArrayList<Guard>> conditionList = mCa.getInitialConditions().get(state).getCondition();
			if (conditionList.size() > 1) {
				print("(or");
				for (ArrayList<Guard> sublist : conditionList) {
					printSublist(sublist);
				}
				print(')');
			}
			else {
				for (ArrayList<Guard> sublist : conditionList) {
					printSublist(sublist);
				}
			}
			print('\"');
			printOneTransitionSuffix();
		}
		printCollectionSuffix();
	}
	
	private void printFinalConditions() {
		printCollectionPrefix("finalConditions");
		print('\n');
		for (STATE state : mCa.getStates()) {
			printOneTransitionPrefix();
			print(mStateMapping.get(state));
			print(' ');
			print('\"');
			ArrayList<ArrayList<Guard>> conditionList = mCa.getFinalConditions().get(state).getCondition();
			if (conditionList.size() > 1) {
				print("(or");
				for (ArrayList<Guard> sublist : conditionList) {
					printSublist(sublist);
				}
				print(')');
			}
			else {
				for (ArrayList<Guard> sublist : conditionList) {
					printSublist(sublist);
				}
			}
			print('\"');
			printOneTransitionSuffix();
		}
		printCollectionSuffix();
	}
	
	private void printTransitions() {
		printCollectionPrefix("transitions");
		print('\n');
		for (STATE state : mCa.getStates()) {
			for (Transition<LETTER, STATE> transition : mCa.getTransitions().get(state)) {
				printOneTransitionPrefix();
				print(mStateMapping.get(state));
				print(' ');
				print(mAlphabetMapping.get(transition.getLetter()));
				print(' ');
				print('\"');
				ArrayList<ArrayList<Guard>> conditionList = transition.getGuards();
				if (conditionList.size() > 1) {
					print("(or");
					for (ArrayList<Guard> sublist : conditionList) {
						printSublist(sublist);
					}
					print(')');
				}
				else {
					for (ArrayList<Guard> sublist : conditionList) {
						printSublist(sublist);
					}
				}
				print('\"');
				print(' ');
				print('{');
				for (Update update : transition.getUpdates()) {
					print(' ');
					
					switch(update.getTermType()) {
					
					case TRUE:
						print("true");
						break;
						
					case FALSE:
						print("false");
						break;
						
					case CONSTANT:
						print(update.getCounterLeft().getCounterName());
						print(" := \"");
						print(update.getConstant().toString());
						print('\"');
						break;
						
					case COUNTER:
						print(update.getCounterLeft().getCounterName());
						print(" := \"");
						print(update.getCounterRight().getCounterName());
						print('\"');
						break;
						
					case SUM:
						print(update.getCounterLeft().getCounterName());
						print(" := \"");
						print("(+ ");
						print(update.getCounterRight().getCounterName());
						print(' ');
						print(update.getConstant().toString());
						print(")\"");
						break;
					}
					
					if (transition.getUpdates().indexOf(update) < (transition.getUpdates().size()-1)) {
						print(',');
					}
				}
				print(' ');
				print('}');
				print(' ');
				print(mStateMapping.get(transition.getSucState()));
				printOneTransitionSuffix();
			}	
		}
		printTransitionsSuffix();
	}
}
