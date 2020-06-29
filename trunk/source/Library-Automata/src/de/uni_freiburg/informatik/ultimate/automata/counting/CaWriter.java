package de.uni_freiburg.informatik.ultimate.automata.counting;

import java.io.PrintWriter;
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
		printCollectionPrefix("callAlphabet");
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
	
	private void printInitialConditions() {
		printCollectionPrefix("initialConditions");
		for (STATE state : mCa.getStates()) {
			printOneTransitionPrefix();
			print(mStateMapping.get(state));
			print(' ');
			print('\"');
			//print(string representation of mCa.getInitialConditions().get(state))
			print('\"');
			printOneTransitionSuffix();
		}
		printCollectionSuffix();
	}
	
	private void printFinalConditions() {
		printCollectionPrefix("finalConditions");
		for (STATE state : mCa.getStates()) {
			printOneTransitionPrefix();
			print(mStateMapping.get(state));
			print(' ');
			print('\"');
			//print(string representation of mCa.getFinalConditions().get(state))
			print('\"');
			printOneTransitionSuffix();
		}
		printCollectionSuffix();
	}
	
	private void printTransitions() {
		printCollectionPrefix("transitions");
		for (STATE state : mCa.getStates()) {
			for (Transition<LETTER, STATE> transition : mCa.getTransitions().get(state)) {
				printOneTransitionPrefix();
				print(mStateMapping.get(state));
				print(' ');
				print(mAlphabetMapping.get(transition.getLetter()));
				print(' ');
				print('\"');
				//print(string representation of transition.getGuards());
				print('\"');
				print(' ');
				print('{');
				for (Update update : transition.getUpdates()) {
					print(' ');
					//print(string representation of update);
					if (transition.getUpdates().indexOf(transition) < (transition.getUpdates().size()-1)) {
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
