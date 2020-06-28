package de.uni_freiburg.informatik.ultimate.automata.counting;

import java.io.PrintWriter;

import de.uni_freiburg.informatik.ultimate.automata.GeneralAutomatonPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;

/**
 * Prints a Counting Automaton
 *
 * @author Marcel Ebbinghaus
 */

public class CaWriter<LETTER, STATE> extends GeneralAutomatonPrinter {
	
	private final CountingAutomaton<LETTER, STATE> mCa;
	
	public CaWriter(final PrintWriter writer, final String name, final CountingAutomaton<LETTER, STATE> ca) {
		super(writer);
		mCa = ca;
		
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
	
	private void printAlphabet() {
		printCollectionPrefix("alphabet");
		for (LETTER letter : mCa.getAlphabet()) {
			//printElement(string representation of letter)	
		}
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
		for (STATE state : mCa.getStates()) {
			//printElement(string representation of state)	
		}
		printCollectionSuffix();
	}
	
	private void printInitialConditions() {
		printCollectionPrefix("initialConditions");
		for (STATE state : mCa.getStates()) {
			printOneTransitionPrefix();
			//print(string representation of state)
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
			//print(string representation of state)
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
				//print(string representation of state)
				print(' ');
				//print(string representation of transition.getLetter());
				print(' ');
				print('\"');
				//print(string representation of transition.getGuards());
				print('\"');
				print(' ');
				print('{');
				for (Update update : transition.getUpdates()) {
					print("\t[");
					//print(string representation of update);
					print(']');
				}
				print("\t}");
				print(' ');
				//print(string representation of transition.getSucStates());
				printOneTransitionSuffix();
			}	
		}
		printCollectionSuffix();
	}
}
