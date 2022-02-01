package de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization;

import java.io.PrintWriter;
import java.util.Collection;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.GeneralAutomatonPrinter;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;

public abstract class BranchingProcessWriter<LETTER, STATE> extends GeneralAutomatonPrinter
{
	private final Map<LETTER, String> mAlphabet;
	private final Map<Condition<LETTER, STATE>, String> mConditionsMapping;
	public BranchingProcessWriter(final PrintWriter writer,
		final String name, final BranchingProcess<LETTER, STATE> branchingProcess) {
		super(writer);
		mAlphabet = getAlphabetMapping(branchingProcess.getAlphabet());
		mConditionsMapping = getConditionsMapping(branchingProcess.getConditions());
		print("Branching Process ");
		print(name);
		printAutomatonPrefix();
		printAlphabet();
		printConditions();
		printEvents(branchingProcess);
		printInitialConditions(branchingProcess.initialConditions());
		printAutomatonSuffix();
		finish();
	}
	protected abstract Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet);
	protected abstract Map<Condition<LETTER, STATE>, String> getConditionsMapping(final Collection<Condition<LETTER, STATE>> places);
	
	protected final void printElementPrefix(final String string) {
		print(String.format("\t%s = ", string));
	}

	private void printAlphabet() {
		printCollectionPrefix("alphabet");
		printValues(mAlphabet);
		printCollectionSuffix();
	}
	
	private void printConditions() {
		printCollectionPrefix("conditions");
		printValues(mConditionsMapping);
		printCollectionSuffix();
	}
	
	private void printEvents(final BranchingProcess<LETTER, STATE> branchingProcess) {
		printlnCollectionPrefix("events");
		for (final Event<LETTER, STATE> Event : branchingProcess.getEvents()) {
			printEvent(Event);
		}
		printTransitionsSuffix();
		print(',');
		print(NEW_LINE);
	}
	
	private void printEvent(final Event<LETTER, STATE> event) {
		//we don't want to print the dummy event
		if ( event.getTransition() != null)
		{
			printOneTransitionPrefix();
			printMarking(event.getPredecessorConditions());
			print(' ');
			print(mAlphabet.get(event.getTransition().getSymbol()));
			print(' ');
			printMarking(event.getSuccessorConditions());
			printOneTransitionSuffix();
		}
	}
	
	private void printMarking(final Collection<Condition<LETTER,STATE>> marking) {
		print('{');
		for (final Condition<LETTER, STATE> place : marking) {
			printElement(mConditionsMapping.get(place));
		}
		print('}');
	}
	
	private void printInitialConditions(final Collection<Condition<LETTER, STATE>> initialConditions) {
		printElementPrefix("initial conditions");
		printMarking(initialConditions);
		println(',');
	}

	
}

	

