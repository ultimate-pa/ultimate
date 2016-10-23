package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.GetRandomNwaTv;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveDeadEnds;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Test class to produce benchmark results.
 * <p>
 * Constructs random nested word automata.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public final class ConstructRandomAutomata implements IOperation<String, String> {
	private static final int NUMBER_OF_SAMPLES = 100;
	private static final String AUTOMATON_NAME_PREFIX = "Random";
	
	public ConstructRandomAutomata(final AutomataLibraryServices services) {
		for (int i = 0; i < NUMBER_OF_SAMPLES; ++i) {
			final INestedWordAutomaton<String, String> random =
					new GetRandomNwaTv(services, 50, 2, 2, 2, 100, 100, 100, 50, 50).getResult();
			INestedWordAutomaton<String, String> nwa;
			try {
				nwa = new RemoveDeadEnds(services, random).getResult();
			} catch (final AutomataOperationCanceledException e) {
				e.printStackTrace();
				continue;
			}
			final String fileName = AUTOMATON_NAME_PREFIX + i;
			AutomatonDefinitionPrinter.writeToFileIfPreferred(services, fileName, "random automaton dump", nwa);
		}
	}
	
	@Override
	public String operationName() {
		return null;
	}
	
	@Override
	public String startMessage() {
		return null;
	}
	
	@Override
	public String exitMessage() {
		return null;
	}
	
	@Override
	public Object getResult() {
		return null;
	}
	
	@Override
	public boolean checkResult(final IStateFactory<String> stateFactory) throws AutomataLibraryException {
		return true;
	}
}
