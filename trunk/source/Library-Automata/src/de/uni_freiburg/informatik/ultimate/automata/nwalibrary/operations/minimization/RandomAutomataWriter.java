package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.GetRandomDfa;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

public class RandomAutomataWriter<LETTER, STATE> implements
	IOperation<LETTER, STATE> {
	private int
		m_nOfAutomatas,
		m_nOfStates,
		m_sizeOfAlphabet;
	
	public RandomAutomataWriter(IUltimateServiceProvider services,
			int nOfAutomatas, int nOfStates, int sizeOfAlphabet) {
		m_nOfAutomatas = nOfAutomatas;
		m_nOfStates = nOfStates;
		m_sizeOfAlphabet = sizeOfAlphabet;
		this.createRandomAutomatas(services);
	}
	
	private void createRandomAutomatas(IUltimateServiceProvider services) {
		HashSet<NestedWordAutomaton<String, String>> automataSet =
				new HashSet<NestedWordAutomaton<String, String>>(m_nOfAutomatas);
		for (int i = 0; i < m_nOfAutomatas; ++i) {
			GetRandomDfa gRD = new GetRandomDfa(
				services, m_nOfStates, m_sizeOfAlphabet, 1, 50, true, false, false);
			NestedWordAutomaton<String, String> nwa = gRD.getResult();
			automataSet.add(nwa);
		}
		
		write(automataSet);
	}
	
	private void write(HashSet<NestedWordAutomaton<String, String>> nwaSet) {
		Iterator<NestedWordAutomaton<String, String>> it = nwaSet.iterator();
		int index = -1;
		while (it.hasNext()) {
			index++;
			NestedWordAutomaton<String, String> nwa = it.next();
			Collection<String> states = nwa.getStates();
			Set<String> alphabet = nwa.getInternalAlphabet();
			
			// For getting all transitions iterate over states and
			// get all incoming transitions.
			Iterator<String> statesIt = states.iterator();
			LinkedList<String> transitions = new LinkedList<String>();
			while (statesIt.hasNext()) {
				String state = statesIt.next();
				Set<String> incomingTransitions = nwa.lettersInternalIncoming(state);
				Iterator<String> inTransIt = incomingTransitions.iterator();
				while (inTransIt.hasNext()) {
					transitions.add(inTransIt.next());
				}
			}
			// Automaton is read. Write to file.
			String filename =
					"/home/bjoern/Uni/Bachelor_Arbeit/finiteAutomata/" +
					m_nOfStates + "_" + m_sizeOfAlphabet + "_" + index + ".ats";
			PrintWriter writer = null;
			try {
				writer = new PrintWriter(new File(filename));
			} catch (FileNotFoundException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			writer.println("NestedWordAutomaton wde = removeDeadEnds(automaton);");
			writer.println("NestedWordAutomaton result = MinimizeDfaSymbolic(wde);");
			writer.println();
			writer.println(nwa.toString());
			writer.flush();
			writer.close();
		}
	}
	
	@Override
	public String operationName() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String startMessage() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String exitMessage() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object getResult() throws OperationCanceledException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		// TODO Auto-generated method stub
		return false;
	}
}
