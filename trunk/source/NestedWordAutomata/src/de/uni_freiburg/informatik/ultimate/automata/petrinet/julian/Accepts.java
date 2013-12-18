package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

//package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import java.util.HashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class Accepts<S, C> implements IOperation<S, C> {
	
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
		
	@Override
	public String operationName() {
		return "acceptsJulian";
	}
	
	private PetriNetJulian<S, C> net;
	private Word<S> nWord;
	private Boolean m_Result;

	// private Collection<Place<S, C>> marking;
	// private int position;
	
	
	@Override
	public String startMessage() {
		return "Start " + operationName() +
			"Operand " + net.sizeInformation();
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName();
	}

	
	

	public Accepts(PetriNetJulian<S, C> net, Word<S> nWord) throws OperationCanceledException {
		this.net = net;
		this.nWord = nWord;
		s_Logger.info(startMessage());
		// this.marking = new HashSet<Place<S, C>>(net.getInitialMarking());
		// this.position = 0;
		m_Result = getResultHelper(0,net.getInitialMarking());
		s_Logger.info(exitMessage());
	}

	public Boolean getResult() throws OperationCanceledException {
		return m_Result;
	}

	private boolean getResultHelper(int position,
	        Marking<S, C> marking) throws OperationCanceledException {
		if (position >= nWord.length())
			return net.isAccepting(marking);
		
		
		if (!UltimateServices.getInstance().continueProcessing()) {
			throw new OperationCanceledException();
		}

		S symbol = nWord.getSymbol(position);
		if (!net.getAlphabet().contains(symbol)) {
			throw new IllegalArgumentException("Symbol "+symbol
					+" not in alphabet"); 
		}

		HashSet<ITransition<S, C>> activeTransitionsWithTheSymbol = 
											new HashSet<ITransition<S, C>>();

		// get all active transitions which are labeled with the next symbol
		for (Place<S, C> place : marking)
			for (ITransition<S, C> transition : place.getSuccessors())
				if (marking.isTransitionEnabled(transition)
				        && transition.getSymbol().equals(symbol))
					activeTransitionsWithTheSymbol.add(transition);
		// marking = new HashSet<Place<S,C>>();
		position++;
		boolean result = false;
		Marking<S, C> nextMarking;
		for (ITransition<S, C> transition : activeTransitionsWithTheSymbol) {
			nextMarking = marking.fireTransition(transition);
			if (getResultHelper(position, nextMarking))
				result = true;
		}
		return result;
	}

	@Override
	public boolean checkResult(StateFactory<C> stateFactory)
			throws OperationCanceledException {

		s_Logger.info("Testing correctness of accepts");

		NestedWord nw = NestedWord.nestedWord(nWord);
		boolean resultAutomata = (new de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Accepts(
				(new PetriNet2FiniteAutomaton(net)).getResult(), nw))
				.getResult();
		boolean correct = (m_Result == resultAutomata);

		s_Logger.info("Finished testing correctness of accepts");

		return correct;

	}


}
