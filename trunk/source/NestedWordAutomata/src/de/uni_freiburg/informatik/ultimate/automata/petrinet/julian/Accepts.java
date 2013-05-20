package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

//package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

import org.apache.log4j.Logger;

public class Accepts<S, C> implements IOperation {
	
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
		assert (ResultChecker.accepts(net, nWord, m_Result));
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


}
