package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;

/**
 * Operation that returns the number of transitions of a petri net.
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class NumberOfTransitions<LETTER, STATE> implements IOperation<LETTER,STATE> {
	
	IPetriNet<LETTER, STATE> m_Net;
	
	public NumberOfTransitions(IPetriNet<LETTER, STATE> nwa) {
		m_Net = nwa;
	}

	@Override
	public String operationName() {
		return "numberOfPlaces";
	}

	@Override
	public String startMessage() {
		throw new UnsupportedOperationException();
	}

	@Override
	public String exitMessage() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Integer getResult() throws OperationCanceledException {
		return m_Net.getTransitions().size();
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		return true;
	}

}
