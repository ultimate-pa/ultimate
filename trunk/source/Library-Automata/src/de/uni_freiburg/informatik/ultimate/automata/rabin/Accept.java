package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

public class Accept<LETTER, STATE, CRSF extends IStateFactory<STATE>> extends GeneralOperation<LETTER, STATE, CRSF> {

	public Accept(final AutomataLibraryServices services, final IRabinAutomaton<LETTER, STATE> automaton,
			final List<LETTER> word) {
		super(services);
		// TODO Auto-generated constructor stub
	}

	@Override
	public Boolean getResult() {
		// TODO Auto-generated method stub
		return null;
	}

}
