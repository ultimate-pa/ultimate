package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.rabin.IRabinAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;

public class Rpn2ra<LETTER, STATE, CRSF extends IPetriNet2FiniteAutomatonStateFactory<STATE> & IBlackWhiteStateFactory<STATE>>
		extends GeneralOperation<LETTER, STATE, CRSF> {

	IRabinAutomaton<LETTER, STATE> mResult;

	public Rpn2ra(final AutomataLibraryServices services, final CRSF factory,
			final IRabinPetriNet<LETTER, STATE> operand) {
		super(services);
		mResult = new RabinPetriNet2RabinAutomaton<>(operand, factory);
	}

	@Override
	public IRabinAutomaton<LETTER, STATE> getResult() {

		return mResult;
	}

}
