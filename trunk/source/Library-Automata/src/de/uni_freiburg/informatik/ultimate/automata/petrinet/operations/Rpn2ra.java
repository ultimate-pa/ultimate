package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.rabin.IRabinAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;

/**
 * A {@link GeneralOperation} that encapsulates a Rabin automaton created through conversion of a Rabin-Petri-Net
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 *            type of letters
 * @param <STATE>
 *            type of states/places
 * @param <CRSF>
 *            A {@link IPetriNet2FiniteAutomatonStateFactory} and {@link IBlackWhiteStateFactory} that operates on
 *            states/places
 */
public class Rpn2ra<LETTER, STATE, CRSF extends IPetriNet2FiniteAutomatonStateFactory<STATE> & IBlackWhiteStateFactory<STATE>>
		extends GeneralOperation<LETTER, STATE, CRSF> {

	IRabinAutomaton<LETTER, STATE> mResult;

	/**
	 * Set a Rabin-Petri-Net that should be lazily converted to a Rabin automaton with a CRSF and services
	 *
	 * @param services
	 *            services
	 * @param factory
	 *            A {@link IPetriNet2FiniteAutomatonStateFactory} and {@link IBlackWhiteStateFactory} that operates on
	 *            states/places
	 * @param operand
	 *            A Rabin-Petri-Net that should be converted to the resulting Rabin automaton
	 */
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
