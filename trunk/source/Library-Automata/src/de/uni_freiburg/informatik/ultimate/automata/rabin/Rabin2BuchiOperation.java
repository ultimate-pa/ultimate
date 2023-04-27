package de.uni_freiburg.informatik.ultimate.automata.rabin;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * A GeneralOperation for conversion of a Rabin to a Buchi automaton
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 * @param <CRSF>
 *            state factory with IBlackWhiteState & IEmptyStackState functionality
 */
public class Rabin2BuchiOperation<LETTER, STATE, CRSF extends IBlackWhiteStateFactory<STATE> & IEmptyStackStateFactory<STATE>>
		extends GeneralOperation<LETTER, STATE, IStateFactory<STATE>> {

	private final Rabin2BuchiAutomaton<LETTER, STATE, CRSF> mConversionAutomaton;

	/**
	 * constructor finalizing a Rabin Automaton and State Factory for this conversion
	 *
	 * @param services
	 *            AutomataLibraryServices
	 * @param factory
	 *            state factory with IBlackWhiteState & IEmptyStackState functionality
	 * @param automaton
	 *            Rabin automaton
	 */

	public Rabin2BuchiOperation(final AutomataLibraryServices services, final CRSF factory,
			final IRabinAutomaton<LETTER, STATE> automaton) {
		super(services);
		mConversionAutomaton = new Rabin2BuchiAutomaton<>(automaton, factory);

	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getResult() {

		return mConversionAutomaton;
	}
}
