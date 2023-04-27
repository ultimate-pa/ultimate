package de.uni_freiburg.informatik.ultimate.automata.rabin;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <STATE>
 * @param <CRSF>
 */
public class Rabin2BuchiTest<LETTER, STATE, CRSF extends IBlackWhiteStateFactory<STATE> & IEmptyStackStateFactory<STATE>>
		extends GeneralOperation<LETTER, STATE, IStateFactory<STATE>> {

	private final Rabin2BuchiAutomaton<LETTER, STATE, CRSF> mConversionAutomaton;

	@SuppressWarnings("unused")
	public Rabin2BuchiTest(final AutomataLibraryServices services, final CRSF factory,
			final IRabinAutomaton<LETTER, STATE> automaton) throws AutomataOperationCanceledException {
		super(services);
		mConversionAutomaton = new Rabin2BuchiAutomaton<>(automaton, factory);

	}

	@Override
	public Object getResult() {

		return mConversionAutomaton;
	}
}
