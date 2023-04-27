package de.uni_freiburg.informatik.ultimate.automata.rabin;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <STATE>
 * @param <CRSF>
 */
public class Buchi2RabinOperation<LETTER, STATE, CRSF> extends GeneralOperation<LETTER, STATE, IStateFactory<STATE>> {

	private final IRabinAutomaton<LETTER, STATE> mConversionAutomaton;

	public Buchi2RabinOperation(final AutomataLibraryServices services, final CRSF factory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> automaton) {
		super(services);
		mConversionAutomaton = new Buchi2RabinAutomaton<>(automaton);

	}

	@Override
	public IRabinAutomaton<LETTER, STATE> getResult() {

		return mConversionAutomaton;
	}
}
