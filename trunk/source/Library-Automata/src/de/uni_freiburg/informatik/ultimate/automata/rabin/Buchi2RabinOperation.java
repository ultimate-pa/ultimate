package de.uni_freiburg.informatik.ultimate.automata.rabin;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Converts a Buchi automaton to a Rabin automaton via {@link Buchi2RabinAutomaton} as a General Operation
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 *            type of letter
 * @param <STATE>
 *            type of state
 */
public class Buchi2RabinOperation<LETTER, STATE> extends GeneralOperation<LETTER, STATE, IStateFactory<STATE>> {

	private final IRabinAutomaton<LETTER, STATE> mConversionAutomaton;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mBuchiAutomaton;

	/**
	 * Converts a Buchi automaton to a Rabin automaton via {@link Buchi2RabinAutomaton}, this constructs a General
	 * Operation
	 *
	 * @param services
	 *            services
	 * @param automaton
	 *            Buchi automaton
	 */
	public Buchi2RabinOperation(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> automaton) {
		super(services);
		mConversionAutomaton = new Buchi2RabinAutomaton<>(automaton);
		mBuchiAutomaton = automaton;

	}

	@Override
	public IRabinAutomaton<LETTER, STATE> getResult() {

		return mConversionAutomaton;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataOperationCanceledException {

		return (new IsEmpty<>(mServices, mConversionAutomaton)
				.getResult() == new BuchiIsEmpty<>(mServices, mBuchiAutomaton).getResult());
	}
}
