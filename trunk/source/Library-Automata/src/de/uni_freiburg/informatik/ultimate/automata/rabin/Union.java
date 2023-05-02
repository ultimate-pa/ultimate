package de.uni_freiburg.informatik.ultimate.automata.rabin;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * A GeneralOperation for a Union over two Rabin automata
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 *            type of letter
 * @param <STATE>
 *            type of state
 * @param <CRSF>
 *            a StateFactory implementing {@link IBlackWhiteStateFactory}
 */
public class Union<LETTER, STATE, CRSF extends IBlackWhiteStateFactory<STATE>>
		extends GeneralOperation<LETTER, STATE, IStateFactory<STATE>> {

	private final IRabinAutomaton<LETTER, STATE> mResult;
	private final IRabinAutomaton<LETTER, STATE> mFirst;
	private final IRabinAutomaton<LETTER, STATE> mSecond;

	/**
	 * Constructs a GeneralOperation for uniting two declared Rabin automata
	 *
	 * @param services
	 *            services
	 * @param factory
	 *            some IBlackWhiteStateFactory for STATE
	 * @param firstAutomaton
	 *            first Rabin automaton
	 * @param secondAutomaton
	 *            second Rabin automaton
	 */
	public Union(final AutomataLibraryServices services, final CRSF factory,
			final IRabinAutomaton<LETTER, STATE> firstAutomaton, final IRabinAutomaton<LETTER, STATE> secondAutomaton) {
		super(services);
		mResult = new RabinUnion<>(firstAutomaton, secondAutomaton, factory);
		mFirst = firstAutomaton;
		mSecond = secondAutomaton;
	}

	@Override
	public IRabinAutomaton<LETTER, STATE> getResult() {

		return mResult;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataOperationCanceledException {

		return (new IsEmpty<>(mServices, mResult).getResult() == (new IsEmpty<>(mServices, mFirst).getResult()
				|| new IsEmpty<>(mServices, mSecond).getResult()));
	}
}
