package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

public class IsEmpty<LETTER, STATE, CRSF extends IStateFactory<STATE>> extends GeneralOperation<LETTER, STATE, CRSF> {

	private final Boolean mResult;
	private final EagerRabinAutomaton<LETTER, STATE> eagerAutomaton;
	private final Set<STATE> evidence;

	final AutomatonSccComputation<LETTER, STATE> acceptingSccComputation;

	public IsEmpty(final AutomataLibraryServices services, final IRabinAutomaton<LETTER, STATE> automaton) {
		super(services);

		if (EagerRabinAutomaton.class == automaton.getClass()) {
			eagerAutomaton = (EagerRabinAutomaton<LETTER, STATE>) automaton;
		} else {
			eagerAutomaton = new EagerRabinAutomaton<>(automaton);
			// Reduces the automaton to its traversable core
		}

		acceptingSccComputation =
				new AutomatonSccComputation<>(services, eagerAutomaton.getStemlessNonFiniteAutomaton());

		mResult = acceptingSccComputation.getBalls().isEmpty();
		if (!mResult) {
			evidence = acceptingSccComputation.getExampleBall();
		} else {
			evidence = new HashSet<>();
		}

	}

	@Override
	public Boolean getResult() {
		// TODO Auto-generated method stub
		return mResult;
	}
}
