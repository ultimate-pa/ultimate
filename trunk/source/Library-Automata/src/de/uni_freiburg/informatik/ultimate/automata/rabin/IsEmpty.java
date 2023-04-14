package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

public class IsEmpty<LETTER, STATE, CRSF extends IStateFactory<STATE>> extends GeneralOperation<LETTER, STATE, CRSF> {

	private List<LETTER> mWordEvidence;
	private List<STATE> mStateEvidence;
	private final Boolean mResult;

	final AutomatonSccComputation<LETTER, STATE> acceptingSccComputation;

	public IsEmpty(final AutomataLibraryServices services, final IRabinAutomaton<LETTER, STATE> automaton)
			throws AutomataOperationCanceledException {
		super(services);

		final EagerRabinAutomaton<LETTER, STATE> eagerAutomaton;

		if (EagerRabinAutomaton.class == automaton.getClass()) {
			eagerAutomaton = (EagerRabinAutomaton<LETTER, STATE>) automaton;
		} else {
			eagerAutomaton = new EagerRabinAutomaton<>(automaton);
			// Reduces the automaton to its traversable core
		}

		acceptingSccComputation =
				new AutomatonSccComputation<>(services, eagerAutomaton.getStemlessNonFiniteAutomaton());

		mResult = acceptingSccComputation.getBalls().isEmpty();

	}

	@Override
	public Boolean getResult() {
		// TODO Auto-generated method stub
		return mResult;
	}

}
