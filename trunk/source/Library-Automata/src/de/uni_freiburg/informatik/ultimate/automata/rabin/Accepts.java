package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

public class Accepts<LETTER, STATE, CRSF extends IStateFactory<STATE>> extends GeneralOperation<LETTER, STATE, CRSF> {
	private final boolean mResult;

	public Accepts(final AutomataLibraryServices services, final IRabinAutomaton<LETTER, STATE> automaton,
			final NestedLassoWord<LETTER> word) {
		super(services);
		// TODO: Could we use another type of lasso-words here instead?
		if (!word.getStem().hasEmptyNestingRelation() || !word.getLoop().hasEmptyNestingRelation()) {
			throw new AssertionError("Rabin automata cannot handle calls/returns.");
		}
		mResult = computeResult(automaton, word.getStem().asList(), word.getLoop().asList());
	}

	private boolean computeResult(final IRabinAutomaton<LETTER, STATE> automaton, final List<LETTER> stem,
			final List<LETTER> loop) {
		// TODO: Implement this
		return false;
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}
}
