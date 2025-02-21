package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

// TODO find a good name
public interface IEmpireAutomaton<L, P, S> extends INwaOutgoingLetterAndTransitionProvider<Transition<L, P>, S> {
	IPredicate getLaw(S state);

	boolean containsPlace(S state, P place);

	@Override
	default IStateFactory<S> getStateFactory() {
		throw new UnsupportedOperationException();
	}

	@Override
	default S getEmptyStackState() {
		return null;
	}

	@Override
	default boolean isFinal(final S state) {
		return false;
	}

	@Override
	default Iterable<OutgoingCallTransition<Transition<L, P>, S>> callSuccessors(final S state,
			final Transition<L, P> letter) {
		return List.of();
	}

	@Override
	default Iterable<OutgoingReturnTransition<Transition<L, P>, S>> returnSuccessors(final S state, final S hier,
			final Transition<L, P> letter) {
		return List.of();
	}
}
