package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import java.util.Collection;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.ISuccessorTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.SimpleSuccessorTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public interface IPetriNetTransitionProvider<LETTER, PLACE> extends IPetriNetSuccessorProvider<LETTER, PLACE> {
	/** @return Outgoing transitions of given place. */
	Set<Transition<LETTER, PLACE>> getSuccessors(final PLACE place);

	/** @return Incoming transitions of given place. */
	Set<Transition<LETTER, PLACE>> getPredecessors(final PLACE place);

	@Override
	default Collection<ISuccessorTransitionProvider<LETTER, PLACE>>
			getSuccessorTransitionProviders(final Set<PLACE> mustPlaces, final Set<PLACE> mayPlaces) {
		final HashRelation<Set<PLACE>, Transition<LETTER, PLACE>> predecessorPlaces2Transition = new HashRelation<>();
		final Set<Transition<LETTER, PLACE>> successorTransitions =
				mustPlaces.stream().flatMap(x -> getSuccessors(x).stream()).collect(Collectors.toSet());
		for (final Transition<LETTER, PLACE> t : successorTransitions) {
			final Set<PLACE> predeccesorOfT = t.getPredecessors();
			if (mayPlaces.containsAll(predeccesorOfT)) {
				predecessorPlaces2Transition.addPair(predeccesorOfT, t);
			}
		}
		return predecessorPlaces2Transition.entrySet().stream()
				.map(x -> new SimpleSuccessorTransitionProvider<>(x.getValue())).collect(Collectors.toList());
	}
}
