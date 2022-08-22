package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import java.util.Collection;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.ISuccessorTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.SimpleSuccessorTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public interface IPetriNetSuccessorProvider<LETTER, PLACE> extends IAutomaton<LETTER, PLACE> {

	Set<PLACE> getInitialPlaces();

	/** @return Outgoing transitions of given place. */
	Set<Transition<LETTER, PLACE>> getSuccessors(final PLACE place);

	/** @return Incoming transitions of given place. */
	Set<Transition<LETTER, PLACE>> getPredecessors(final PLACE place);

	/**
	 *
	 * @return {@link ISuccessorTransitionProvider}s such that the set of predecessors contains only "mayPlaces" and at
	 *         least one "mustPlaces".
	 */
	default Collection<ISuccessorTransitionProvider<LETTER, PLACE>>
			getSuccessorTransitionProviders(final Set<PLACE> mustPlaces, final Set<PLACE> mayPlaces) {
		final HashRelation<Set<PLACE>, Transition<LETTER, PLACE>> predecessorPlaces2Transition = new HashRelation<>();
		for (final PLACE p : mustPlaces) {
			for (final Transition<LETTER, PLACE> t : getSuccessors(p)) {
				final Set<PLACE> predeccesorOfT = t.getPredecessors();
				if (mayPlaces.containsAll(predeccesorOfT)) {
					predecessorPlaces2Transition.addPair(predeccesorOfT, t);
				}
			}
		}
		return predecessorPlaces2Transition.entrySet().stream()
				.map(x -> new SimpleSuccessorTransitionProvider<>(x.getValue())).collect(Collectors.toList());
	}

	/**
	 * @param marking
	 *            A marking.
	 * @return {@code true} iff the marking is accepting.
	 */
	boolean isAccepting(Marking<PLACE> marking);

	boolean isAccepting(PLACE place);

}