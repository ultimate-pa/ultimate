package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.ISuccessorTransitionProvider;

public interface IPetriNetSuccessorProvider<LETTER, PLACE> extends IAutomaton<LETTER, PLACE> {

	Set<PLACE> getInitialPlaces();

	/**
	 *
	 * @return {@link ISuccessorTransitionProvider}s such that the set of predecessors contains only "mayPlaces" and at
	 *         least one "mustPlaces".
	 */
	Collection<ISuccessorTransitionProvider<LETTER, PLACE>> getSuccessorTransitionProviders(final Set<PLACE> mustPlaces,
			final Set<PLACE> mayPlaces);

	/**
	 * @param marking
	 *            A marking.
	 * @return {@code true} iff the marking is accepting.
	 */
	boolean isAccepting(Marking<PLACE> marking);

	boolean isAccepting(PLACE place);

}