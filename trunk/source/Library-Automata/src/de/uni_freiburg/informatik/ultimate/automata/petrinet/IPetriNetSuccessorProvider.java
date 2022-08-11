package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.ISuccessorTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;

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
	Collection<ISuccessorTransitionProvider<LETTER, PLACE>> getSuccessorTransitionProviders(final Set<PLACE> mustPlaces,
			final Set<PLACE> mayPlaces);

	/**
	 * @param marking
	 *            A marking.
	 * @return {@code true} iff the marking is accepting.
	 */
	boolean isAccepting(Marking<LETTER, PLACE> marking);

	boolean isAccepting(PLACE place);

}