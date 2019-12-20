package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.ISuccessorTransitionProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public interface IPetriNetSuccessorProvider<LETTER, PLACE> extends IAutomaton<LETTER, PLACE> {

	Set<PLACE> getInitialPlaces();

	/** @return Outgoing places of given transition. */
	Set<PLACE> getSuccessors(ITransition<LETTER, PLACE> transition);


	/** @return Incoming places of given transition. */
	Set<PLACE> getPredecessors(final ITransition<LETTER, PLACE> transition);

	Collection<ISuccessorTransitionProvider<LETTER, PLACE>> getSuccessorTransitionProviders(
			final HashRelation<PLACE, PLACE> place2allowedSiblings);

	/**
	 * @param marking
	 *            A marking.
	 * @return {@code true} iff the marking is accepting.
	 */
	boolean isAccepting(Marking<LETTER, PLACE> marking);

	boolean isAccepting(PLACE place);

}