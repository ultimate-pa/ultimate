package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.ISuccessorTransitionProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public interface IPetriNetSuccessorProvider<LETTER, PLACE> extends IAutomaton<LETTER, PLACE> {

	Set<PLACE> getInitialPlaces();

	/** @return Outgoing places of given transition. */
	ImmutableSet<PLACE> getSuccessors(ITransition<LETTER, PLACE> transition);

	/** @return Incoming places of given transition. */
	ImmutableSet<PLACE> getPredecessors(final ITransition<LETTER, PLACE> transition);

	/**
	 *
	 * @param place2allowedSiblings
	 * @return all {@link ISuccessorTransitionProvider}s such that for its predecessors {p1,...,pn}
	 * there exists some i such that pi is in the domain of the place2allowedSiblings and all
	 * elements of {p1,...,p_{i-1},p_{i+1},pn} are in relation with pi.
	 */
	Collection<ISuccessorTransitionProvider<LETTER, PLACE>> getSuccessorTransitionProviders(
			final HashRelation<PLACE, PLACE> place2allowedSiblings);

	/**
	 *
	 * @return {@link ISuccessorTransitionProvider}s such that the set of
	 *         predecessors contains only "mayPlaces" and at least one "mustPlaces".
	 */
	Collection<ISuccessorTransitionProvider<LETTER, PLACE>> getSuccessorTransitionProviders(
			final Set<PLACE> mustPlaces,
			final Set<PLACE> mayPlaces);

	/**
	 * @param marking
	 *            A marking.
	 * @return {@code true} iff the marking is accepting.
	 */
	boolean isAccepting(Marking<PLACE> marking);

	boolean isAccepting(PLACE place);

}