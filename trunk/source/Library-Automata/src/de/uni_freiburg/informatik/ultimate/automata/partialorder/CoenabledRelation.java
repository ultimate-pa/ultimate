/*
 * Copyright (C) 2019 Elisabeth Schanno
 * Copyright (C) 2019 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.FinitePrefix;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Relates letters labeling transitions in a Petri net. Two transitions are coenabled if there exists a reachable
 * marking where these transitions can fire independently (i.e., without one disabling the other).
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 *            The type of letters labeling Petri net transitions.
 * @param <PLACE>
 *            The type of the places in the Petri net.
 */
public final class CoenabledRelation<LETTER, PLACE> {

	private final HashRelation<ITransition<LETTER, PLACE>, ITransition<LETTER, PLACE>> mRelation;

	private CoenabledRelation(final HashRelation<ITransition<LETTER, PLACE>, ITransition<LETTER, PLACE>> relation) {
		mRelation = relation;
	}

	/**
	 * Creates a new instance by computing the relation from the given Petri net.
	 *
	 * @param services
	 *            Automata library services to be used in the computation
	 * @param petriNet
	 *            The net whose coenabled-relation shall be computed.
	 *
	 * @return A new relation computed from the finite unfolding prefix of the given net.
	 *
	 * @throws AutomataOperationCanceledException
	 *             if the computation is canceled
	 * @throws PetriNetNot1SafeException
	 *             if the given net is not 1-safe
	 */
	public static <LETTER, PLACE> CoenabledRelation<LETTER, PLACE> fromPetriNet(final AutomataLibraryServices services,
			final IPetriNet<LETTER, PLACE> petriNet)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		final BranchingProcess<LETTER, PLACE> bp = new FinitePrefix<>(services, petriNet).getResult();
		return fromBranchingProcess(bp);
	}

	/**
	 * Creates a new instance by computing the relation from the given branching process.
	 *
	 * @param bp
	 *            The branching process of a Petri net.
	 * @return A new relation computed from the branching process.
	 */
	public static <LETTER, PLACE> CoenabledRelation<LETTER, PLACE>
			fromBranchingProcess(final BranchingProcess<LETTER, PLACE> bp) {
		return new CoenabledRelation<>(computeFromBranchingProcess(bp));
	}

	private static <LETTER, PLACE> HashRelation<ITransition<LETTER, PLACE>, ITransition<LETTER, PLACE>>
			computeFromBranchingProcess(final BranchingProcess<LETTER, PLACE> bp) {
		final HashRelation<ITransition<LETTER, PLACE>, ITransition<LETTER, PLACE>> hashRelation = new HashRelation<>();
		final ICoRelation<LETTER, PLACE> coRelation = bp.getCoRelation();
		final Collection<Event<LETTER, PLACE>> events = bp.getEvents();
		for (final Event<LETTER, PLACE> event1 : events) {
			if (bp.getDummyRoot() != event1) {
				final Set<Event<LETTER, PLACE>> coRelatedEvents = coRelation.computeCoRelatedEvents(event1);
				for (final Event<LETTER, PLACE> coRelatedEvent : coRelatedEvents) {
					hashRelation.addPair(event1.getTransition(), coRelatedEvent.getTransition());
				}
			}
		}
		return hashRelation;
	}

	/**
	 * Determines the size of the relation.
	 *
	 * @return The number of pairs of transitions that are in the relation.
	 */
	public int size() {
		return mRelation.size();
	}

	/**
	 * Computes the set of all coenabled transitions.
	 *
	 * @param element
	 *            The transition whose coenabled transitions shall be computed.
	 * @return The set of all transitions b, such that the pair (element, b) is in the relation.
	 */
	public Set<ITransition<LETTER, PLACE>> getImage(final ITransition<LETTER, PLACE> element) {
		return mRelation.getImage(element);
	}

	/**
	 * For each pair in the relation involving a given transition, creates a new corresponding pair involving the other
	 * transition. The original pairs are not removed, they remain in the relation.
	 *
	 * @param from
	 *            The transition from which the relationships will be copied.
	 * @param to
	 *            The transition to which the relationships will be copied.
	 */
	public void copyRelationships(final ITransition<LETTER, PLACE> from, final ITransition<LETTER, PLACE> to) {
		for (final ITransition<LETTER, PLACE> t3 : mRelation.getImage(from)) {
			mRelation.addPair(to, t3);
		}
		for (final ITransition<LETTER, PLACE> t3 : mRelation.getDomain()) {
			if (mRelation.containsPair(t3, from)) {
				mRelation.addPair(t3, to);
			}
		}
	}

	/**
	 * Removes all pairs involving the given transition from the relation.
	 *
	 * @param transition
	 *            The transition to be removed.
	 */
	public void deleteElement(final ITransition<LETTER, PLACE> transition) {
		mRelation.removeDomainElement(transition);
		mRelation.removeRangeElement(transition);
	}

	/**
	 * Replace oldTransition by newTransition.
	 *
	 * @param oldTransition
	 *            A transition that will be removed from the relation.
	 * @param newTransition
	 *            A transition that will replace the removed transition.
	 */
	public void replaceElement(final ITransition<LETTER, PLACE> oldTransition,
			final ITransition<LETTER, PLACE> newTransition) {
		mRelation.replaceDomainElement(oldTransition, newTransition);
		mRelation.replaceRangeElement(oldTransition, newTransition);
	}

	public void addPair(final ITransition<LETTER, PLACE> first, final ITransition<LETTER, PLACE> second) {
		mRelation.addPair(first, second);
		mRelation.addPair(second, first);
	}
}
