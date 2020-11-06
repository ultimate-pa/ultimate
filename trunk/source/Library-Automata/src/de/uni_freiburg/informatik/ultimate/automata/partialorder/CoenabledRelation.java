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
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.FinitePrefix;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Relates letters labeling transitions in a Petri net. Two letters are coenabled if there exists a reachable marking
 * where transitions labelled with these letters can fire independently (i.e., without one disabling the other).
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 *            The type of letters labeling Petri net transitions.
 */
public final class CoenabledRelation<LETTER> {

	private final HashRelation<LETTER, LETTER> mRelation;

	private CoenabledRelation(final HashRelation<LETTER, LETTER> relation) {
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
	public static <PLACE, LETTER> CoenabledRelation<LETTER> fromPetriNet(final AutomataLibraryServices services,
			final IPetriNet<LETTER, PLACE> petriNet)
					throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		final BranchingProcess<LETTER, PLACE> bp = new FinitePrefix<>(services, petriNet).getResult();
		return new CoenabledRelation<>(computeFromBranchingProcess(bp));
	}

	private static <PLACE, LETTER> HashRelation<LETTER, LETTER>
	computeFromBranchingProcess(final BranchingProcess<LETTER, PLACE> bp) {
		final HashRelation<LETTER, LETTER> hashRelation = new HashRelation<>();
		final ICoRelation<LETTER, PLACE> coRelation = bp.getCoRelation();
		final Collection<Event<LETTER, PLACE>> events = bp.getEvents();
		for (final Event<LETTER, PLACE> event1 : events) {
			if (bp.getDummyRoot() != event1) {
				final Set<Event<LETTER, PLACE>> coRelatedEvents = coRelation.computeCoRelatatedEvents(event1);
				for (final Event<LETTER, PLACE> coRelatedEvent : coRelatedEvents) {
					hashRelation.addPair(event1.getTransition().getSymbol(),
							coRelatedEvent.getTransition().getSymbol());
				}
			}
		}
		return hashRelation;
	}

	/**
	 * Determines the size of the relation.
	 *
	 * @return The number of pairs of letters that are in the relation.
	 */
	public int size() {
		return mRelation.size();
	}

	/**
	 * Computes the set of all coenabled letters.
	 *
	 * @param element
	 *            The letter whose coenabled letters shall be computed.
	 * @return The set of all letters b, such that the pair (element, b) is in the relation.
	 */
	public Set<LETTER> getImage(final LETTER element) {
		return mRelation.getImage(element);
	}

	/**
	 * For each pair in the relation involving a given letter, creates a new corresponding pair involving the other
	 * letter. The original pairs are not removed, they remain in the relation.
	 */
	public void copyRelationships(final LETTER from, final LETTER to) {
		for (final LETTER t3 : mRelation.getImage(from)) {
			mRelation.addPair(to, t3);
		}
		for (final LETTER t3 : mRelation.getDomain()) {
			if (mRelation.containsPair(t3, from)) {
				mRelation.addPair(t3, to);
			}
		}
	}

	/**
	 * Removes all pairs involving the given letter from the relation.
	 */
	public void deleteElement(final LETTER letter) {
		mRelation.removeDomainElement(letter);
		mRelation.removeRangeElement(letter);
	}
}
