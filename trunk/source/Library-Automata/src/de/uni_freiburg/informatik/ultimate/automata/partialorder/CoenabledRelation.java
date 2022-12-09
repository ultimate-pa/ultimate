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
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.FinitePrefix;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.SymmetricHashRelation;

/**
 * Relates letters labeling transitions in a Petri net. Two transitions are coenabled if there exists a reachable
 * marking where these transitions can fire independently (i.e., without one disabling the other).
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters labeling Petri net transitions.
 * @param <P>
 *            The type of the places in the Petri net.
 */
public final class CoenabledRelation<L, P> extends SymmetricHashRelation<Transition<L, P>> {

	private CoenabledRelation() {
		super();
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
	public static <L, P> CoenabledRelation<L, P> fromPetriNet(final AutomataLibraryServices services,
			final IPetriNet<L, P> petriNet) throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		final BranchingProcess<L, P> bp = new FinitePrefix<>(services, petriNet).getResult();
		return fromBranchingProcess(bp);
	}

	/**
	 * Creates a new instance by computing the relation from the given branching process.
	 *
	 * @param bp
	 *            The branching process of a Petri net.
	 * @return A new relation computed from the branching process.
	 */
	public static <L, P> CoenabledRelation<L, P> fromBranchingProcess(final BranchingProcess<L, P> bp) {
		final var relation = new CoenabledRelation<L, P>();
		final ICoRelation<L, P> coRelation = bp.getCoRelation();
		final Collection<Event<L, P>> events = bp.getEvents();
		for (final Event<L, P> event1 : events) {
			if (bp.getDummyRoot() != event1) {
				final Set<Event<L, P>> coRelatedEvents = coRelation.computeCoRelatedEvents(event1);
				for (final Event<L, P> coRelatedEvent : coRelatedEvents) {
					relation.addPair(event1.getTransition(), coRelatedEvent.getTransition());
				}
			}
		}
		return relation;
	}

	public void renameAndProjectTransitions(final Map<Transition<L, P>, Transition<L, P>> old2New) {
		for (final var entry : old2New.entrySet()) {
			final var original = entry.getKey();
			final var copy = entry.getValue();
			replaceElement(original, copy);
		}
		final var obsolete = DataStructureUtils.difference(getDomain(), Set.copyOf(old2New.values()));
		for (final var trans : obsolete) {
			removeElement(trans);
		}
	}
}
