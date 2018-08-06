/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.ISuccessorTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.SimpleSuccessorTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization.PetriNetToUltimateModel;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * General Petri net interface.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 *            Type of letters from the alphabet used to label transitions
 */
public interface IPetriNet<LETTER, PLACE> extends IAutomaton<LETTER, PLACE>, IPetriNetSuccessorProvider<LETTER, PLACE> {
	Collection<PLACE> getPlaces();

	Collection<ITransition<LETTER, PLACE>> getTransitions();

	Collection<PLACE> getAcceptingPlaces();





	/** @return Outgoing transitions of given place. */
	Set<ITransition<LETTER, PLACE>> getSuccessors(final PLACE place);

	/** @return Incoming transitions of given place. */
	Set<ITransition<LETTER, PLACE>> getPredecessors(final PLACE place);




	@Override
	default IElement transformToUltimateModel(final AutomataLibraryServices services)
			throws AutomataOperationCanceledException {
		return new PetriNetToUltimateModel<LETTER, PLACE>().transformToUltimateModel(this);
	}

	@Override
	default Collection<ISuccessorTransitionProvider<LETTER, PLACE>> getSuccessorTransitionProviders(final Collection<PLACE> places) {
		final HashRelation<Set<PLACE>, ITransition<LETTER, PLACE>> predecessorPlaces2Transition = new HashRelation<>();
		for (final PLACE p : places) {
			for (final ITransition<LETTER, PLACE> t : getSuccessors(p)) {
				predecessorPlaces2Transition.addPair(getPredecessors(t), t);
			}
		}
		final List<ISuccessorTransitionProvider<LETTER, PLACE>> result = new ArrayList<>();
		for (final Set<PLACE> predecessors : predecessorPlaces2Transition.getDomain()) {
			final Set<ITransition<LETTER, PLACE>> transitions = predecessorPlaces2Transition.getImage(predecessors);
			result.add(new SimpleSuccessorTransitionProvider<>(transitions, this));
		}
		return result;
	}


}
