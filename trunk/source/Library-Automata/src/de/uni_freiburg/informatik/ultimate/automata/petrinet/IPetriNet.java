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

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.Word;
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
 * @param <C>
 *            place content type
 */
public interface IPetriNet<LETTER, C> extends IAutomaton<LETTER, C> {
	/**
	 * @return The places.
	 */
	Collection<Place<C>> getPlaces();

	/**
	 * @return The transitions.
	 */
	Collection<ITransition<LETTER, C>> getTransitions();

	/**
	 * @return The initial marking.
	 */
	Marking<LETTER, C> getInitialMarking();

	/**
	 * @return The accepting markings.
	 */
	Collection<Collection<Place<C>>> getAcceptingMarkings();

	/**
	 * @param marking
	 *            A marking.
	 * @return {@code true} iff the marking is accepting.
	 */
	boolean isAccepting(Marking<LETTER, C> marking);

	/**
	 * @param word
	 *            A word.
	 * @return {@code true} iff the word is accepted.
	 */
	boolean accepts(Word<LETTER> word);

	default boolean acceptsEmptyWord() {
		final Word<LETTER> emptyWord = new Word<>();
		return accepts(emptyWord);
	}

	@Override
	default IElement transformToUltimateModel(final AutomataLibraryServices services)
			throws AutomataOperationCanceledException {
		return new PetriNetToUltimateModel<LETTER, C>().transformToUltimateModel(this);
	}

	/** @return Map from each place to its outgoing transitions. */
	HashRelation<Place<C>, ITransition<LETTER, C>> getSuccessors();
	

	/** @return Map from each place to its incoming transitions. */
	HashRelation<Place<C>, ITransition<LETTER, C>> getPredecessors();
	
	/** @return Outgoing transitions of one place. */
	default Set<ITransition<LETTER, C>> getSuccessors(Place<C> place) {
		return getSuccessors().getImage(place);
	}

	/** @return Incoming transitions of one place. */
	default Set<ITransition<LETTER, C>> getPredecessors(Place<C> place) {
		return getPredecessors().getImage(place);
	}

}
