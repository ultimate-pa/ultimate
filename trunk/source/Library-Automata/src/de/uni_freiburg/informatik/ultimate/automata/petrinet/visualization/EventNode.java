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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;

/**
 * Ultimate model of an OcurrenceNet event.
 * <p>
 * TODO Christian 2017-02-06 What is an "OcurrenceNet"?
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <S>
 *            symbol type
 * @param <C>
 *            place content type
 */
public final class EventNode<S, C> extends PetriNetVisualizationNode {
	private static final long serialVersionUID = -2531826841396458461L;

	/**
	 * @param event
	 *            Event.
	 */
	// false-positive warning (resp. impossible to solve due to "super constructor comes first" rule in Java)
	@SuppressWarnings("fb-contrib:PRMC_POSSIBLY_REDUNDANT_METHOD_CALLS")
	public EventNode(final Event<S, C> event) {
		super(event.getTransition().getSymbol().toString());

		final Transition<S, C> transition = event.getTransition();
		final DefaultAnnotations annot = new DefaultAnnotations();
		annot.put("Transition", transition);
		annot.put("Companion", event.getCompanion());
		annot.put("Ancestors", event.getAncestors());
		annot.put("ByLocalConfigurationRepresentedMarking", event.getMark());

		final Map<String, IAnnotations> annotations = getPayload().getAnnotations();
		annotations.put(LibraryIdentifiers.PLUGIN_ID, annot);

		final S symbol = transition.getSymbol();
		if (symbol instanceof IAnnotations) {
			annot.put("Symbol", symbol);
		}
	}
}
