/*
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;

/**
 * Ultimate model of an {@link IPetriNet} transition.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public final class TransitionNode extends PetriNetVisualizationNode {
	private static final long serialVersionUID = -2531826841396458461L;

	/**
	 * @param transition
	 *            A transition.
	 */
	public TransitionNode(final Transition<?, ?> transition) {
		super(transition.getSymbol().toString());

		final IPayload payload = getPayload();
		final DefaultAnnotations thisPluginsAnnotations = new DefaultAnnotations();
		thisPluginsAnnotations.put("hashCode", transition.hashCode());
		final Map<String, IAnnotations> annotations = payload.getAnnotations();
		annotations.put(LibraryIdentifiers.PLUGIN_ID, thisPluginsAnnotations);

		final Object symbol = transition.getSymbol();
		if (symbol instanceof IAnnotations) {
			thisPluginsAnnotations.put("Symbol", symbol);
		}
	}
}
