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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;

/**
 * Ultimate model of an automaton state.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public final class AutomatonState extends
		ModifiableExplicitEdgesMultigraph<AutomatonState, AutomatonTransition, AutomatonState, AutomatonTransition> {
	private static final long serialVersionUID = 264254789648279608L;
	
	private final String mName;
	
	/**
	 * Constructor.
	 * 
	 * @param content
	 *            state content
	 * @param isAccepting
	 *            {@code true} iff the state is accepting
	 */
	public AutomatonState(final Object content, final boolean isAccepting) {
		final DefaultAnnotations acceptance = new DefaultAnnotations();
		acceptance.put("isAccepting", isAccepting);
		final Map<String, IAnnotations> annotations = getPayload().getAnnotations();
		annotations.put("isAccepting", acceptance);
		
		if (content instanceof IAnnotations) {
			annotations.put("Content", (IAnnotations) content);
		}
		
		mName = String.valueOf(content);
	}
	
	@Override
	public String toString() {
		return mName;
	}
	
	@Override
	public AutomatonState getLabel() {
		return this;
	}
}
