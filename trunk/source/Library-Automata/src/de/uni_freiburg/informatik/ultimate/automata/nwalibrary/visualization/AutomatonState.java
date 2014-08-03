/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.visualization;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.model.annotation.DefaultAnnotations;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.structure.ModifiableExplicitEdgesMultigraph;

/**
 * Ultimate model of an automaton state.
 * @author heizmann@informatik.uni-freiburg.de 
 */

public class AutomatonState extends ModifiableExplicitEdgesMultigraph<AutomatonState, AutomatonTransition> {
	private static final long serialVersionUID = 264254789648279608L;
	
	private final String m_Name;
	
	public AutomatonState(Object content, boolean isAccepting) {
		
		DefaultAnnotations acceptance = new DefaultAnnotations();
		acceptance.put("isAccepting",isAccepting);
		HashMap<String,IAnnotations> annotations = getPayload().getAnnotations();
		annotations.put("isAccepting", acceptance);
		
		if (content instanceof IAnnotations) {
			annotations.put("Content", (IAnnotations) content);
		}
		
		m_Name = String.valueOf(content);
	}
	
	public String toString() {
		return m_Name;
	}

}
