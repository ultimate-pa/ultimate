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

import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.structure.ModifiableMultigraphEdge;

/**
 * Ultimate model of an automaton transition.
 * @author heizmann@informatik.uni-freiburg.de 
 */

public class AutomatonTransition extends ModifiableMultigraphEdge<AutomatonState, AutomatonTransition> {

	private static final long serialVersionUID = -2531826841396458461L;
	
	public enum Transition { CALL, INTERNAL, RETURN, INITIAL };
	
	private String m_Name;
	
	public AutomatonTransition(AutomatonState state,
							   Transition type,
							   Object transitionLabel,
							   String linPred,
							   AutomatonState succState) {
		super(state, succState);
		assert(type == Transition.RETURN || linPred ==null);
		assert(type != Transition.RETURN || linPred != null);
		switch (type) {
		case CALL: m_Name = "Call"; break;
		case INTERNAL: m_Name = "Internal"; break;
		case RETURN: m_Name = "Return"; break;
		case INITIAL: m_Name = ""; break;
		default: throw new IllegalArgumentException();
		}
		m_Name = m_Name + ": " + transitionLabel;
		if (type == Transition.RETURN) {
			m_Name = m_Name + " " + linPred;
		}
		
		if (transitionLabel instanceof IAnnotations) {
			getPayload().getAnnotations().put("Symbol", (IAnnotations) transitionLabel);
		}
		state.addOutgoing(this);
		succState.addIncoming(this);
		getPayload().setName(m_Name);
	}
	public String toString() {
		return m_Name;
	}

}
