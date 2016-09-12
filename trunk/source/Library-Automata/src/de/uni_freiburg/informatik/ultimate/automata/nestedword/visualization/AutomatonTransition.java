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

import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableMultigraphEdge;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;

/**
 * Ultimate model of an automaton transition.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public final class AutomatonTransition
		extends ModifiableMultigraphEdge<AutomatonState, AutomatonTransition, AutomatonState, AutomatonTransition> {
	private static final long serialVersionUID = -2531826841396458461L;
	
	/**
	 * Transition type.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	public enum Transition {
		/**
		 * Call transition.
		 */
		CALL,
		/**
		 * Internal transition.
		 */
		INTERNAL,
		/**
		 * Return transition.
		 */
		RETURN,
		/**
		 * Initial transition.
		 */
		INITIAL
	}
	
	private String mName;
	
	/**
	 * Constructor.
	 * 
	 * @param state
	 *            state
	 * @param type
	 *            transition type
	 * @param transitionLabel
	 *            transition label
	 * @param linPred
	 *            linear predecessor name
	 * @param succState
	 *            successor state representation
	 */
	public AutomatonTransition(final AutomatonState state, final Transition type, final Object transitionLabel,
			final String linPred, final AutomatonState succState) {
		super(state, succState);
		assert type == Transition.RETURN || linPred == null;
		assert type != Transition.RETURN || linPred != null;
		switch (type) {
			case CALL:
				mName = "Call";
				break;
			case INTERNAL:
				mName = "Internal";
				break;
			case RETURN:
				mName = "Return";
				break;
			case INITIAL:
				mName = "";
				break;
			default:
				throw new IllegalArgumentException();
		}
		mName = mName + ": " + transitionLabel;
		if (type == Transition.RETURN) {
			mName = mName + " " + linPred;
		}
		
		if (transitionLabel instanceof IAnnotations) {
			getPayload().getAnnotations().put("Symbol", (IAnnotations) transitionLabel);
		}
		state.addOutgoing(this);
		succState.addIncoming(this);
	}
	
	@Override
	public String toString() {
		return mName;
	}
	
	@Override
	public AutomatonTransition getLabel() {
		return this;
	}
}
