/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 * 
 * This file is part of the ULTIMATE AutomataScriptParser plug-in.
 * 
 * The ULTIMATE AutomataScriptParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AutomataScriptParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AutomataScriptParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AutomataScriptParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AutomataScriptParser plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class NestedwordAutomatonAST extends AbstractNestedwordAutomatonAST {


	public NestedwordAutomatonAST(final ILocation loc, final String name, final List<String> callAlphabet, final List<String> internalAlphabet,
			final List<String> returnAlphabet, final List<String> states, final List<String> initStates, final List<String> finStates,
			final TransitionListAST internalTransitions, final TransitionListAST callTransitions,
			final TransitionListAST returnTransitions) {
		super(loc, name, callAlphabet, internalAlphabet, returnAlphabet, states, initStates, finStates, internalTransitions,
				callTransitions, returnTransitions);
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("NestedwordAutomaton(" + mName + "): " + "[#call_alph: ");
		builder.append(getCallAlphabet().size());
		builder.append(" #int_alph: ");
		builder.append(getInternalAlphabet().size());
		builder.append(" #return_alph: ");
		builder.append(getReturnAlphabet().size());
		builder.append(" #States: ");
		builder.append(getStates().size());
		builder.append(" #init_states: ");
		builder.append(getInitialStates().size());
		builder.append(" #final_states: ");
		builder.append(getFinalStates().size());
		builder.append(" #int_trans: ");
		builder.append(getInternalTransitions().size());
		builder.append(" #call_trans: ");
		builder.append(getCallTransitions().size());
		builder.append(" #ret_trans: ");
		builder.append(getReturnTransitions().size());
		builder.append("]");
		return builder.toString();
	}
}
