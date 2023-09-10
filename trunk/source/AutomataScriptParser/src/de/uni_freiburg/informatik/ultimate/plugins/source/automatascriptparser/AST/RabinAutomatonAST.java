/*
 * Copyright (C) 2023 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class RabinAutomatonAST extends AutomatonAST {
	private final List<String> mAlphabet;
	private final List<String> mStates;
	private final List<String> mInitialStates;
	private final List<String> mAcceptingStates;
	private final List<String> mFiniteStates;
	private final Map<Pair<String, String>, Set<String>> mTransitions;

	public RabinAutomatonAST(final ILocation loc, final String name, final List<String> alphabet,
			final List<String> states, final List<String> initialStates, final List<String> acceptingStates,
			final List<String> finiteStates, final TransitionListAST transitions) {
		super(loc, name);
		mAlphabet = alphabet == null ? List.of() : alphabet;
		mStates = states == null ? List.of() : states;
		mInitialStates = initialStates == null ? List.of() : initialStates;
		mAcceptingStates = acceptingStates == null ? List.of() : acceptingStates;
		mFiniteStates = finiteStates == null ? List.of() : finiteStates;
		mTransitions = transitions == null ? Map.of() : transitions.getTransitions();
	}

	public List<String> getAlphabet() {
		return mAlphabet;
	}

	public List<String> getStates() {
		return mStates;
	}

	public List<String> getInitialStates() {
		return mInitialStates;
	}

	public List<String> getAcceptingStates() {
		return mAcceptingStates;
	}

	public List<String> getFiniteStates() {
		return mFiniteStates;
	}

	public Map<Pair<String, String>, Set<String>> getTransitions() {
		return mTransitions;
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("RabinAutomaton(" + mName + "): " + "[#alphabet: ");
		builder.append(mAlphabet.size());
		builder.append(" #states: ");
		builder.append(mStates.size());
		builder.append(" #initalStates: ");
		builder.append(mInitialStates.size());
		builder.append(" #acceptingStates: ");
		builder.append(mAcceptingStates.size());
		builder.append(" #finiteStates: ");
		builder.append(mFiniteStates.size());
		builder.append(" #transitions: ");
		builder.append(mTransitions.size());
		builder.append("]");
		return builder.toString();
	}
}
