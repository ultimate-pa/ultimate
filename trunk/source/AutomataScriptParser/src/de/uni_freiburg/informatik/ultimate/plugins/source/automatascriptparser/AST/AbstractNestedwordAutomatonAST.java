/*
 * Copyright (C) 2013-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author musab@informatik.uni-freiburg.de
 */
public abstract class AbstractNestedwordAutomatonAST extends AutomatonAST {
	private static final long serialVersionUID = 2260897609736623517L;

	private final List<String> mCallAlphabet;
	private final List<String> mInternalAlphabet;
	private final List<String> mReturnAlphabet;

	private final List<String> mStates;
	private final List<String> mInitialStates;
	private final List<String> mFinalStates;

	private final Map<Pair<String, String>, Set<String>> mInternalTransitions;
	private final Map<Pair<String, String>, Set<String>> mCallTransitions;
	private final Map<String, Map<String, Map<String, Set<String>>>> mReturnTransitions;

	public AbstractNestedwordAutomatonAST(final ILocation loc, final String name, final List<String> callAlphabet,
			final List<String> internalAlphabet, final List<String> returnAlphabet, final List<String> states,
			final List<String> initStates, final List<String> finStates, final TransitionListAST internalTransitions,
			final TransitionListAST callTransitions, final TransitionListAST returnTransitions) {
		super(loc, name);
		if (callAlphabet != null) {
			mCallAlphabet = callAlphabet;
		} else {
			mCallAlphabet = new ArrayList<String>();
		}
		if (internalAlphabet != null) {
			mInternalAlphabet = internalAlphabet;
		} else {
			mInternalAlphabet = new ArrayList<String>();
		}
		if (returnAlphabet != null) {
			mReturnAlphabet = returnAlphabet;
		} else {
			mReturnAlphabet = new ArrayList<String>();
		}
		if (states != null) {
			mStates = states;
		} else {
			mStates = new ArrayList<String>();
		}
		if (initStates != null) {
			mInitialStates = initStates;
		} else {
			mInitialStates = new ArrayList<String>();
		}
		if (finStates != null) {
			mFinalStates = finStates;
		} else {
			mFinalStates = new ArrayList<String>();
		}
		if (internalTransitions != null) {
			mInternalTransitions = internalTransitions.getTransitions();
		} else {
			mInternalTransitions = new HashMap<>();
		}
		if (callTransitions != null) {
			mCallTransitions = callTransitions.getTransitions();
		} else {
			mCallTransitions = new HashMap<>();
		}
		if (returnTransitions != null) {
			mReturnTransitions = returnTransitions.getReturnTransitions();
		} else {
			mReturnTransitions = new HashMap<>();
		}
	}

	public List<String> getCallAlphabet() {
		return mCallAlphabet;
	}

	public List<String> getInternalAlphabet() {
		return mInternalAlphabet;
	}

	public List<String> getReturnAlphabet() {
		return mReturnAlphabet;
	}

	public List<String> getStates() {
		return mStates;
	}

	public List<String> getInitialStates() {
		return mInitialStates;
	}

	public List<String> getFinalStates() {
		return mFinalStates;
	}

	public Map<Pair<String, String>, Set<String>> getInternalTransitions() {
		return mInternalTransitions;
	}

	public Map<Pair<String, String>, Set<String>> getCallTransitions() {
		return mCallTransitions;
	}

	public Map<String, Map<String, Map<String, Set<String>>>> getReturnTransitions() {
		return mReturnTransitions;
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("NestedwordAutomaton(" + mName + "): " + "[#call_alph: ");
		builder.append(mCallAlphabet.size());
		builder.append(" #int_alph: ");
		builder.append(mInternalAlphabet.size());
		builder.append(" #return_alph: ");
		builder.append(mReturnAlphabet.size());
		builder.append(" #States: ");
		builder.append(mStates.size());
		builder.append(" #init_states: ");
		builder.append(mInitialStates.size());
		builder.append(" #final_states: ");
		builder.append(mFinalStates.size());
		builder.append(" #int_trans: ");
		builder.append(mInternalTransitions.size());
		builder.append(" #call_trans: ");
		builder.append(mCallTransitions.size());
		builder.append(" #ret_trans: ");
		builder.append(mReturnTransitions.size());
		builder.append("]");
		return builder.toString();
	}
}
