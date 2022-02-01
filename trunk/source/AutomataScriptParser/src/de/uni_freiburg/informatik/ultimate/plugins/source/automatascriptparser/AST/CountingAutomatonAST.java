/*
 * Copyright (C) 2020 Jacob Maxam (jacob.maxam@googlemail.com)
 * Copyright (C) 2020 University of Freiburg
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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * @author Jacob Maxam
 */
public class CountingAutomatonAST extends AutomatonAST {
	//private static final long serialVersionUID = ???;

	private final List<String> mAlphabet;
	private final List<String> mStates;
	private final List<String> mCounters;
	
	private final StateConditionPairListAST mInitialConditions;
	private final StateConditionPairListAST mFinalConditions;

	private final CountingTransitionListAST mTransitions;

	public CountingAutomatonAST(final ILocation loc, final String name, final List<String> alphabet,
			final List<String> states, final List<String> counters, final StateConditionPairListAST initConditions,
			final StateConditionPairListAST finConditions,
			final CountingTransitionListAST transitions) {
		super(loc, name);
		if (alphabet != null) {
			mAlphabet = alphabet;
		} else {
			mAlphabet = new ArrayList<String>();
		}
		if (states != null) {
			mStates = states;
		} else {
			mStates = new ArrayList<String>();
		}
		if (counters != null) {
			mCounters = counters;
		} else {
			mCounters = new ArrayList<String>();
		}
		
		mInitialConditions = initConditions;
		
		mFinalConditions = finConditions;
		
		mTransitions = transitions;
	}

	public List<String> getAlphabet() {
		return mAlphabet;
	}

	public List<String> getStates() {
		return mStates;
	}

	public List<String> getCounters() {
		return mCounters;
	}

	public StateConditionPairListAST getInitialConditions() {
		return mInitialConditions;
	}

	public StateConditionPairListAST getFinalConditions() {
		return mFinalConditions;
	}

	public CountingTransitionListAST getTransitions() {
		return mTransitions;
	}
	
	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("CountingAutomaton(" + mName + "): " + "[#Alph: ");
		builder.append(mAlphabet.size());
		builder.append(" #States: ");
		builder.append(mStates.size());
		builder.append(" #Counters: ");
		builder.append(mCounters.size());
		builder.append(" #Trans: ");
		builder.append(mTransitions.size());
		builder.append("]");
		return builder.toString();
	}
}