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
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.TransitionListAST.Pair;



/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class NestedwordAutomatonAST extends AutomatonAST {

	/**
	 * 
	 */
	private static final long serialVersionUID = 2260897609736623517L;
	
	private List<String> mCallAlphabet;
	private List<String> mInternalAlphabet;
	private List<String> mReturnAlphabet;
	
	private List<String> mStates;
	private List<String> mInitialStates;
	private List<String> mFinalStates;
	
	private Map<Pair<String, String>, Set<String>> mInternalTransitions;
	private Map<Pair<String, String>, Set<String>> mCallTransitions;
	private Map<String, Map<String, Map<String, Set<String>>>> mReturnTransitions;
	
	public NestedwordAutomatonAST(ILocation loc, String name) {
		super(loc);
		mCallAlphabet = new ArrayList<String>();
		mInternalAlphabet = new ArrayList<String>();
		mReturnAlphabet = new ArrayList<String>();
		mStates = new ArrayList<String>();
		mInitialStates = new ArrayList<String>();
		mFinalStates = new ArrayList<String>();
		mInternalTransitions = new HashMap<Pair<String,String>, Set<String>>();
		mCallTransitions = new HashMap<Pair<String,String>, Set<String>>();
		mReturnTransitions = new HashMap<String, Map<String, Map<String, Set<String>>>>();
		mName = name;
		
	}

	public List<String> getCallAlphabet() {
		return mCallAlphabet;
	}

	public void setCallAlphabet(List<String> mCallAlphabet) {
		if (mCallAlphabet != null)
			this.mCallAlphabet = mCallAlphabet;
	}

	public List<String> getInternalAlphabet() {
		return mInternalAlphabet;
	}

	public void setInternalAlphabet(List<String> mInternalAlphabet) {
		if (mInternalAlphabet != null)
			this.mInternalAlphabet = mInternalAlphabet;
	}

	public List<String> getReturnAlphabet() {
		return mReturnAlphabet;
	}

	public void setReturnAlphabet(List<String> mReturnAlphabet) {
		if (mReturnAlphabet != null)
			this.mReturnAlphabet = mReturnAlphabet;
	}
	
	public void setStates(List<String> states) {
		if (states != null)
			mStates = states;
	}
	
	public void setInitialStates(List<String> initStates) {
		if (initStates != null)
			mInitialStates = initStates;
	}
	public void setFinalStates(List<String> finStates) {
		if (finStates != null)
			mFinalStates = finStates;
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

	public void setInternalTransitions(TransitionListAST internalTransitions) {
		if (internalTransitions != null)
			this.mInternalTransitions = internalTransitions.getTransitions();
	}

	public Map<Pair<String, String>, Set<String>> getCallTransitions() {
		return mCallTransitions;
	}

	public void setCallTransitions(TransitionListAST callTransitions) {
		if (callTransitions != null)
			this.mCallTransitions = callTransitions.getTransitions();
	}

	public Map<String, Map<String, Map<String, Set<String>>>> getReturnTransitions() {
		return mReturnTransitions;
	}

	public void setReturnTransitions(TransitionListAST returnTransitions) {
		if (returnTransitions != null)
			this.mReturnTransitions = returnTransitions.getReturnTransitions();
	}

	@Override
	public String toString() {
		StringBuilder builder = new StringBuilder();
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
