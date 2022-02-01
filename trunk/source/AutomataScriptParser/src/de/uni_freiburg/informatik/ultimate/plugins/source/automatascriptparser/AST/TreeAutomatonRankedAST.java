/*
 * Copyright (C) 2015-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class TreeAutomatonRankedAST extends AutomatonAST {
	
	private static final long serialVersionUID = -6821752595035882929L;

	//	String mId;
	List<RankedAlphabetEntryAST> mRankedAlphabet;
	List<String> mStates;
	List<String> mFinalStates;
	List<TreeAutomatonTransitionAST> mTransitions;
	
	public TreeAutomatonRankedAST(ILocation loc, String id) {
		super(loc, id);
	}
	

	public void setAlphabet(List<RankedAlphabetEntryAST> entryList) {
		mRankedAlphabet = entryList;
	}

	public void setStates(List<String> identifierList) {
		mStates = identifierList;
	}

	public void setFinalStates(List<String> identifierList) {
		mFinalStates = identifierList;
	}

	public void setTransitions(List<TreeAutomatonTransitionAST> transitions) {
		mTransitions = transitions;
	}

//	public String getmId() {
//		return mId;
//	}

	public List<RankedAlphabetEntryAST> getRankedAlphabet() {
		return mRankedAlphabet;
	}

	public List<String> getStates() {
		return mStates;
	}

	public List<String> getFinalStates() {
		return mFinalStates;
	}

	public List<TreeAutomatonTransitionAST> getTransitions() {
		return mTransitions;
	}


	
}
