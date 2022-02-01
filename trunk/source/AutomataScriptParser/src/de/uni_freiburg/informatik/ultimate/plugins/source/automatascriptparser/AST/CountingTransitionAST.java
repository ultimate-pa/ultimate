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

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;


public class CountingTransitionAST extends AtsASTNode{
	
	private final String mPredecessorState, mLetter, mGuard, mSuccessorState;
	private final UpdateListAST mUpdateList;
	
	public CountingTransitionAST(ILocation loc, String predeccessorState, String letter, String guard, UpdateListAST updateList, String successorState) {
		super(loc);
		this.mPredecessorState = predeccessorState;
		this.mLetter = letter;
		this.mGuard = guard;
		this.mUpdateList = updateList;
		this.mSuccessorState = successorState;
	}
	
	
	public String getPredecessorState() {
		return mPredecessorState;
	}


	public String getLetter() {
		return mLetter;
	}


	public String getGuard() {
		return mGuard;
	}


	public String getSuccessorState() {
		return mSuccessorState;
	}


	public UpdateListAST getUpdateList() {
		return mUpdateList;
	}
}
