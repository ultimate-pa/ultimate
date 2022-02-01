/*
 * Copyright (C) 2015 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BoogieProcedureInliner plug-in.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieProcedureInliner plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieProcedureInliner plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BoogieProcedureInliner plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.Deque;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;

/**
 * Value for backtranslation mappings.
 * See documentation of getters, for more information.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class BackTransValue {

	private final String mInlineEntryProcId;
	private final BoogieASTNode mOriginalNode;
	private final Deque<CallStatement> mOriginalCallStack;

	public BackTransValue(String inlineEntryProcId,  Deque<CallStatement> origCallStack, BoogieASTNode origNode) {
		mInlineEntryProcId = inlineEntryProcId;
		mOriginalNode = origNode;
		mOriginalCallStack = origCallStack;
	}

	/** @return Identifier from the Procedure, where the inlining process started. */
	public String getInlineEntryProcId() {
		return mInlineEntryProcId;
	}

	/** 
	 * Returns the stack of original CallStatements, that created the key while inlining.
	 * <p>
	 * The topmost call from the stack is the last/innermost call.<br>
	 * The stack is empty, iff the key was direct part of the entry procedure from the inlining process.
	 * <p>
	 * Reference equality of the stacks and the calls inside the stacks is ensured.
	 * <p>
	 * <b>Don't modify</b> the returned stacks!
	 * 
	 * @return Original call stack.
	 */
	public Deque<CallStatement> getOriginalCallStack() {
		return mOriginalCallStack;
	}

	/**  @return Backtranslated node. {@code null} if the node should be omitted. */
	public BoogieASTNode getOriginalNode() {
		return mOriginalNode;
	}
	
	
	
}
