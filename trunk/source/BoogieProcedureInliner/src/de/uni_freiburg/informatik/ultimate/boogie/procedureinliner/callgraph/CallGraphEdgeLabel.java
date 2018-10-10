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
package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph;

/**
 * Information about the type of the call (recursive, call forall, ...).
 * The flag -- whether to inline a call or not -- is stored here too.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class CallGraphEdgeLabel {

	/**
	 * Describes the type of the call.
	 * 
	 * @author schaetzc@informatik.uni-freiburg.de
	 */
	public enum EdgeType {
		/** A normal call to an unimplemented procedure. */
		SIMPLE_CALL_UNIMPLEMENTED,
		/** A normal call to an implemented procedure. */
		SIMPLE_CALL_IMPLEMENTED,
		/** A {@code call forall} statement. */
		CALL_FORALL,
		/** A call to a recursive procedure which does not call the caller again (neither directly nor indirectly). */
		EXTERN_RECURSIVE_CALL,
		/** A recursive call where the caller is called directly or indirectly from the callee. */
		INTERN_RECURSIVE_CALL,
		/** A fork (starts another thread, cannot be inlined). Joins are not represented in the call graph. */
		FORK;

		public boolean isSimpleCall() {
			return ordinal() <= SIMPLE_CALL_IMPLEMENTED.ordinal();
		}

		public boolean isRecursive() {
			return this == EXTERN_RECURSIVE_CALL || this == INTERN_RECURSIVE_CALL;
		}
	}

	private final String mCalleeProcedureId;

	private EdgeType mEdgeType;

	/** The call, represented by this CallGraphEdge shall be inlined. */
	private boolean mInlineFlag = false;

	/**
	 * Constructs a CalLGraphEdge, which initially isn't marked for inlining.
	 * @param calleeProcedureId Identifier of the called procedure. 
	 * @param edgeTpye Type of the call.
	 */
	public CallGraphEdgeLabel(String calleeProcedureId, EdgeType edgeTpye) {
		mCalleeProcedureId = calleeProcedureId;
		mEdgeType = edgeTpye;
	}
	
	public String getCalleeProcedureId() {
		return mCalleeProcedureId;
	}
	
	public void setEdgeType(EdgeType edgeType) {
		mEdgeType = edgeType;
	}

	public EdgeType getEdgeType() {
		return mEdgeType;
	}

	public void setInlineFlag(boolean inlineFlag) {
		mInlineFlag = inlineFlag;
	}

	public boolean getInlineFlag() {
		return mInlineFlag;
	}

	@Override
	public String toString() {
		return mEdgeType + "(" + mCalleeProcedureId + ")" + (mInlineFlag ? "*" : "");
	}


}
