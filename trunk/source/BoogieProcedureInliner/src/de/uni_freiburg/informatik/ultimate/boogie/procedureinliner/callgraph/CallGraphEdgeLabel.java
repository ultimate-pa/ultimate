package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph;

/**
 * 
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class CallGraphEdgeLabel {

	/**
	 * Describes the type of the call.
	 * 
	 * @author schaetzc@informatik.uni-freiburg.de
	 */
	public static enum EdgeType {
		/** A normal call to an unimplemented procedure. */
		SIMPLE_CALL_UNIMPLEMENTED,
		/** A normal call to an implemented procedure. */
		SIMPLE_CALL_IMPLEMENTED,
		/** A {@code call forall} statement. */
		CALL_FORALL,
		/** A call to a recursive procedure, which doesn't calls the caller again (neither directly nor indirectly). */
		EXTERN_RECURSIVE_CALL,
		/** A recursive call, where the caller is called directly or indirectly from the callee. */
		INTERN_RECURSIVE_CALL;
		
		public boolean isSimpleCall() {
			return ordinal() <= SIMPLE_CALL_IMPLEMENTED.ordinal();
		}
		
		public boolean isRecursive() {
			return ordinal() >= EXTERN_RECURSIVE_CALL.ordinal();
		}
	} 
	
	private String mCalleeProcedureId;

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
