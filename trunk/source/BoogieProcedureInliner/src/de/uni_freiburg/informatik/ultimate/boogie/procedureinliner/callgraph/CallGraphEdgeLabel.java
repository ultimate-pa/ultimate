package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph;

public class CallGraphEdgeLabel {

	public static enum EdgeType {
		SIMPLE_CALL_UNIMPLEMENTED,
		SIMPLE_CALL_IMPLEMENTED,
		CALL_FORALL,
		EXTERN_RECURSIVE_CALL,
		INTERN_RECURSIVE_CALL;
		
		public boolean isSimpleCall() {
			return ordinal() <= SIMPLE_CALL_IMPLEMENTED.ordinal();
		}
		
		public boolean isRecursive() {
			return ordinal() >= EXTERN_RECURSIVE_CALL.ordinal();
		}
	} 
	
	private String mCalleProcedureId;
	private EdgeType mEdgeType;
	
	private boolean mInlineFlag;

	public CallGraphEdgeLabel(String calleeProcedureId, EdgeType edgeTpye) {
		mCalleProcedureId = calleeProcedureId;
		mEdgeType = edgeTpye;
	}
	
	public String getCalleeProcedureId() {
		return mCalleProcedureId;
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
		return mEdgeType + "(" + mCalleProcedureId + ")" + (mInlineFlag ? "*" : "");
	}


}
