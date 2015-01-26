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
	
	public CallGraphEdgeLabel(String calleeProcedureId) {
		this(calleeProcedureId, null);
	}

	public CallGraphEdgeLabel(String calleeProcedureId, EdgeType edgeTpye) {
		mCalleProcedureId = calleeProcedureId;
		mEdgeType = edgeTpye;
	}
	
	public String getCalleeProcedureId() {
		return mCalleProcedureId;
	}
	
	public EdgeType getEdgeType() {
		return mEdgeType;
	}

	@Override
	public int hashCode() {
		return 11 * ((mCalleProcedureId == null) ? 0 : mCalleProcedureId.hashCode())
				+ ((mEdgeType == null) ? 0 : mEdgeType.ordinal() + 1);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		CallGraphEdgeLabel other = (CallGraphEdgeLabel) obj;
		if (mCalleProcedureId == null) {
			if (other.mCalleProcedureId != null)
				return false;
		} else if (!mCalleProcedureId.equals(other.mCalleProcedureId))
			return false;
		if (mEdgeType != other.mEdgeType)
			return false;
		return true;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(mEdgeType);
		sb.append('(');
		sb.append(mCalleProcedureId);
		sb.append(')');
		return sb.toString();
	}


}
