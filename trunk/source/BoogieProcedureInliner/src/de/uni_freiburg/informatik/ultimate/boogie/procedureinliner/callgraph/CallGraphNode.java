package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.structure.ModifiableLabeledEdgesMultigraph;

/**
 * Node of a Boogie call graph.
 * A Node represents a procedure, where the directed edges are the calls inside this procedure.
 * Multiple calls to the same procedure occur multiple times. The order of all calls is preserved.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class CallGraphNode extends ModifiableLabeledEdgesMultigraph<CallGraphNode, CallGraphEdgeLabel> {

	private static final long serialVersionUID = -937014582193693103L;

	private final String mId;
	private Procedure mProcedureWithSpecification;
	private Procedure mProcedureWithBody;

	public CallGraphNode(String id) {
		mId = id;
	}
	
	public String getId() {
		return mId;
	}
	
	public void setProcedureWithSpecification(Procedure p) {
		assert p == null || p.getIdentifier().equals(mId);
		assert p == null || p.getSpecification() != null;
		mProcedureWithSpecification = p;
	}
	
	public void setProcedureWithBody(Procedure p) {
		assert p == null || p.getIdentifier().equals(mId);
		assert p == null || p.getBody() != null;
		mProcedureWithBody = p;
	}

	public Procedure getProcedureWithSpecification() {
		return mProcedureWithSpecification;
	}

	public Procedure getProcedureWithBody() {
		return mProcedureWithBody;
	}

	public boolean isImplemented() {
		return mProcedureWithBody != null;
	}
	
	/**
	 * Iterates over all outgoing edge labels, looking for set inline flags.
	 * @return A call statement inside the procedure should be inlined.
	 * @see CallGraphEdgeLabel#getInlineFlag()
	 */
	public boolean hasInlineFlags() {
		for (CallGraphEdgeLabel edgeLabel : getOutgoingEdgeLabels()) {
			if (edgeLabel.getInlineFlag()) {
				return true;
			}
		}
		return false;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(mId);
		sb.append(isImplemented() ? "(implemented)" : "(unimplemented)");
		sb.append(getOutgoingEdgeLabels());
		return sb.toString();
	}
}
