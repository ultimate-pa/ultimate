package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.structure.ModifiableLabeledEdgesMultigraph;

/**
 * Node of a Boogie call graph.
 * A Node is a procedure, where the directed edges are the calls inside this procedure.
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

	public void setProcedureWithSpecificationAndBody(Procedure p) {
		setProcedureWithSpecification(p);
		setProcedureWithBody(p);
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
	
	
	public Procedure getProcedureWithSpecificationAndBody() {
		assert mProcedureWithBody == mProcedureWithSpecification;
		return mProcedureWithBody;
	}
	
	public Procedure getProcedureWithSpecification() {
		return mProcedureWithSpecification;
	}

	public Procedure getProcedureWithBody() {
		return mProcedureWithBody;
	}
	
	@Override
	public String toString() {
		return mId;
	}
}
