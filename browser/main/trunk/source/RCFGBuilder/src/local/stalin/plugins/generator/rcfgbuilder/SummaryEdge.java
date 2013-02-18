package local.stalin.plugins.generator.rcfgbuilder;

import java.util.List;

import local.stalin.model.IPayload;
import local.stalin.model.boogie.ast.CallStatement;
import local.stalin.model.boogie.ast.Statement;

/**
 * Represents execution of a call in a recursive control flow graph.
 * Source of this edge is the LocNode where the procedure was called.
 * Target of this edge is the LocNode where the procedure returns to.
 * The effect of the execution of the procedure is defined by a TranAnnot object
 * which is contained in the Payload of this SummaryEdge.
 *  
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class SummaryEdge extends TransEdge {

	private static final long serialVersionUID = -2923506946454722306L;

	public SummaryEdge(LocNode source, LocNode target, IPayload payload) {
		super.setPayload(payload);
		connectSource(source);
		connectTarget(target);
	}
	
	
	public SummaryEdge(LocNode source, LocNode target, CallStatement st) {
		super();
		TransAnnot transAnnot = new TransAnnot();
		transAnnot.addStatement(st);
		super.getPayload().getAnnotations().put(Activator.PLUGIN_ID,transAnnot);
		super.getPayload().setName("Summary");
		
		connectSource(source);
		connectTarget(target);
	}

	public TransAnnot getInternalAnnotations() {
		return ((TransAnnot) getPayload().getAnnotations().get(Activator.PLUGIN_ID));
	}
	

	public CallStatement getCallStatement() {
		TransAnnot transAnnot = (TransAnnot)
				super.getPayload().getAnnotations().get(Activator.PLUGIN_ID);
		List<Statement> stmts = transAnnot.getStatements();
		assert (stmts.size() == 1) : "SummaryEdge should contain exactly one" +
				"CallStatement";
		return (CallStatement) stmts.get(0);
	}
	


}
