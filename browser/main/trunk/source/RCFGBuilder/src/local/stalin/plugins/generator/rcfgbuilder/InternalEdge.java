package local.stalin.plugins.generator.rcfgbuilder;

import java.util.List;

import local.stalin.model.IPayload;
import local.stalin.model.boogie.ast.AssignmentStatement;
import local.stalin.model.boogie.ast.AssumeStatement;
import local.stalin.model.boogie.ast.HavocStatement;
import local.stalin.model.boogie.ast.Statement;
import local.stalin.plugins.generator.rcfgbuilder.TransAnnot.Origin;

/**
 * Represents an edge in a control flow graph. (In a recursive CFG the edge of a
 * control flow graph is called InternalEdge - opposed to CallEdge and
 * ReturnEdge)
 * The behaviour and origin of this edge is defined in an TransitionAnnotations
 * object, which is contained in the Payload of this TransitionEdge.
 * The origin of the edge is either, the requires specification, the ensures
 * specification, an assert statement or the implementation of a procedure.
 * The TransitionAnnotations object contains a list of Statements. The name of
 * the InternalEdge's Payload is
 * <ul>
 * <li>a prettyprinted representation of the Statements, if the origin of this
 *  edge is the implementation,</li>
 * <li>"Assert" if origin of this edge is an AssertStatement,</li>
 * <li>"Requires" if origin of this edge is the requires specification,</li>
 * <li>"Ensures" if origin of this edge is the ensures specification.</li>
 * </ul>
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */

public class InternalEdge extends TransEdge {
	

	private static final long serialVersionUID = -4965044088568203179L;
	/**
	 * Defines the maximum length of this edges name.
	 */
	private static final int MAX_NAME_LENGTH = 20;
	
	public InternalEdge(LocNode source, LocNode target, IPayload payload) {
		super.setPayload(payload);
		connectSource(source);
		connectTarget(target);
	}

	public InternalEdge(LocNode source, LocNode target, Statement st, Origin origin) {
		super();
		TransAnnot transAnnot = new TransAnnot(origin);
		super.getPayload().getAnnotations().put(Activator.PLUGIN_ID,transAnnot);
		addStatement(st);
		
		connectSource(source);
		connectTarget(target);
	}
	
	public TransAnnot getInternalAnnotations() {
		return ((TransAnnot) getPayload().getAnnotations().get(Activator.PLUGIN_ID));
	}
	
	public void addStatement(Statement st) {
		if ( st instanceof AssumeStatement
				|| st instanceof AssignmentStatement
				|| st instanceof HavocStatement ) {
		}
		else {
			throw new IllegalArgumentException("Only Assignment, Assume and" +
					" HavocStatement allowed in InternalEdge.");
		}
		getInternalAnnotations().addStatement(st);
		updatePayloadName(st);
	}
	
	public List<Statement> getStatements() {
		return getInternalAnnotations().getStatements();
	}
	
//	public Statement getStatement() {
//		assert (!UnstructuredBoogie2RecursiveCFGObserver.MULTIPLE_STATEMENTS_PER_TRANSITION) :
//			"MULTIPLE_STATEMENTS_PER_TRANSITION is set. Use getStatements()" +
//			" instead of getStatement()";
//		return getStatements().get(0);
//	}
	
	
	public void updatePayloadName(Statement st) {
		String name;
		if (getPayload().hasName()) {
			name = getPayload().getName();
		}
		else {
			name = "";
		}
		Origin origin = getInternalAnnotations().getOrigin();
		switch (origin) {
		case ASSERT : getPayload().setName("Assert");
		break;
		case REQUIRES : getPayload().setName("Requires");
		break;
		case ENSURES : getPayload().setName("Ensures");
		break;
		case IMPLEMENTATION : {
			if (name.length()<MAX_NAME_LENGTH) {
				name = name + BoogieStatementPrettyPrinter.print(st);
				if (name.length()>MAX_NAME_LENGTH) {
					name = name.substring(0, MAX_NAME_LENGTH) + "...";
				}
				getPayload().setName(name);
			}
		}
		}
	}
}
