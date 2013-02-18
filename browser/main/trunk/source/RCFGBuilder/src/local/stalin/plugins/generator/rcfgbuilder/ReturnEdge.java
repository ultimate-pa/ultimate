package local.stalin.plugins.generator.rcfgbuilder;

import java.util.LinkedList;
import java.util.List;

import local.stalin.model.IPayload;
import local.stalin.model.IType;
import local.stalin.model.boogie.ast.AssignmentStatement;
import local.stalin.model.boogie.ast.CallStatement;
import local.stalin.model.boogie.ast.Expression;
import local.stalin.model.boogie.ast.IdentifierExpression;
import local.stalin.model.boogie.ast.Procedure;
import local.stalin.model.boogie.ast.VarList;
import local.stalin.model.boogie.ast.VariableLHS;

/**
 * Represents a procedure return in a recursive control flow graph.
 * The update of the variables of the calling prodecure is defined in a
 * TransAnnot object which is contained in the Payload of this RetunEdge.
 * The LocNode from which the procedure was called is stored in m_CallerNode. 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */

public class ReturnEdge extends TransEdge {

	private static final long serialVersionUID = -3389272502488762075L;
	
	private LocNode m_CallerNode;

	public ReturnEdge(LocNode source, LocNode target,
					  IPayload payload, LocNode callerNode) {
		super.setPayload(payload);
		connectSource(source);
		connectTarget(target);
		m_CallerNode = callerNode;
	}
	
	public ReturnEdge(LocNode source,
					  LocNode target,
			          CallStatement st,
			          CallAnnot callAnnot,
			          Procedure proc,
			          LocNode callerNode) {
		super();
		ReturnAnnot returnAnnot = new ReturnAnnot(callAnnot);
		returnAnnot.addStatement(getLocalVariableAssignment(st, proc));
		super.getPayload().getAnnotations().put(Activator.PLUGIN_ID,returnAnnot);
		super.getPayload().setName("Return");
		connectSource(source);
		connectTarget(target);
		m_CallerNode = callerNode;
	}

	
	public LocNode getCallerNode() {
		return m_CallerNode;
	}
	
	
	public ReturnAnnot getReturnAnnotations() {
		return ((ReturnAnnot)
						getPayload().getAnnotations().get(Activator.PLUGIN_ID));
	}
	
	public CallAnnot getCorrespondingCallAnnot() {
		return getReturnAnnotations().getCorrespondingCallAnnot();
	}

	
	private AssignmentStatement getLocalVariableAssignment(
										CallStatement st, Procedure proc) {
		String[] lhsIdentifiers = st.getLhs();
		List<String> outIdentifiers = new LinkedList<String>();
		List<IType> outTypes = new LinkedList<IType>();
		VarList[] outParams = proc.getOutParams();
		for (VarList varList : outParams) {
			String[] identifiers = varList.getIdentifiers();
			IType type = varList.getType().getBoogieType();
			for (String identifier : identifiers) {
				outIdentifiers.add(identifier);
				outTypes.add(type);
			}
		}
		s_Logger.debug("Call "+st+" assigns "+lhsIdentifiers.length+" variables");
		s_Logger.debug("Procedure"+st.getMethodName()+" has "
				+outIdentifiers.size()+"(out)parameters");
		if (lhsIdentifiers.length!=outIdentifiers.size()) {
			throw new IllegalArgumentException("CallStatement" + st + 
					"applied to the wrong number of arguments");
		}
		VariableLHS[] lhs = new VariableLHS[lhsIdentifiers.length];
		Expression[] rhs = new Expression[lhsIdentifiers.length];
		
		for(int i=0;i<lhsIdentifiers.length;i++){
			lhs[i] = new VariableLHS(outTypes.get(i), lhsIdentifiers[i]);
			rhs[i] = new IdentifierExpression(outTypes.get(i), outIdentifiers.get(i));
		}
		return new AssignmentStatement(null,0, lhs,rhs);
	}


}
