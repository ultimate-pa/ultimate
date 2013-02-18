package local.stalin.plugins.generator.rcfgbuilder;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import local.stalin.model.IPayload;
import local.stalin.model.IType;
import local.stalin.model.boogie.ast.ASTType;
import local.stalin.model.boogie.ast.AssignmentStatement;
import local.stalin.model.boogie.ast.CallStatement;
import local.stalin.model.boogie.ast.Expression;
import local.stalin.model.boogie.ast.IdentifierExpression;
import local.stalin.model.boogie.ast.Procedure;
import local.stalin.model.boogie.ast.UnaryExpression;
import local.stalin.model.boogie.ast.VarList;
import local.stalin.model.boogie.ast.VariableLHS;
import local.stalin.model.boogie.ast.BinaryExpression.Operator;
/**
 * Represents an procedure call in a recursive control flow graph.
 * The initialization of the input variables of the called procedure is defined
 * in an CallAnnotations object which is contained in the Payload of this
 * CallEdge.
 * A CallAnnotations object provides also an auxiliary TransitionFormula
 * (m_OldVarsEquality) that can be used for the computation
 * of nested interpolants. This auxiliary TransitionFormula is obtained from an
 * auxiliary AssignmentStatement which is computed by buildSelfAssignment(...)
 * defined in this class.
 *  
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class CallEdge extends TransEdge {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = -4965044088568203179L;

	public CallEdge(LocNode source, LocNode target, IPayload payload){
		super.setPayload(payload);
		connectSource(source);
		connectTarget(target);
	}
	
	public CallEdge(LocNode source,
					LocNode target,
					CallStatement st,
					Procedure proc,
					Map<String,ASTType> modifiedGlobalVars) {
		super();
		CallAnnot callAnnot = new CallAnnot();
		callAnnot.addStatement(getLocalVariableAssignment(st, proc));
		callAnnot.setGlobalVarSelfAssignment(
					buildSelfAssignment(modifiedGlobalVars));
		super.getPayload().getAnnotations().put(Activator.PLUGIN_ID,callAnnot);
		super.getPayload().setName("Call");
		connectSource(source);
		connectTarget(target);
	}
	
	public CallAnnot getCallAnnotations() {
		return ((CallAnnot)
						getPayload().getAnnotations().get(Activator.PLUGIN_ID));
	}
	

	
	/**
	 * Build AssignmentStatement that represents initialization of the input
	 * variables during a procedure call. The left hand side of the assignment
	 * contains only local variables since in BoogiePL global variables are not
	 * modified during a procedure call. The update of the "OLD global variable"
	 * is not represented by this assignment.  
	 * @param st
	 * @param proc Procedure which is called by the CallStatement st.
	 * @return AssignmentStatement that represents the initialization of the
	 *  input variables of the called procedure.
	 */
	private AssignmentStatement getLocalVariableAssignment(CallStatement st,
														   Procedure proc) {
		Expression[] arguments = st.getArguments();
		List<VariableLHS> parameterList = new LinkedList<VariableLHS>();
		VarList[] inParams = proc.getInParams();
		for (VarList varList : inParams) {
			String[] identifiers = varList.getIdentifiers();
			IType type = varList.getType().getBoogieType();
			for (String identifier : identifiers) {
				parameterList.add(new VariableLHS(type, identifier));
			}
		}
		s_Logger.debug("Call "+st+" has "+arguments.length+" arguments");
		s_Logger.debug("Procedure"+st.getMethodName()+" has "
				+parameterList.size()+"(in)parameters");
		if (arguments.length!=parameterList.size()) {
			throw new IllegalArgumentException("CallStatement" + st + 
					"has wrong number of arguments");
		}
		VariableLHS[] lhs = parameterList.toArray(new VariableLHS[0]);
		return new AssignmentStatement(null,0, lhs,arguments);
	}
	

	/**
	 * Build AssignmentStatement such that to a variable the own value is
	 * assigned. 
	 * This AssignmentStatement seems to be pretty useless, but will be used to
	 * build an auxiliary TransitionFormula used for the computation of nested
	 * interpolants.
	 * @param vars Representation for a set of variables. A variable name is
	 * mapped to its type.  
	 * @return Assignment where we assign to each variable in vars its own value 
	 */
	private AssignmentStatement buildSelfAssignment(Map<String,ASTType> vars) {
		Collection<String> identifiers;
		if (vars==null) {
			identifiers = new HashSet<String>(0);
		}
		else {
			identifiers = vars.keySet();
		}
		VariableLHS[] lhs = new VariableLHS[identifiers.size()];
		Expression[] rhs = new Expression[identifiers.size()];
		
		int i=0;
		for (String identifier : identifiers) {
			IType type = vars.get(identifier).getBoogieType();
			lhs[i] = new VariableLHS(type,identifier);
			rhs[i] = new IdentifierExpression(type,identifier);
			rhs[i] = new UnaryExpression(UnaryExpression.Operator.OLD, rhs[i]);
			i++;
		}
		return new AssignmentStatement(null,0,lhs,rhs);
	}
	
}
