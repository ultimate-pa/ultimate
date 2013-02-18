package local.stalin.plugins.generator.rcfgbuilder;

import local.stalin.model.boogie.ast.AssignmentStatement;

/**
 * Defines the behaviour of a CallEdge in a recursive control flow graph.
 * A CallEdge is a TransitionEdge that provides also an auxiliary
 * TransitionFormula (m_OldVarsEquality) which can be used for the computation
 * of nested interpolants.
 * m_OldVarsEquality represents the equality y_in=y_out for every global
 * variable that may be modified by the called procedure. These equalities
 * should be used to express that the value of the global variable is the same 
 * as the value of the variable in the old context.   
 * @author heizmann@informatik.uni-freiburg.de
 */
public class CallAnnot extends TransAnnot {

	private static final long serialVersionUID = 5047439633229508126L;

	protected AssignmentStatement m_GlobalVarSelfAssignment;
	protected TransFormula m_OldVarsEquality;
	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"Statements", "PrettyPrintedStatements", "TransitionFormula",
		"OldVarsEquality", "OccurenceInCounterexamples"
	};
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "OldVarsEquality") {
			return m_OldVarsEquality;
		}
		else {
			return super.getFieldValue(field);
		}
	}

	public AssignmentStatement getGlobalVarSelfAssignment() {
		return m_GlobalVarSelfAssignment;
	}

	public void setGlobalVarSelfAssignment(
			AssignmentStatement globalVarSelfAssignment) {
		m_GlobalVarSelfAssignment = globalVarSelfAssignment;
	}

	public TransFormula getOldVarsEquality() {
		return m_OldVarsEquality;
	}

	public void setOldVarsEquality(TransFormula oldVarsEquality) {
		m_OldVarsEquality = oldVarsEquality;
	}
}
