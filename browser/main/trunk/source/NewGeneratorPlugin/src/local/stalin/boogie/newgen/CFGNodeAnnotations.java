package local.stalin.boogie.newgen;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import local.stalin.logic.Formula;
import local.stalin.logic.TermVariable;
import local.stalin.model.AbstractAnnotations;
import local.stalin.model.boogie.ast.AssumeStatement;
import local.stalin.model.boogie.ast.Procedure;
import local.stalin.model.boogie.ast.Statement;

public class CFGNodeAnnotations extends AbstractAnnotations {
	/**
	 * The serial version UID.  Change only if serial representation changes.
	 */
	private static final long serialVersionUID = -221145005712480077L;
	
	private Procedure m_Procedure;
	private List<Statement> m_Statements = new ArrayList<Statement>();
	
	HashMap<String, TermVariable> m_InVars;
	HashMap<String, TermVariable> m_OutVars;
	HashMap<String, TermVariable> m_OldVars;
	HashSet<TermVariable> m_Vars;
	Formula m_Assertion;
	Formula m_Assumption;

	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"procedure", "statements", 
		"invars", "outvars", "vars", "oldvars",
		"assertion", "assumption"
	};
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "procedure")
			return m_Procedure;
		else if (field == "statements")
			return m_Statements;
		else if (field == "invars")
			return m_InVars;
		else if (field == "outvars")
			return m_OutVars;
		else if (field == "oldvars")
			return m_OldVars;
		else if (field == "vars")
			return m_Vars;
		else if (field == "assertion")
			return m_Assertion;
		else if (field == "assumption")
			return m_Assumption;
		else
			throw new UnsupportedOperationException("Unknown field "+field);
	}

	public void addStatement(Statement statement) {
		m_Statements.add(statement);
	}

	public void addStatement(int i, AssumeStatement statement) {
		m_Statements.add(i, statement);
	}

	public void setProcedure(Procedure p) {
		m_Procedure = p;
	}

	public void setInVars(HashMap<String, TermVariable> inVars) {
		m_InVars = inVars;
	}
	public void setOutVars(HashMap<String, TermVariable> outVars) {
		m_OutVars = outVars;
	}
	public void setVars(HashSet<TermVariable> vars) {
		m_Vars = vars;
	}
	public void setOldVars(HashMap<String, TermVariable> oldVars) {
		m_OldVars = oldVars;
	}
	public void setAssertion(Formula assertion) {
		m_Assertion = assertion;
	}
	public void setAssumption(Formula assumption) {
		m_Assumption = assumption;
	}

	public List<Statement> getStatements() {
		return m_Statements;
	}

	public boolean isProcedureRoot() {
		return m_Procedure != null;
	}

	public Procedure getProcedure() {
		return m_Procedure;
	}

}
