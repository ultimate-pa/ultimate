package de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;

public class CFGNodeAnnotations extends AbstractAnnotations {
	/**
	 * The serial version UID.  Change only if serial representation changes.
	 */
	private static final long serialVersionUID = -221145005712480077L;
	
	private Procedure m_Procedure;
	private List<Statement> m_Statements = new ArrayList<Statement>();
	
	HashMap<BoogieVar, TermVariable> m_InVars;
	HashMap<BoogieVar, TermVariable> m_OutVars;
	HashSet<TermVariable> m_Vars;
	Term m_Assertion;
	Term m_Assumption;

	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"procedure", "statements", 
		"invars", "outvars", "vars",
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

	public void setInVars(HashMap<BoogieVar, TermVariable> hashMap) {
		m_InVars = hashMap;
	}
	public void setOutVars(HashMap<BoogieVar, TermVariable> outVars) {
		m_OutVars = outVars;
	}
	public void setVars(HashSet<TermVariable> vars) {
		m_Vars = vars;
	}
	public void setAssertion(Term assertion) {
		m_Assertion = assertion;
	}
	public void setAssumption(Term assumption) {
		m_Assumption = assumption;
	}

	public List<Statement> getStatements() {
		return m_Statements;
	}

	public Term getAssertion() {
		return m_Assertion;
	}
	
	public Term getAssumption() {
		return m_Assumption;
	}
	
	public HashMap<BoogieVar, TermVariable> getInVars() {
		if (m_InVars == null)
			m_InVars = new HashMap<BoogieVar, TermVariable>();
		return m_InVars;
	}
	public HashMap<BoogieVar, TermVariable> getOutVars() {
		if (m_OutVars == null)
			m_OutVars = new HashMap<BoogieVar, TermVariable>();
		return m_OutVars;
	}

	public HashSet<TermVariable> getVars() {
		if(m_Vars == null)
			m_Vars = new HashSet<TermVariable>();
		return m_Vars;
	}
	
	public boolean isProcedureRoot() {
		return m_Procedure != null;
	}

	public Procedure getProcedure() {
		return m_Procedure;
	}

}
