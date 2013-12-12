package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;

/**
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BasicPredicate extends AbstractAnnotations implements IPredicate {
	private static final long serialVersionUID = -2257982001512157622L;
	protected final String[] m_Procedures;
	protected Term m_Formula;
	protected final Term m_ClosedFormula;
	protected final Set<BoogieVar> m_Vars;
	protected final int m_SerialNumber;
	
	
	
	protected BasicPredicate(int serialNumber, String[] procedures, Term term, Set<BoogieVar> vars,
			Term closedFormula) {
		m_Formula = term;
		m_ClosedFormula = closedFormula;
		m_Procedures = procedures;
		m_Vars = vars;
		m_SerialNumber = serialNumber;
	}


	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"Procedures", "Formula", "Vars"
	};
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "Procedures")
			return m_Procedures;
		else if (field == "Formula")
			return m_Formula;
		else if (field == "Vars")
			return m_Vars;
		else
			throw new UnsupportedOperationException("Unknown field "+field);
	}
	
	
	public String[] getProcedures() {
		return m_Procedures;
	}

	/**
	 * @return the m_Assertion
	 */
	public Term getFormula() {
		return m_Formula;
	}
	
	public Term getClosedFormula() {
		return m_ClosedFormula;
	}

	public Set<BoogieVar> getVars() {
		return m_Vars;
	}
	
	@Override
	public String toString() {
		String result = m_SerialNumber + "#";
		result += m_Formula.toStringDirect();
		return result;
	}

	public boolean isUnknown() {
		return false;
	}

	@Override
	public int hashCode() {
		return m_SerialNumber;
	}
	
}