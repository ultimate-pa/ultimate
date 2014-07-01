package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;

/**
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class SPredicate extends BasicPredicate implements ISLPredicate {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1750137515726690834L;
	protected final ProgramPoint m_ProgramPoint;
	
	
	protected SPredicate(ProgramPoint programPoint, int serialNumber, String[] procedures, Term term, Set<BoogieVar> vars, Term closedFormula) {
		super(serialNumber,procedures,term,vars,closedFormula);
		m_ProgramPoint = programPoint;
	}


	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"ProgramPoint", "Procedures", "Formula", "Vars"
	};
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "ProgramPoint")
			return m_Procedures;
		else
			return super.getFieldValue(field);
	}
	
	@Override
	public ProgramPoint getProgramPoint() {
		return m_ProgramPoint;
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
		String result = super.m_SerialNumber + "#";
		if (m_ProgramPoint != null) {
			result += m_ProgramPoint.getPosition();
		}
		result += m_Formula.toString();
		return result;
	}



	public boolean isUnknown() {
		return false;
	}

	@Override
	public int hashCode() {
		return super.m_SerialNumber;
	}
	
	
	
	
	


}
