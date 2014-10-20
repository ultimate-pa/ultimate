package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;

public class UnknownState implements ISLPredicate {

//	private static final long serialVersionUID = 9190582215913478152L;
	private final ProgramPoint m_ProgramPoint;
	private final int m_SerialNumber;
	private final Term m_Term;
	
	protected UnknownState(ProgramPoint programPoint, int serialNumber, Term term) {
		m_ProgramPoint = programPoint;
		m_SerialNumber = serialNumber;
		m_Term = term;
		
//		super(programPoint, serialNumber, new String[0], term, null, null);
	}
	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"ProgramPoint", "isUnknown"
	};
	
//	@Override
//	protected String[] getFieldNames() {
//		return s_AttribFields;
//	}

//	@Override
//	protected Object getFieldValue(String field) {
//		if (field == "ProgramPoint")
//			return m_ProgramPoint;
//		else if (field == "isUnknown")
//			return true;
//		else
//			throw new UnsupportedOperationException("Unknown field "+field);
//	}
	
	@Override
	public String toString() {
		String result = m_SerialNumber + "#";
		if (m_ProgramPoint != null) {
			result += m_ProgramPoint.getPosition();
		}
		else {
			result += "unknown";
		}
		return result;
	}
	
	@Override
	public int hashCode() {
		return m_SerialNumber;
	}
	
	
	public ProgramPoint getProgramPoint() {
		return m_ProgramPoint;
	}
	
	
	@Override
	public Term getFormula() {
		return m_Term;
	}

	@Override
	public Set<BoogieVar> getVars() {
		throw new UnsupportedOperationException();
	}

	@Override
	public String[] getProcedures() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Term getClosedFormula() {
		throw new UnsupportedOperationException();
	}





}
