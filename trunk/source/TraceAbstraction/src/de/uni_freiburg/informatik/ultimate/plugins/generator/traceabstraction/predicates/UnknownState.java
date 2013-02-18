package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;

public class UnknownState implements ISLPredicate {

//	private static final long serialVersionUID = 9190582215913478152L;
	private final ProgramPoint m_ProgramPoint;
	private final int m_SerialNumber;
	
	protected UnknownState(ProgramPoint programPoint, int serialNumber) {
		m_ProgramPoint = programPoint;
		m_SerialNumber = serialNumber;
		
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
		if (m_ProgramPoint != null) {
			return m_ProgramPoint.getPosition();
		}
		else {
			return "unknown";
		}
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
		throw new UnsupportedOperationException();
	}

	@Override
	public Set<BoogieVar> getVars() {
		throw new UnsupportedOperationException();
	}

	@Override
	public String[] getProcedures() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Term getClosedFormula() {
		// TODO Auto-generated method stub
		return null;
	}





}
