package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;

public class PredicateWithHistory extends SPredicate {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 4545005036147569544L;
	private final Map<Integer,Term> m_History;
	

	protected PredicateWithHistory(ProgramPoint programPoint, int serialNumber, 
			String[] procedures, Term formula,
			Set<BoogieVar> vars, Term closedFormula, Map<Integer,Term> history) {
		super(programPoint, serialNumber, procedures, formula, vars, closedFormula);
		this.m_History = history;
	}

	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"ProgramPoint", "Procedures", "Formula", "Vars", "History"
	};
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}
	
	@Override
	protected Object getFieldValue(String field) {
		if (field == "History")
			return m_History;
		else 
			return super.getFieldValue(field);
	}
	
	public Map<Integer,Term> getCopyOfHistory() {
		Map<Integer,Term> result = new HashMap<Integer,Term>();
		for (Integer i : m_History.keySet()) {
			result.put(i, m_History.get(i));
		}
		return result;
	}
	
//	public void setHistory(Map<Integer,Term> history) {
//		m_History = history;
//	}

}
