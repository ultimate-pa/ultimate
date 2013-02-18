package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;

public class ProdState extends BasicPredicate {

	/**
	 * 
	 */
	private static final long serialVersionUID = -8826942011742605334L;
	
	List<IPredicate> m_Predicates = new ArrayList<IPredicate>();
	
	protected ProdState(int serialNumber, List<IPredicate> mPredicates, Term term, Set<BoogieVar> vars) {
		super(serialNumber, null, term, vars, null);
		m_Predicates = mPredicates;
	}

	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"Predicates", "Formula", "Vars", "OldVars"
	};
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "Predicates")
			return m_Predicates;
		else 
			return super.getFieldValue(field);
	}

	public void addPredicate(IPredicate Predicate) {
		m_Predicates.add(Predicate);
	}
	
	public List<IPredicate> getPredicates() {
		return m_Predicates;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.StateFormula#toString()
	 */
	@Override
	public String toString() {
//		StringBuilder result = new StringBuilder();
//		for (Predicate pp : m_Predicates)
//			result.append(pp.getPosition()  + ",");
//		return result.toString();
		return m_Predicates.toString();
	}
	
	
}
