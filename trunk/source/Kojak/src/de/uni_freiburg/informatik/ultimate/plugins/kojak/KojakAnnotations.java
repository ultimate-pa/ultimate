package de.uni_freiburg.informatik.ultimate.plugins.kojak;

import de.uni_freiburg.informatik.ultimate.model.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;

public class KojakAnnotations extends AbstractAnnotations{

	/**
	 * 
	 */
	private static final long serialVersionUID = 9102324719771924437L;

	private IPredicate m_predicate = null;
	
	private final static String[] s_AttribFields = {
		"predicate"
	};
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "predicate")
			return m_predicate;
		else
			throw new UnsupportedOperationException("Unknown field "+field);
	}

	public IPredicate getPredicate() {
		return m_predicate;
	}
	
	public void setPredicate(IPredicate predicate) {
		m_predicate = predicate;
	}
	
}
