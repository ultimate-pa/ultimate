package de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations;

import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;

public class Boogie2SMTAnnotation extends AbstractAnnotations {

	/**
	 * 
	 */
	private static final long serialVersionUID = -1582207944510090271L;
	Boogie2SMT m_boogie2smt;

	public Boogie2SMTAnnotation(Boogie2SMT b2s) {
		m_boogie2smt = b2s;
	}
	
	public Boogie2SMT getBoogie2smt() {
		return m_boogie2smt;
	}

	@Override
	protected String[] getFieldNames() {
		return new String[]{"boogie2smt"};
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field.equals("boogie2smt")) {
			return m_boogie2smt;
		} else
			throw new UnsupportedOperationException("Unknown field "+field);
	}
}
