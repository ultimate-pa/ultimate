package de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations;
import de.uni_freiburg.informatik.ultimate.model.AbstractAnnotations;


public class NestedWord extends AbstractAnnotations {

	private static final long serialVersionUID = -8029219440474308254L;
	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
	};
	


	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
			throw new UnsupportedOperationException("Unknown field "+field);
	}

	
	

}
