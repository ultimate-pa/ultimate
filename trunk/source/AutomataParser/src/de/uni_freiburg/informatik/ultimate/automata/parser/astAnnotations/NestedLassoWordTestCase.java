package de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations;
import de.uni_freiburg.informatik.ultimate.model.AbstractAnnotations;


public class NestedLassoWordTestCase extends AbstractAnnotations {

	private static final long serialVersionUID = 4369873014201526957L;
	private final String operation;

	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"operation"
	};
	


	public NestedLassoWordTestCase(String operation) {
		this.operation = operation;
	}

	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "operation")
			return operation;
		else
			throw new UnsupportedOperationException("Unknown field "+field);
	}

	/**
	 * @return the operation
	 */
	public String getOperation() {
		return operation;
	}
	
	

}
