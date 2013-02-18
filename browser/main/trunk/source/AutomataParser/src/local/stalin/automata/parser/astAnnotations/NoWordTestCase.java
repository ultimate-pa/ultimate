package local.stalin.automata.parser.astAnnotations;
import local.stalin.model.AbstractAnnotations;


public class NoWordTestCase extends AbstractAnnotations {

	private static final long serialVersionUID = 8724215026562975804L;
	private final String operation;

	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"operation"
	};
	


	public NoWordTestCase(String operation) {
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
