package local.stalin.automata.parser.astAnnotations;
import local.stalin.model.AbstractAnnotations;


public class StartNode extends AbstractAnnotations {

	private static final long serialVersionUID = 5455318598271842272L;
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
	};
	
	public StartNode() {
	}

	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
			throw new UnsupportedOperationException("Unknown field "+field);
	}

}
