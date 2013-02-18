package local.stalin.automata.parser.astAnnotations;
import local.stalin.model.AbstractAnnotations;


public class SymbolAtCallPosition extends AbstractAnnotations {

	private static final long serialVersionUID = 2314928752144627129L;
	private final String identifier;

	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"identifier"
	};
	


	public SymbolAtCallPosition(String identifier) {
		this.identifier = identifier;
	}

	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "identifier")
			return identifier;
		else
			throw new UnsupportedOperationException("Unknown field "+field);
	}

	/**
	 * @return the identifier
	 */
	public String getIdentifier() {
		return identifier;
	}
	
	

}
