package de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations;
import de.uni_freiburg.informatik.ultimate.model.AbstractAnnotations;


public class AutomatonNameExpression extends AbstractAnnotations {

	private static final long serialVersionUID = -65967713228007967L;
	private final String name;

	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"name"
	};
	


	public AutomatonNameExpression(String name) {
		this.name = name;
	}

	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "name")
			return name;
		else
			throw new UnsupportedOperationException("Unknown field "+field);
	}

	/**
	 * @return the name
	 */
	public String getName() {
		return name;
	}

	
}
