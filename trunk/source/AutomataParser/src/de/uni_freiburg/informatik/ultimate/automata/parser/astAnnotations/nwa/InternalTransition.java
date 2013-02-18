package de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations.nwa;
import de.uni_freiburg.informatik.ultimate.model.AbstractAnnotations;


public class InternalTransition extends AbstractAnnotations {

	private static final long serialVersionUID = -2561393438913623451L;
	private final String m_Predecessor;
	private final String m_Symbol;
	private final String m_Successor;
	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"predecessor", "symbol", "successor"
	};
	
	public InternalTransition(String predecessor, String symbol, String successor) {
		super();
		this.m_Predecessor = predecessor;
		this.m_Symbol = symbol;
		this.m_Successor = successor;
	}

	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "predecessor")
			return m_Predecessor;
		else if (field == "symbol")
			return m_Symbol;
		else if (field == "successor")
			return m_Successor;
		else
			throw new UnsupportedOperationException("Unknown field "+field);
	}

	/**
	 * @return the m_Predecessor
	 */
	public String getM_Predecessor() {
		return m_Predecessor;
	}

	/**
	 * @return the m_Symbol
	 */
	public String getM_Symbol() {
		return m_Symbol;
	}

	/**
	 * @return the m_Successor
	 */
	public String getM_Successor() {
		return m_Successor;
	}
	
}
