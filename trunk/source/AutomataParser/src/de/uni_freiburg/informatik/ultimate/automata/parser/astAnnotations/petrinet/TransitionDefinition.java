package de.uni_freiburg.informatik.ultimate.automata.parser.astAnnotations.petrinet;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.model.AbstractAnnotations;

public class TransitionDefinition extends AbstractAnnotations {

	private static final long serialVersionUID = 974342975448223824L;
	private final ArrayList<String> m_Predecessors;
	private final String m_Symbol;
	private final ArrayList<String> m_Successors;
	
	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"predecessors", "symbol", "successors"
	};
	
	public TransitionDefinition(ArrayList<String> predecessors, String symbol, ArrayList<String> successors) {
		super();
		this.m_Predecessors = predecessors;
		this.m_Symbol = symbol;
		this.m_Successors = successors;
	}

	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "predecessors")
			return m_Predecessors;
		else if (field == "symbol")
			return m_Symbol;
		else if (field == "successors")
			return m_Successors;
		else
			throw new UnsupportedOperationException("Unknown field "+field);
	}

	/**
	 * @return the m_Predecessor
	 */
	public ArrayList<String> getPredecessors() {
		return m_Predecessors;
	}

	/**
	 * @return the m_Symbol
	 */
	public String getSymbol() {
		return m_Symbol;
	}

	/**
	 * @return the m_Successor
	 */
	public ArrayList<String> getSuccessors() {
		return m_Successors;
	}
	
}
