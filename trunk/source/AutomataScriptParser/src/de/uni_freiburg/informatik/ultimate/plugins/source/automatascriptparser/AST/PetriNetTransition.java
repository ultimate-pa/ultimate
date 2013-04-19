/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class PetriNetTransition extends AtsASTNode {


	/**
	 * 
	 */
	private static final long serialVersionUID = -1676272287026669953L;

	private String m_symbol;

	
	private IdentifierList m_predeccesors;
	private IdentifierList m_successors;
	

	public PetriNetTransition(IdentifierList from, String symbol, IdentifierList to) {
		m_predeccesors = from;
		m_symbol = symbol;
		m_successors = to;
	}
	

	public IdentifierList getPreviousMarking() {
		return m_predeccesors;
	}


	public IdentifierList getNextMarking() {
		return m_successors;
	}


	public String getSymbol() {
		return m_symbol;
	}
	
	/**
	 * Returns the list of predecessor of this transition
	 * @return
	 */
	public List<String> getPreds() {
		return m_predeccesors.getIdentifierList();
	}
	
	/**
	 * Returns the list of successors of this transition
	 * @return
	 */
	public List<String> getSuccs() {
		return m_successors.getIdentifierList();
	}


	@Override
	public String toString() {
		StringBuilder builder = new StringBuilder();
		builder.append("{");
		for (String pred : m_predeccesors.getIdentifierList()) {
			builder.append(pred + " ");
		}
		builder.deleteCharAt(builder.length() - 1);
		builder.append("}" + m_symbol + "{");
		for (String succ : m_successors.getIdentifierList()) {
			builder.append(succ + " ");
		}
		builder.deleteCharAt(builder.length() - 1);
		builder.append("}");
		return builder.toString();
	}


	
	
}
