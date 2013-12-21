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
public class PetriNetTransitionAST extends AtsASTNode {


	/**
	 * 
	 */
	private static final long serialVersionUID = -1676272287026669953L;

	private String m_symbol;

	
	private IdentifierListAST m_predeccesors;
	private IdentifierListAST m_successors;
	

	public PetriNetTransitionAST(IdentifierListAST from, String symbol, IdentifierListAST to) {
		m_predeccesors = from;
		m_symbol = symbol;
		m_successors = to;
	}
	

	public IdentifierListAST getPreviousMarking() {
		return m_predeccesors;
	}


	public IdentifierListAST getNextMarking() {
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
