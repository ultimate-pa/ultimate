/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class IdentifierList extends AtsASTNode {

	/**
	 * 
	 */
	private static final long serialVersionUID = -7741847124495330627L;
	private List<String> m_idList;
	
	
	public IdentifierList() {
		m_idList = new ArrayList<String>();
	}
	
	public void addId(String id) {
		m_idList.add(id);
	}
	
	public List<String> getIdentifierList() {
		return m_idList;
	}
	
	/**
	 * Use at your own risk
	 * @param i this parameter is the index of the identifier you want to get
	 * @return the identifier at index i, or throws an exception
	 */
	public String getIdentifier(int i) {
		return m_idList.get(i);
	}
	
	// Some methods needed for petri nets
	/**
	 * Indicates whether this list contains 2 identifiers.
	 * @return true iff it contains exactly 2 identifiers, otherwise false.
	 */
	public boolean isPair() {
		return (m_idList.size() == 2);
	}

	@Override
	public String getAsString() {
		StringBuilder builder = new StringBuilder();
		for (String id : m_idList) {
			builder.append(id + " ");
		}
		return builder.toString();
	}
	
	
	
}
