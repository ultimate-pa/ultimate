/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class AutomatonAST extends AtsASTNode {

	/**
	 * 
	 */
	private static final long serialVersionUID = -5781432895026883308L;
	// The variable which is associated with this automaton
	protected String m_Name;
	

	public String getName() {
		return m_Name;
	}


	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 7;
		result = prime * result + ((m_Name == null) ? 0 : m_Name.hashCode());
		return result;
	}


	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		AutomatonAST other = (AutomatonAST) obj;
		if (m_Name == null) {
			if (other.m_Name != null)
				return false;
		} else if (!m_Name.equals(other.m_Name))
			return false;
		return true;
	}
	
	
	
}
