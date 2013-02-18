/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

import java.util.ArrayList;
import java.util.List;


/**
 * @author musab@informatik.uni-freiburg.de
 *
 */

public class VariableDeclaration extends AtsASTNode {
    /**
	 * 
	 */
	private static final long serialVersionUID = 6868411705150725931L;
	private List<String> m_identifiers;
    
    public VariableDeclaration(String identifier) {
    	m_identifiers = new ArrayList<String>();
    	m_identifiers.add(identifier);
    }
    
    public List<String> getIdentifiers() {
		return m_identifiers;
	}

	public void addVariable(String identifier) {
    	m_identifiers.add(identifier);
    }
	
	public void addVariables(List<String> identifiers) {
		for (String id : identifiers) {
			m_identifiers.add(id);
		}
	}

	@Override
	public String toString() {
		return "VariableDeclaration [Vars: " + m_identifiers + "]";
	}
}
