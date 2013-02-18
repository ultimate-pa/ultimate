/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class PetriNetMarking extends AtsASTNode {

	/**
	 * 
	 */
	private static final long serialVersionUID = 4421611212582004461L;
	private String m_place;
	private String m_token;
	
	public PetriNetMarking(String place, String token) {
		m_place = place;
		m_token = token;
	}

	public String getPlace() {
		return m_place;
	}

	public String getToken() {
		return m_token;
	}


}
