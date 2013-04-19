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
public class PetriNetMarkingList extends AtsASTNode {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = -2876076623803821394L;
	private IdentifierList m_markings;
	
	public PetriNetMarkingList() {
		m_markings = new IdentifierList();
	}
	
	public PetriNetMarkingList(IdentifierList idlist) {
		this();
		m_markings = idlist;
	}

	public List<String> getMarkings() {
		return m_markings.getIdentifierList();
	}
	
	public boolean containsPlace(String place) {
		return m_markings.getIdentifierList().contains(place);
	}

}
