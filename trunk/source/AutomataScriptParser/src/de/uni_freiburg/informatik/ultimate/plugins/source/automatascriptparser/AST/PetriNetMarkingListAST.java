/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class PetriNetMarkingListAST extends AtsASTNode {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = -2876076623803821394L;
	private IdentifierListAST m_markings;
	
	public PetriNetMarkingListAST(ILocation loc) {
		super(loc);
		m_markings = new IdentifierListAST(loc);
	}
	
	public PetriNetMarkingListAST(ILocation loc, IdentifierListAST idlist) {
		this(loc);
		m_markings = idlist;
	}

	public List<String> getMarkings() {
		return m_markings.getIdentifierList();
	}
	
	public boolean containsPlace(String place) {
		return m_markings.getIdentifierList().contains(place);
	}

}
