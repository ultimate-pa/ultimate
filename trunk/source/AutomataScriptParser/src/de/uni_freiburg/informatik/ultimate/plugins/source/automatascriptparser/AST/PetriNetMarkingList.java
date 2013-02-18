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
public class PetriNetMarkingList extends AtsASTNode {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = -2876076623803821394L;
	private List<PetriNetMarking> m_markings;
	
	public PetriNetMarkingList() {
		m_markings = new ArrayList<PetriNetMarking>();
	}
	
	public PetriNetMarkingList(PetriNetMarking pm) {
		this();
		m_markings.add(pm);
	}
	
	public void addMarking(PetriNetMarking pm) {
		m_markings.add(pm);
	}

	public List<PetriNetMarking> getMarkings() {
		return m_markings;
	}
	
	public boolean containsPlace(String place) {
		for (PetriNetMarking pm : m_markings) {
			if ((place.equals(pm.getPlace())) || (place.equals(pm.getToken()))) {
				return true;
			}
		}
		return false;
	}

}
