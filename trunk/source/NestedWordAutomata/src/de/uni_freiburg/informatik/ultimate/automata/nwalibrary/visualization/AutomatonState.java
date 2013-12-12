package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.visualization;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.model.annotation.DefaultAnnotations;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.structure.ModifiableExplicitEdgesMultigraph;

/**
 * Ultimate model of an automaton state.
 * @author heizmann@informatik.uni-freiburg.de 
 */

public class AutomatonState extends ModifiableExplicitEdgesMultigraph<AutomatonState, AutomatonTransition> {
	private static final long serialVersionUID = 264254789648279608L;
	
	private final String m_Name;
	
	public AutomatonState(Object content, boolean isAccepting) {
		
		DefaultAnnotations acceptance = new DefaultAnnotations();
		acceptance.put("isAccepting",isAccepting);
		HashMap<String,IAnnotations> annotations = getPayload().getAnnotations();
		annotations.put("isAccepting", acceptance);
		
		if (content instanceof IAnnotations) {
			annotations.put("Content", (IAnnotations) content);
		}
		
		m_Name = String.valueOf(content);
	}
	
	public String toString() {
		return m_Name;
	}

}
