package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.visualization;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.AbstractEdgeNode;
import de.uni_freiburg.informatik.ultimate.model.DefaultAnnotations;
import de.uni_freiburg.informatik.ultimate.model.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.Payload;
import de.uni_freiburg.informatik.ultimate.model.structure.BaseExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.model.structure.ModifiableExplicitEdgesMultigraph;

/**
 * Ultimate model of an automaton state.
 * @author heizmann@informatik.uni-freiburg.de 
 */

public class AutomatonState extends ModifiableExplicitEdgesMultigraph<AutomatonState, AutomatonTransition> {
	/**
	 * 
	 */
	private static final long serialVersionUID = 264254789648279608L;
	private List<IEdge> incoming = new ArrayList<IEdge>();
	private List<IEdge> outgoing = new ArrayList<IEdge>();
	
	public AutomatonState(Object content, boolean isAccepting) {
		
		IPayload payload = super.getPayload();
		DefaultAnnotations acceptance = new DefaultAnnotations();
		acceptance.put("isAccepting",isAccepting);
		HashMap<String,IAnnotations> annotations = 
				new HashMap<String,IAnnotations>();
		annotations.put("isAccepting", acceptance);
		
		if (content instanceof IAnnotations) {
			annotations.put("Content", (IAnnotations) content);

		}
		if (content != null) {
			payload.setName(content.toString());
		}
		payload.setAnnotations(annotations);
	}
	
	public String toString() {
		return super.getPayload().getName();
	}

}
