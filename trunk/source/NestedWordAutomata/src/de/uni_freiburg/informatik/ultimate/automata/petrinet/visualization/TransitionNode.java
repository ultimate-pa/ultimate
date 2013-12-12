package de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.Transition;
import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.annotation.DefaultAnnotations;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;

/**
 * Ultimate model of a PetriNet transition.
 * @author heizmann@informatik.uni-freiburg.de 
 */

public class TransitionNode extends PetriNetVisualizationNode {

	private static final long serialVersionUID = -2531826841396458461L;
	
	public TransitionNode(Transition<?,?> transition) {
		super(transition.getSymbol().toString());
		
		IPayload payload = this.getPayload(); 
		DefaultAnnotations thisPluginsAnnotations = new DefaultAnnotations();
		thisPluginsAnnotations.put("hashCode",transition.hashCode());
		HashMap<String,IAnnotations> annotations = payload.getAnnotations();
		annotations.put(Activator.PLUGIN_ID, thisPluginsAnnotations);
		
		if (transition.getSymbol() instanceof IAnnotations) {
			thisPluginsAnnotations.put("Symbol", (IAnnotations) transition.getSymbol());

		}
	}

}
