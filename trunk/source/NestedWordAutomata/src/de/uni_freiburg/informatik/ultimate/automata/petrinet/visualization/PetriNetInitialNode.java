package de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization;

import java.util.Collection;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.model.DefaultAnnotations;
import de.uni_freiburg.informatik.ultimate.model.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.IPayload;

/**
 * Ultimate model of a PetriNet place.
 * @author heizmann@informatik.uni-freiburg.de 
 */

public class PetriNetInitialNode extends PetriNetVisualizationNode {
	private static final long serialVersionUID = 264254789648279608L;
	
	public PetriNetInitialNode(Collection<String> acceptingMarkings) {
		super("My sucessors are the initial marking");
		
		IPayload payload = this.getPayload();
		DefaultAnnotations thisPluginsAnnotations = new DefaultAnnotations();
		thisPluginsAnnotations.put("accepting markings of this petri net",
				acceptingMarkings);
		HashMap<String,IAnnotations> annotations = payload.getAnnotations();
		annotations.put(Activator.PLUGIN_ID, thisPluginsAnnotations);
	}
	
}
