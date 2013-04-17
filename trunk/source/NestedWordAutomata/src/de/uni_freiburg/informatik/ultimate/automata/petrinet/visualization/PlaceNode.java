package de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization;

import java.util.Collection;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.model.DefaultAnnotations;
import de.uni_freiburg.informatik.ultimate.model.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.IPayload;

/**
 * Ultimate model of a PetriNet place.
 * @author heizmann@informatik.uni-freiburg.de 
 */

public class PlaceNode extends PetriNetVisualizationNode {

	private static final long serialVersionUID = 7581148770748066703L;

	public PlaceNode(Place<?,?> place, 
							Collection<String> participatedAcceptingMarkings) {
		super(place.getContent().toString());
		
		IPayload payload = this.getPayload();
		DefaultAnnotations thisPluginsAnnotations = new DefaultAnnotations();
		thisPluginsAnnotations.put("accepting markings containing this place",
				participatedAcceptingMarkings);
		thisPluginsAnnotations.put("toString",place.toString());
		thisPluginsAnnotations.put("hashCode",place.hashCode());
		HashMap<String,IAnnotations> annotations = payload.getAnnotations();
		annotations.put(Activator.PLUGIN_ID, thisPluginsAnnotations);
		
		if (place.getContent() instanceof IAnnotations) {
			thisPluginsAnnotations.put("Content", (IAnnotations) place.getContent());
		}
	}
	
	

}
