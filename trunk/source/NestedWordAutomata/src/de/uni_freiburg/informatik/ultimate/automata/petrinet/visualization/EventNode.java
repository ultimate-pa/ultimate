package de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.Event;
import de.uni_freiburg.informatik.ultimate.model.annotation.DefaultAnnotations;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;

/**
 * Ultimate model of a OcurrenceNet event.
 * @author heizmann@informatik.uni-freiburg.de 
 */

public class EventNode<S,C> extends PetriNetVisualizationNode {

	private static final long serialVersionUID = -2531826841396458461L;
	
	
	public EventNode(Event<S,C> event) {
		super(event.getTransition().getSymbol().toString());
		
		DefaultAnnotations annot = new DefaultAnnotations();
		annot.put("Transition",event.getTransition());
		annot.put("Companion", event.getCompanion());
		annot.put("Ancestors", event.getAncestors());
		annot.put("ByLocalConfigurationRepresentedMarking",event.getMark());
	
		HashMap<String,IAnnotations> annotations =  this.getPayload().getAnnotations();
		annotations.put(Activator.PLUGIN_ID, annot);
		
		S symbol = event.getTransition().getSymbol();
		if (symbol instanceof IAnnotations) {
			annot.put("Symbol", (IAnnotations) symbol);

		}
		
	}


}
