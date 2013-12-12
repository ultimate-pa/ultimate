package de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.model.annotation.DefaultAnnotations;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;

/**
 * Ultimate model of a PetriNet place.
 * @author heizmann@informatik.uni-freiburg.de 
 */

public class BranchingProcessInitialNode<S,C> extends PetriNetVisualizationNode {
	/**
	 * 
	 */
	private static final long serialVersionUID = 264254789648279608L;
	
	public BranchingProcessInitialNode(BranchingProcess<S,C> net) {
		super("My sucessors are the initial conditions");
		
		IAnnotations thisPluginsAnnotations = new DefaultAnnotations();
//		thisPluginsAnnotations.put("Places2Conditions",net.getPlace2Conditions());
//		thisPluginsAnnotations.put("Markings2Events",net.getMarkings2Events());
//		thisPluginsAnnotations.put("CutOffEvents",net.getCutOffEvents());
		HashMap<String,IAnnotations> annotations = this.getPayload().getAnnotations(); 
		annotations.put(Activator.PLUGIN_ID, thisPluginsAnnotations);
		
	}
	


}
