package de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization;

import java.util.ArrayList;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.Condition;
import de.uni_freiburg.informatik.ultimate.model.annotation.DefaultAnnotations;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;

/**
 * Ultimate model of a OccurenceNet condition.
 * @author heizmann@informatik.uni-freiburg.de 
 */

public class ConditionNode<S,C> extends PetriNetVisualizationNode {
	/**
	 * 
	 */
	private static final long serialVersionUID = 264254789648279608L;
	
	public ConditionNode(Condition<S,C> condition, BranchingProcess<S,C> bc) {
		super(condition.toString());
		
		DefaultAnnotations annot = new DefaultAnnotations();
		annot.put("Condition",condition.toString());
		annot.put("CorrespondingPlace",condition.getPlace());
		annot.put("NumberSuccesorEvents", condition.getSuccessorEvents().size());
		annot.put("AllConditionsInCoRelation", allConditionsInCoRelation(condition,bc));
		HashMap<String,IAnnotations> annotations = this.getPayload().getAnnotations();
		annotations.put(Activator.PLUGIN_ID, annot);
		
		C content = condition.getPlace().getContent();
		if (content instanceof IAnnotations) {
			annot.put("Content", (IAnnotations) content);

		}
//		super.setPayload(payload);
	}
	
	private ArrayList<Condition<S,C>> allConditionsInCoRelation(Condition<S,C> condition, BranchingProcess<S,C> bc) {
		ArrayList<Condition<S,C>> conditionsInCoRelation = new ArrayList<Condition<S,C>>();
		for (Condition<S,C> c : bc.getConditions()) {
			if (bc.isInCoRelation(condition, c)) {
				conditionsInCoRelation.add(c);
			}
		}
		return conditionsInCoRelation;
	}
	
	

}
