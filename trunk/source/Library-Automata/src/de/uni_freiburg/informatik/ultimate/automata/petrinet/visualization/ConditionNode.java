/*
 * Copyright (C) 2009-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
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
