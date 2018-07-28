/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
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
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;

/**
 * Ultimate model of a OccurenceNet condition.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <S>
 *            symbol type
 * @param <C>
 *            place content type
 */
public final class ConditionNode<S, C> extends PetriNetVisualizationNode {
	private static final long serialVersionUID = 264254789648279608L;

	/**
	 * @param condition
	 *            Condition.
	 * @param branchingProcess
	 *            branching process
	 */
	public ConditionNode(final Condition<S, C> condition, final BranchingProcess<S, C> branchingProcess) {
		super(condition.toString());

		final DefaultAnnotations annot = new DefaultAnnotations();
		annot.put("Condition", mName);
		annot.put("CorrespondingPlace", condition.getPlace());
		annot.put("NumberSuccesorEvents", condition.getSuccessorEvents().size());
		annot.put("AllConditionsInCoRelation", allConditionsInCoRelation(condition, branchingProcess));
		final Map<String, IAnnotations> annotations = getPayload().getAnnotations();
		annotations.put(LibraryIdentifiers.PLUGIN_ID, annot);

		final C content = condition.getPlace();
		if (content instanceof IAnnotations) {
			annot.put("Content", content);

		}
		// super.setPayload(payload);
	}

	private ArrayList<Condition<S, C>> allConditionsInCoRelation(final Condition<S, C> condition,
			final BranchingProcess<S, C> bc) {
		final ArrayList<Condition<S, C>> conditionsInCoRelation = new ArrayList<>();
		for (final Condition<S, C> c : bc.getConditions()) {
			if (bc.isInCoRelation(condition, c)) {
				conditionsInCoRelation.add(c);
			}
		}
		return conditionsInCoRelation;
	}
}
