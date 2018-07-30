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

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

/**
 * Converter from {@link BranchingProcess} to Ultimate model.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            symbol type
 * @param <PLACE>
 *            place content type
 */
public class BranchingProcessToUltimateModel<LETTER, PLACE> {
	/**
	 * @param branchingProcess
	 *            Branching process.
	 * @return the initial node of the Branching process Ultimate model
	 */
	@SuppressWarnings("unchecked")
	public IElement transformToUltimateModel(final BranchingProcess<LETTER, PLACE> branchingProcess) {
		final BranchingProcessInitialNode<LETTER, PLACE> graphroot = new BranchingProcessInitialNode<>(branchingProcess);

		final Collection<Condition<LETTER, PLACE>> initialStates = branchingProcess.initialConditions();
		// Collection<Event<S,C>> cutOffEvents = net.getCutOffEvents();

		final Map<Condition<LETTER, PLACE>, ConditionNode<LETTER, PLACE>> place2ConditionNode = new HashMap<>();
		final Map<Event<LETTER, PLACE>, EventNode<LETTER, PLACE>> transition2EventNode = new HashMap<>();

		final Queue<Object> queue = new LinkedList<>(initialStates);

		// add all initial states to model - all are successors of the graphroot
		for (final Condition<LETTER, PLACE> place : initialStates) {
			final ConditionNode<LETTER, PLACE> conditionNode = new ConditionNode<>(place, branchingProcess);
			place2ConditionNode.put(place, conditionNode);
			graphroot.connectOutgoing(conditionNode);
		}

		while (!queue.isEmpty()) {
			final Object node = queue.remove();

			if (node instanceof Condition) {
				conditionHandling(place2ConditionNode, transition2EventNode, queue, (Condition<LETTER, PLACE>) node);
			} else if (node instanceof Event) {
				eventHandling(branchingProcess, place2ConditionNode, transition2EventNode, queue, (Event<LETTER, PLACE>) node);
			}
		}
		return graphroot;
	}

	private void conditionHandling(final Map<Condition<LETTER, PLACE>, ConditionNode<LETTER, PLACE>> place2ConditionNode,
			final Map<Event<LETTER, PLACE>, EventNode<LETTER, PLACE>> transition2EventNode, final Queue<Object> queue,
			final Condition<LETTER, PLACE> place) {
		final ConditionNode<LETTER, PLACE> conditionNode = place2ConditionNode.get(place);
		for (final Event<LETTER, PLACE> transition : place.getSuccessorEvents()) {
			EventNode<LETTER, PLACE> transNode = transition2EventNode.get(transition);
			if (transNode == null) {
				transNode = new EventNode<>(transition);
				transition2EventNode.put(transition, transNode);
				queue.add(transition);
			}
			conditionNode.connectOutgoing(transNode);
		}
	}

	private void eventHandling(final BranchingProcess<LETTER, PLACE> branchingProcess,
			final Map<Condition<LETTER, PLACE>, ConditionNode<LETTER, PLACE>> place2ConditionNode,
			final Map<Event<LETTER, PLACE>, EventNode<LETTER, PLACE>> transition2EventNode, final Queue<Object> queue,
			final Event<LETTER, PLACE> transition) {
		final EventNode<LETTER, PLACE> eventNode = transition2EventNode.get(transition);
		for (final Condition<LETTER, PLACE> place : transition.getSuccessorConditions()) {
			ConditionNode<LETTER, PLACE> conditionNode = place2ConditionNode.get(place);
			if (conditionNode == null) {
				conditionNode = new ConditionNode<>(place, branchingProcess);
				place2ConditionNode.put(place, conditionNode);
				queue.add(place);
			}
			eventNode.connectOutgoing(conditionNode);
		}
	}
}
