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
 * @param <S>
 *            symbol type
 * @param <C>
 *            place content type
 */
public class BranchingProcessToUltimateModel<S, C> {
	/**
	 * @param branchingProcess
	 *            Branching process.
	 * @return the initial node of the Branching process Ultimate model
	 */
	@SuppressWarnings("unchecked")
	public IElement transformToUltimateModel(final BranchingProcess<S, C> branchingProcess) {
		final BranchingProcessInitialNode<S, C> graphroot = new BranchingProcessInitialNode<>(branchingProcess);

		final Collection<Condition<S, C>> initialStates = branchingProcess.initialConditions();
		// Collection<Event<S,C>> cutOffEvents = net.getCutOffEvents();

		final Map<Condition<S, C>, ConditionNode<S, C>> place2ConditionNode = new HashMap<>();
		final Map<Event<S, C>, EventNode<S, C>> transition2EventNode = new HashMap<>();

		final Queue<Object> queue = new LinkedList<>(initialStates);

		// add all initial states to model - all are successors of the graphroot
		for (final Condition<S, C> place : initialStates) {
			final ConditionNode<S, C> conditionNode = new ConditionNode<>(place, branchingProcess);
			place2ConditionNode.put(place, conditionNode);
			graphroot.connectOutgoing(conditionNode);
		}

		while (!queue.isEmpty()) {
			final Object node = queue.remove();

			if (node instanceof Condition) {
				conditionHandling(place2ConditionNode, transition2EventNode, queue, (Condition<S, C>) node);
			} else if (node instanceof Event) {
				eventHandling(branchingProcess, place2ConditionNode, transition2EventNode, queue, (Event<S, C>) node);
			}
		}
		return graphroot;
	}

	private void conditionHandling(final Map<Condition<S, C>, ConditionNode<S, C>> place2ConditionNode,
			final Map<Event<S, C>, EventNode<S, C>> transition2EventNode, final Queue<Object> queue,
			final Condition<S, C> place) {
		final ConditionNode<S, C> conditionNode = place2ConditionNode.get(place);
		for (final Event<S, C> transition : place.getSuccessorEvents()) {
			EventNode<S, C> transNode = transition2EventNode.get(transition);
			if (transNode == null) {
				transNode = new EventNode<>(transition);
				transition2EventNode.put(transition, transNode);
				queue.add(transition);
			}
			conditionNode.connectOutgoing(transNode);
		}
	}

	private void eventHandling(final BranchingProcess<S, C> branchingProcess,
			final Map<Condition<S, C>, ConditionNode<S, C>> place2ConditionNode,
			final Map<Event<S, C>, EventNode<S, C>> transition2EventNode, final Queue<Object> queue,
			final Event<S, C> transition) {
		final EventNode<S, C> eventNode = transition2EventNode.get(transition);
		for (final Condition<S, C> place : transition.getSuccessorConditions()) {
			ConditionNode<S, C> conditionNode = place2ConditionNode.get(place);
			if (conditionNode == null) {
				conditionNode = new ConditionNode<>(place, branchingProcess);
				place2ConditionNode.put(place, conditionNode);
				queue.add(place);
			}
			eventNode.connectOutgoing(conditionNode);
		}
	}
}
