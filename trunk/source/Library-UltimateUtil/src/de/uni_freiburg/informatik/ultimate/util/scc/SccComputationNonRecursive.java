/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Util Library.
 * 
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Util Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.scc;

import java.util.Iterator;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.core.services.model.ILogger;

/**
 * Non-recursive implementation of {@link SccComputation}.
 * @author Matthias Heizmann
 *
 * @param <NODE>
 */
public class SccComputationNonRecursive<NODE, COMP extends StronglyConnectedComponent<NODE>> extends SccComputation<NODE, COMP> {
	
	public SccComputationNonRecursive(
			ILogger logger,
			ISuccessorProvider<NODE> successorProvider,
			IStronglyConnectedComponentFactory<NODE, COMP> sccFac,
			int numberOfAllNodes, Set<NODE> startNodes) {
		super(logger, successorProvider, sccFac, numberOfAllNodes, startNodes);
	}
	
	
	@Override
	protected void strongconnect(NODE v) {
		Stack<TodoStackElement> todoStack = new Stack<>();
		todoStack.push(new TodoStackElement(v, null));
		while (!todoStack.isEmpty()) {
			TodoStackElement todoStackElement = todoStack.pop();
			switch (todoStackElement.getTask()) {
			case INDEX:
				if (m_Indices.containsKey(todoStackElement.getNode())) {
					// do nothing
				} else {
					doIndex(todoStackElement.getNode());
					todoStackElement.reportTaskAccomplished();
					todoStack.push(todoStackElement);
				}
				break;
			case GET_SUCCESSORS:
				todoStackElement.reportTaskAccomplished();
				todoStack.push(todoStackElement);
				doGetSuccessors(todoStackElement.getNode(), todoStack);
				break;
			case SET_LOWLINK:
				doSetLowlink(todoStackElement.getNode(), todoStackElement.getPredecessor());
				break;
			default:
				throw new AssertionError();
			}
		}
	}


	private void doSetLowlink(NODE node, NODE predecessor) {
		if (m_LowLinks.get(node).equals(m_Indices.get(node))) {
			establishNewComponent(node);
		}
		if (predecessor == null) {
			// node is first element, do nothing
		} else {
			updateLowlink(predecessor, m_LowLinks.get(node));
		}
	}


	private void doGetSuccessors(NODE node, Stack<TodoStackElement> todoStack) {
		Iterator<NODE> it = m_SuccessorProvider.getSuccessors(node);
		while(it.hasNext()) {
			NODE succ = it.next();
			if (m_Indices.containsKey(succ)) {
				if (m_NoScc.contains(succ)) {
					updateLowlink(node, m_Indices.get(succ));
				}
			} else {
				todoStack.push(new TodoStackElement(succ, node));
			}
		}
	}


	private void doIndex(NODE node) {
		assert (!m_Indices.containsKey(node));
		assert (!m_LowLinks.containsKey(node));
		m_Indices.put(node, m_Index);
		m_LowLinks.put(node, m_Index);
		m_Index++;
		m_NoScc.push(node);
	}


	enum NextTask { INDEX, GET_SUCCESSORS, SET_LOWLINK };
	private class TodoStackElement {
		
		private final NODE m_Node;
		private NextTask m_Task;
		private final NODE m_Predecessor;
		public TodoStackElement(NODE node, NODE predecessor) {
			super();
			m_Node = node;
			m_Task = NextTask.INDEX;
			m_Predecessor = predecessor;
		}
		public void reportTaskAccomplished() {
			switch (m_Task) {
			case INDEX:
				m_Task = NextTask.GET_SUCCESSORS;
				break;
			case GET_SUCCESSORS:
				m_Task = NextTask.SET_LOWLINK;
				break;
			case SET_LOWLINK:
				throw new IllegalStateException("SET_LOWLINK is last task");
			default:
				throw new AssertionError();
			}
		}
		public NODE getNode() {
			return m_Node;
		}
		public NextTask getTask() {
			return m_Task;
		}
		public NODE getPredecessor() {
			return m_Predecessor;
		}
		@Override
		public String toString() {
			return "TodoStackElement [m_Node=" + m_Node + ", m_Task=" + m_Task
					+ ", m_Predecessor=" + m_Predecessor + "]";
		}
		
	}
}