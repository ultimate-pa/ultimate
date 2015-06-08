package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton;

import java.util.Iterator;
import java.util.Set;
import java.util.Stack;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

public class SccComputationNonRecursive<NODE, COMP extends StronglyConnectedComponent<NODE>> extends SccComputation<NODE, COMP> {
	
	public SccComputationNonRecursive(
			IUltimateServiceProvider services,
			Logger logger,
			de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.SccComputation.ISuccessorProvider<NODE> successorProvider,
			de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.SccComputation.IStronglyConnectedComponentFactory<NODE, COMP> sccFac,
			int numberOfAllNodes, Set<NODE> startNodes) {
		super(services, logger, successorProvider, sccFac, numberOfAllNodes, startNodes);
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
//				if (m_NoScc.size() >= 1000) {
////					throw new AssertionError("contains on stack with 1000 elements is inefficient");
//				}
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
