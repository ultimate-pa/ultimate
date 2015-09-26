package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;

/**
 * Stores information on a loop stack level, that is: - The loop entry node of
 * the current loop, - The exit edge over which the loop will be left -
 * Iteration counts for loops nested within the current loop
 */
public class LoopStackElement {
	private final Object m_loopNode;
	private final RCFGEdge m_exitEdge;
	private final RCFGEdge m_entryEdge;
	// private final Map<Object, Integer> m_iterationCounts;
	private int m_iteration_count;

	public LoopStackElement(Object loopNode, RCFGEdge exitEdge,
			RCFGEdge entryEdge) {
		m_loopNode = loopNode;
		m_exitEdge = exitEdge;
		m_entryEdge = entryEdge;
		m_iteration_count = 0;
		// m_iterationCounts = new HashMap<Object, Integer>();
	}

	public Object getLoopNode() {
		return m_loopNode;
	}

	public RCFGEdge getExitEdge() {
		return m_exitEdge;
	}

	public RCFGEdge getEntryEdge() {
		return m_entryEdge;
	}

	// public int getIterationCount(Object loopNode)
	// {
	// Integer count = m_iterationCounts.get(loopNode);
	// if (count == null)
	// {
	// return 0;
	// }
	// return count.intValue();
	// }
	//
	// public void increaseIterationCount(Object loopNode)
	// {
	// m_iterationCounts.put(loopNode,
	// Integer.valueOf(getIterationCount(loopNode) + 1));
	// }

	public int getIterationCount() {
		return m_iteration_count;
	}

	public void increaseIterationCount() {
		m_iteration_count++;
	}

	public LoopStackElement copy() {
		LoopStackElement result = new LoopStackElement(m_loopNode, m_exitEdge,
				m_entryEdge);
		result.m_iteration_count = m_iteration_count;
		// for (Object p : m_iterationCounts.keySet())
		// {
		// result.m_iterationCounts.put(p, m_iterationCounts.get(p));
		// }
		return result;
	}

	@Override
	public String toString() {
		String s = "";
		// if (m_iterationCounts != null)
		// {
		// for (Entry<Object, Integer> entry : m_iterationCounts.entrySet())
		// {
		// if(entry == null)
		// {
		// continue;
		// }
		// s += String.format("<%s, %s>", entry.getKey(), entry.getValue());
		// }
		// }
		if (m_loopNode != null) {
			s += m_loopNode.toString();
		}
		// if (m_exitEdge != null)
		// {
		// s += "(" + m_exitEdge.toString() + ")";
		// }
		if (s.length() == 0) {
			return "*";
		}
		s += "(" + m_iteration_count + ")";
		return "'lse:" + s + "'";
	}
}