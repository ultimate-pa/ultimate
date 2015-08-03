package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;

/**
 * Stores information on a loop stack level, that is: - The loop entry node of
 * the current loop, - The exit edge over which the loop will be left -
 * Iteration counts for loops nested within the current loop
 */
public class LoopStackElement
{
	private final Object m_loopNode;
	private final RCFGEdge m_exitEdge;
	private final Map<Object, Integer> m_iterationCounts = new HashMap<Object, Integer>();

	public LoopStackElement(Object loopNode, RCFGEdge exitEdge)
	{
		m_loopNode = loopNode;
		m_exitEdge = exitEdge;
	}

	public Object getLoopNode()
	{
		return m_loopNode;
	}

	public RCFGEdge getExitEdge()
	{
		return m_exitEdge;
	}

	public int getIterationCount(Object loopNode)
	{
		Integer count = m_iterationCounts.get(loopNode);
		if (count == null) 
		{
			return 0;
		}
		return count.intValue();
	}

	public void increaseIterationCount(Object loopNode)
	{
		m_iterationCounts.put(loopNode, Integer.valueOf(getIterationCount(loopNode) + 1));
	}

	public LoopStackElement copy()
	{
		LoopStackElement result = new LoopStackElement(m_loopNode, m_exitEdge);
		for (Object p : m_iterationCounts.keySet())
		{
			result.m_iterationCounts.put(p, m_iterationCounts.get(p));
		}
		return result;
	}
}