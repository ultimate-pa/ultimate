/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.algorithm;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;

/**
 * @author Stefan Wissert
 * 
 */
public class PrintEdgeVisitor extends AbstractMinimizationVisitor {

	public PrintEdgeVisitor(Logger logger) {
		super(logger);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.
	 * AbstractRCFGVisitor
	 * #applyMinimizationRules(de.uni_freiburg.informatik.ultimate
	 * .blockencoding.model.MinimizedNode)
	 */
	@Override
	protected MinimizedNode[] applyMinimizationRules(MinimizedNode node) {
		for (IMinimizedEdge edge : node.getMinimalOutgoingEdgeLevel()) {
			s_Logger.debug("Visit Edge: " + edge.toString());
		}
		return new MinimizedNode[0];
	}

}
