/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.algorithm;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.plugins.generator.blockendcoding.Activator;

/**
 * @author Stefan Wissert
 * 
 */
public class PrintEdgeVisitor extends AbstractMinimizationVisitor {

	private static Logger s_Logger;

	public PrintEdgeVisitor() {
		super();
		s_Logger = UltimateServices.getInstance().getLogger(
				Activator.s_PLUGIN_ID);
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
