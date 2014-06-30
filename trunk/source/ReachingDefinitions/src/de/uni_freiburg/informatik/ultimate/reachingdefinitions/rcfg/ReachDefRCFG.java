package de.uni_freiburg.informatik.ultimate.reachingdefinitions.rcfg;

import java.util.LinkedHashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.BaseObserver;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.reachingdefinitions.annotations.ReachDefStatementAnnotation;
import de.uni_freiburg.informatik.ultimate.reachingdefinitions.plugin.Activator;
import de.uni_freiburg.informatik.ultimate.reachingdefinitions.util.Util;

/**
 * 
 * {@link ReachDefRCFG} computes a DefUse set that is expressed as
 * {@link ReachDefStatementAnnotation} annotation for each edge of an RCFG.
 * 
 * It makes the following assumptions:
 * <ul>
 * <li>A
 * </ul>
 * 
 * @author dietsch
 * 
 */
public class ReachDefRCFG extends BaseObserver {

	private final Logger mLogger;
	
	public ReachDefRCFG (){
		mLogger = Activator.getLogger();
	}
	
	@Override
	public boolean process(IElement root) throws Throwable {
		if (root instanceof RootNode) {
			RootNode rootNode = (RootNode) root;
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("Loops: " + rootNode.getRootAnnot().getLoopLocations().size());
			}
			process(rootNode);
		}
		return false;
	}

	private void process(RootNode node) throws Throwable {
		LinkedHashSet<RCFGEdge> remaining = new LinkedHashSet<>();

		for (RCFGEdge next : node.getOutgoingEdges()) {
			remaining.add(next);
		}

		while (!remaining.isEmpty()) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("");
				mLogger.debug(" 		              Open: "
						+ Util.prettyPrintIterable(remaining, Util.<RCFGEdge> createHashCodePrinter()));
			}
			RCFGEdge current = remaining.iterator().next();
			remaining.remove(current);
			ReachDefRCFGVisitor v = new ReachDefRCFGVisitor();

			boolean fxpReached = v.process(current);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(" 		              Fixpoint reached: " + fxpReached);
			}
			if (!fxpReached) {
				for (RCFGEdge next : current.getTarget().getOutgoingEdges()) {
					remaining.add(next);
				}
			}
		}
	}
}
