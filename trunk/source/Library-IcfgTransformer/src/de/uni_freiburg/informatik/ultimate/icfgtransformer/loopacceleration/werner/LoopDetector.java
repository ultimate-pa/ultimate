package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Objects;
import java.util.Set;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * Extracts the loops from an {@link IIcfg}.
 *
 * @param <INLOC>
 *
 * @author Jonas Werner (jonaswerner95@gmail.com)
 */

public class LoopDetector<INLOC extends IcfgLocation> {
	
	private final ILogger mLogger;
	private final Deque<Deque<IcfgEdge>> mLoopBodies;
	
	/**
	 * Get Loop bodies of an {@link IIcfg}.
	 * 
	 * @param logger
	 * @param originalIcfg
	 */
	
	public LoopDetector(final ILogger logger, final IIcfg<INLOC> originalIcfg) {
		
		mLogger = Objects.requireNonNull(logger);
		
		mLogger.debug("Detecting loops...");
		
		mLoopBodies = getLoop(originalIcfg);
	}
	
	/**
	 * Get Loop bodies of an {@link IIcfg}.
	 * as a queue of edges
	 * 
	 * @param logger
	 * @param originalIcfg
	 */
	private Deque<Deque<IcfgEdge>> getLoop(final IIcfg<INLOC> originalIcfg) {
		
		final Set<INLOC> loopHeads = originalIcfg.getLoopLocations();
		final Deque<Deque<IcfgEdge>> loopBodies = new ArrayDeque<>();
		
		if (!loopHeads.isEmpty()) {
			mLogger.debug("Loops found.");
			for (INLOC loopHead : loopHeads) {
				Deque<IcfgEdge> path = new ArrayDeque<>();
				for (IcfgEdge edge : loopHead.getOutgoingEdges()) {
					path.addLast(edge);
				}
				path = getPath(path);
				loopBodies.add(path);
			}

		} else {
			mLogger.debug("No Loops found.");
		}
		
		mLogger.debug(loopBodies.toString());
		return loopBodies;
	}
	

	private Deque<IcfgEdge> getPath(Deque<IcfgEdge> path) {
		for (IcfgEdge edge : path) {
			
			if (edge.getTarget() == path.getFirst().getSource()) {
				path.addLast(edge);
				return path;
			}
			
			Deque<IcfgEdge> newPath = new ArrayDeque<>(path);
			newPath.addLast(edge);
			
			if (findLoopHeader(newPath)) {
				path = newPath;
			}
			
			// mLogger.debug(edge.getTarget().toString());
		}
		return path;
	}
	
	@SuppressWarnings("unchecked")
	private boolean findLoopHeader(final Deque<IcfgEdge> path) {
		Deque<IcfgEdge> stack = new ArrayDeque<>();
		Deque<INLOC> visited = new ArrayDeque<>();
		stack.push(path.getLast());
		
		while (!stack.isEmpty()) {
			IcfgLocation node = stack.pop().getSource();
			for (IcfgLocation successor : node.getOutgoingNodes()) {
				if (successor == path.getFirst().getSource()) {
					return true;
				}
				if (!visited.contains(successor)) {
					visited.addLast((INLOC) successor);
					for (IcfgEdge edge : successor.getOutgoingEdges()) {
						stack.push(edge);
					}
				}
			}
		}
		return false;
	}
	
	public Deque<Deque<IcfgEdge>> getLoopBodies() {
		return mLoopBodies;
	}
}
