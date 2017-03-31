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
	
	private final Deque<Deque<IcfgEdge>> mBackbones;
	
	/**
	 * Loop Detector for retrieving loops in a {@link IIcfg}.
	 * 
	 * @param logger
	 * @param originalIcfg
	 */
	
	public LoopDetector(final ILogger logger, final IIcfg<INLOC> originalIcfg) {
		
		mLogger = Objects.requireNonNull(logger);
		
		mLogger.debug("Loop detector constructed.");
		
		mLoopBodies = getLoop(originalIcfg);
		
		mBackbones = null;
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
				
				Deque<IcfgEdge> path = getPath(loopHead);
				loopBodies.add(path);
			}

		} else {
			mLogger.debug("No Loops found.");
		}
		
		mLogger.debug(loopBodies.toString());
		return loopBodies;
	}
	

	private Deque<IcfgEdge> getPath(final IcfgLocation loopHead) {
		
		Deque<IcfgEdge> loopPath = new ArrayDeque<>();
		Deque<IcfgEdge> stack = new ArrayDeque<>();
		
		for (IcfgEdge edge : loopHead.getOutgoingEdges()) {
			stack.push(edge);
		}
		
		while (!stack.isEmpty()) {
			IcfgEdge edge = stack.pop();
			Deque<IcfgEdge> newPath = new ArrayDeque<>(loopPath);
			newPath.addLast(edge);
			
			if (findLoopHeader(newPath, loopHead)) {
				loopPath = newPath;
				if (edge.getTarget() != loopHead) {
					
					// TODO something for nested loops and more than one loop.
					
					for (IcfgEdge transition : edge.getTarget().getOutgoingEdges()) {
						stack.push(transition);
					}
				}
			}
		}
		return loopPath;
	}
	
	/**
	 * Try to find a path back to the loopheader.
	 * If there is one return true, else false.
	 * 
	 * @param path path to check
	 * @param loopHead loopHeader
	 */
	private boolean findLoopHeader(final Deque<IcfgEdge> path, final IcfgLocation loopHead) {
		Deque<IcfgEdge> stack = new ArrayDeque<>();
		Deque<IcfgLocation> visited = new ArrayDeque<>();
		stack.push(path.getLast());
		
		while (!stack.isEmpty()) {
			
			IcfgLocation node = stack.pop().getTarget();

			for (IcfgLocation successor : node.getOutgoingNodes()) {
				if (successor == loopHead || node == loopHead){
					return true;
				}
				if (!visited.contains(successor)) {
					visited.addLast(successor);
					for (IcfgEdge edge : successor.getOutgoingEdges()) {
						stack.push(edge);
					}
				}
			}
		}
		return false;
	}
	
	@SuppressWarnings("unchecked")
	private Deque<Backbone> getBackbone(final Deque<IcfgEdge> loopBody) {
		Deque<Backbone> backbones = null;
		
		final Deque<IcfgEdge> body = loopBody;
		final IcfgLocation loopHead = loopBody.getFirst().getSource();
		final IcfgEdge initialEdge = loopBody.getFirst();
		
		final Deque<Deque<IcfgEdge>> possibleBackbones = new ArrayDeque<>();
		possibleBackbones.addFirst((Deque<IcfgEdge>) initialEdge);
		
		while (!possibleBackbones.isEmpty()) {
			Deque<IcfgLocation> visited = new ArrayDeque<>();
			Deque<IcfgEdge> backBone = possibleBackbones.pop();
			while (backBone.getLast().getTarget() != loopHead || !visited.contains(backBone.getLast().getTarget())) {
				visited.addLast(backBone.getLast().getTarget());
				
				if (backBone.getLast().getTarget().getOutgoingEdges().size() > 1) {
					for (IcfgEdge edge : backBone.getLast().getTarget().getOutgoingEdges()) {
						Deque<IcfgEdge> newBackbone = backBone;
						newBackbone.addLast(edge);
						possibleBackbones.addLast(newBackbone);
					}
					break;
				}
				
			}
			
		}	
		return backbones;
	}
	
	/**
	 * Get Loop bodies of an {@link IIcfg}.
	 * as a queue of edges
	 * 
	 * @param originalIcfg
	 */
	public Deque<Deque<IcfgEdge>> getLoopBodies(final IIcfg<INLOC> originalIcfg) {
		return mLoopBodies;
	}
	
	public Deque<Deque<IcfgEdge>> getLoopBackbones(Deque<IcfgEdge> loopBody) {
		return mBackbones;
	}
}