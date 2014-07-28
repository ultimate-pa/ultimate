package de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.walker;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

/**
 * This walker traverses RCFG-graphs in breadth-first order with incoming edges
 * and nodes as one unit. I.e. an observer sees (root node -> root edge, program
 * point -> some edge, program point -> ...). No edge is traversed twice.
 * 
 * @author dietsch
 * 
 */
public class RCFGWalkerBreadthFirst extends RCFGWalker
{
	protected Queue<RCFGEdge> mRemainingEdges;
	protected HashSet<RCFGEdge> mProcessedEdges;

	public RCFGWalkerBreadthFirst(ObserverDispatcher dispatcher, Logger logger)
	{
		super(dispatcher, logger);
		mRemainingEdges = new LinkedList<>();
		mProcessedEdges = new HashSet<>();
	}

	public void processProgram(RootNode node)
	{
		level(node);
		for (RCFGEdge edge : node.getOutgoingEdges()) {
			mRemainingEdges.add(edge);
		}
		processMethods();
	}

	protected void processMethods()
	{
		while (!mRemainingEdges.isEmpty()) {
			if(mDispatcher.abortAll()){
				return;
			}
			
			RCFGEdge currentEdge = mRemainingEdges.poll();
			level(currentEdge);
			mProcessedEdges.add(currentEdge);

			RCFGNode currentNode = currentEdge.getTarget();
			level(currentNode);
			
			if(mDispatcher.abortCurrentBranch()){
				continue;
			}

			for (RCFGEdge nextEdge : currentNode.getOutgoingEdges()) {
				if (!mProcessedEdges.contains(nextEdge)) {
					mRemainingEdges.add(nextEdge);
				}
			}

		}
	}

}
