/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE IRSDependencies plug-in.
 * 
 * The ULTIMATE IRSDependencies plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE IRSDependencies plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IRSDependencies plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IRSDependencies plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE IRSDependencies plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.walker;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

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
	protected Queue<IcfgEdge> mRemainingEdges;
	protected HashSet<IcfgEdge> mProcessedEdges;

	public RCFGWalkerBreadthFirst(ObserverDispatcher dispatcher, ILogger logger)
	{
		super(dispatcher, logger);
		mRemainingEdges = new LinkedList<>();
		mProcessedEdges = new HashSet<>();
	}

	@Override
	public void startFrom(final Collection<IcfgEdge> startEdges) {
//		level(node);
//		for (final IcfgEdge edge : node.getOutgoingEdges()) {
//			mRemainingEdges.add(edge);
//		}
		mRemainingEdges.addAll(startEdges);
		processMethods();
	}

	protected void processMethods()
	{
		while (!mRemainingEdges.isEmpty()) {
			if(mDispatcher.abortAll()){
				return;
			}
			
			final IcfgEdge currentEdge = mRemainingEdges.poll();
			level(currentEdge);
			mProcessedEdges.add(currentEdge);

			final IcfgLocation currentNode = currentEdge.getTarget();
			level(currentNode);
			
			if(mDispatcher.abortCurrentBranch()){
				continue;
			}

			for (final IcfgEdge nextEdge : currentNode.getOutgoingEdges()) {
				if (!mProcessedEdges.contains(nextEdge)) {
					mRemainingEdges.add(nextEdge);
				}
			}

		}
	}

}
