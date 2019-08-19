/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ReachingDefinitions plug-in.
 *
 * The ULTIMATE ReachingDefinitions plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ReachingDefinitions plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ReachingDefinitions plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ReachingDefinitions plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ReachingDefinitions plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;

/**
 *
 * @author dietsch
 *
 */
public class AssumeFinder extends BaseObserver {

	private final ILogger mLogger;
	private final LinkedHashMap<IcfgEdge, List<AssumeStatement>> mEdgesWithAssumes;

	public AssumeFinder(final ILogger logger) {
		mLogger = logger;
		mEdgesWithAssumes = new LinkedHashMap<>();
	}

	@Override
	public boolean process(final IElement root) throws Throwable {
		if (root instanceof BoogieIcfgContainer) {
			final BoogieIcfgContainer rootNode = (BoogieIcfgContainer) root;

			process(rootNode);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("AssumeFinder result (edge.hashCode(), pretty-printed assume statement):");
				for (final IcfgEdge e : mEdgesWithAssumes.keySet()) {
					for (final AssumeStatement ass : mEdgesWithAssumes.get(e)) {
						mLogger.debug(e.hashCode() + " " + BoogiePrettyPrinter.print(ass));
					}
				}
			}
		}
		return false;
	}

	public LinkedHashMap<IcfgEdge, List<AssumeStatement>> getEdgesWithAssumes() {
		return mEdgesWithAssumes;
	}

	private void process(final IcfgLocation node) {
		final Queue<IcfgEdge> openEdges = new LinkedList<>();
		final HashSet<IcfgEdge> completed = new HashSet<>();
		final AssumeFinderVisitor visitor = new AssumeFinderVisitor();

		openEdges.addAll(node.getOutgoingEdges());

		while (!openEdges.isEmpty()) {
			final IcfgEdge current = openEdges.poll();

			visitor.start(current);
			completed.add(current);

			final IcfgLocation target = current.getTarget();
			if (target == null) {
				mLogger.warn("Empty target for edge " + current.hashCode());
				continue;
			}

			for (final IcfgEdge next : target.getOutgoingEdges()) {
				if (!completed.contains(next)) {
					openEdges.add(next);
				}
			}
		}
	}

	private List<AssumeStatement> getAssumeList(final IcfgEdge edge) {
		List<AssumeStatement> rtr = mEdgesWithAssumes.get(edge);
		if (rtr == null) {
			rtr = new ArrayList<>();
			mEdgesWithAssumes.put(edge, rtr);
		}
		return rtr;
	}

	private class AssumeFinderVisitor extends RCFGEdgeVisitor {

		private IcfgEdge mMotherEdge;

		public void start(final IcfgEdge edge) {
			mMotherEdge = edge;
			visit(edge);
		}

		@Override
		protected void visit(final StatementSequence sequence) {
			super.visit(sequence);
			for (final Statement s : sequence.getStatements()) {
				if (s instanceof AssumeStatement) {
					getAssumeList(mMotherEdge).add((AssumeStatement) s);
				}
			}
		}
	}

}
