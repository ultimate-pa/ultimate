/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BuchiProgramProduct plug-in.
 *
 * The ULTIMATE BuchiProgramProduct plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BuchiProgramProduct plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiProgramProduct plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiProgramProduct plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BuchiProgramProduct plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class RemoveSinkStates extends BaseProductOptimizer {

	public RemoveSinkStates(final RootNode product, final IUltimateServiceProvider services,
			final IToolchainStorage storage) {
		super(product, services, storage);
	}

	@Override
	protected RootNode createResult(final RootNode root) {
		final List<RCFGNode> sinks = collectSinks(root);
		if (mLogger.isDebugEnabled()) {
			mLogger.info("Collected " + sinks.size() + " initial sink states");
		}
		removeSinks(sinks);
		removeDisconnectedLocations(root);
		mLogger.info(
				"Removed " + mRemovedEdges + " edges and " + mRemovedLocations + " locations by removing sink states");
		return root;
	}

	private static List<RCFGNode> collectSinks(final RootNode root) {
		final ArrayList<RCFGNode> rtr = new ArrayList<>();
		final ArrayDeque<RCFGNode> nodes = new ArrayDeque<>();
		final HashSet<RCFGNode> closed = new HashSet<>();
		nodes.addAll(root.getOutgoingNodes());
		while (!nodes.isEmpty()) {
			final RCFGNode current = nodes.removeFirst();
			if (closed.contains(current)) {
				continue;
			}
			closed.add(current);
			if (current.getOutgoingEdges().size() == 0) {
				rtr.add(current);
			} else {
				nodes.addAll(current.getOutgoingNodes());
			}

		}
		return rtr;
	}

	private void removeSinks(final List<RCFGNode> sinks) {
		final ArrayDeque<RCFGNode> nodes = new ArrayDeque<>();
		nodes.addAll(sinks);
		while (!nodes.isEmpty()) {
			final RCFGNode current = nodes.removeFirst();

			if (current.getOutgoingEdges().size() == 0) {
				final ArrayList<RCFGEdge> incoming = new ArrayList<>(current.getIncomingEdges());
				for (final RCFGEdge edge : incoming) {
					nodes.add(edge.getSource());
					edge.disconnectSource();
					edge.disconnectTarget();
					mRemovedEdges++;
				}
			}
		}
	}

	@Override
	public boolean isGraphChanged() {
		return mRemovedEdges > 0 || mRemovedLocations > 0;
	}
}
