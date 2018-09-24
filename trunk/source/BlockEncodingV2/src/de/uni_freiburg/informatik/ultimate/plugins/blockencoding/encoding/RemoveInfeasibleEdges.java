/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BlockEncodingV2 plug-in.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncodingV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncodingV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BlockEncodingV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.blockencoding.encoding;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.BlockEncodingBacktranslator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;

public class RemoveInfeasibleEdges extends BaseBlockEncoder<IcfgLocation> {

	public RemoveInfeasibleEdges(final IUltimateServiceProvider services,
			final BlockEncodingBacktranslator backtranslator, final ILogger logger) {
		super(logger, services, backtranslator);
	}

	@Override
	protected BasicIcfg<IcfgLocation> createResult(final BasicIcfg<IcfgLocation> icfg) {
		final Deque<IcfgEdge> edges = new ArrayDeque<>();
		final Set<IcfgEdge> closed = new HashSet<>();

		edges.addAll(icfg.getInitialNodes().stream().flatMap(a -> a.getOutgoingEdges().stream())
				.collect(Collectors.toSet()));

		while (!edges.isEmpty()) {
			final IcfgEdge current = edges.removeFirst();
			if (!closed.add(current)) {
				continue;
			}
			edges.addAll(current.getTarget().getOutgoingEdges());
			checkEdge(current);
		}

		removeDisconnectedLocations(icfg);
		mLogger.info("Removed " + mRemovedEdges + " edges and " + mRemovedLocations
				+ " locations because of local infeasibility");
		return icfg;
	}

	private void checkEdge(final IcfgEdge edge) {
		if (edge instanceof IIcfgCallTransition<?> || edge instanceof IIcfgReturnTransition<?, ?>) {
			return;
		}

		final Infeasibility result = edge.getTransformula().isInfeasible();

		switch (result) {
		case INFEASIBLE:
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("Removing " + result + ": " + edge);
			}
			removeEdge(edge);
			break;
		case NOT_DETERMINED:
		case UNPROVEABLE:
			break;
		default:
			throw new IllegalArgumentException();
		}
	}

	private void removeEdge(final IcfgEdge edge) {
		edge.disconnectSource();
		edge.disconnectTarget();
		mRemovedEdges++;
	}

	@Override
	public boolean isGraphStructureChanged() {
		return mRemovedEdges > 0 || mRemovedLocations > 0;
	}

}
