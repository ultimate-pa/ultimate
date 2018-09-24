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

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.BlockEncodingBacktranslator;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class Simplifier extends BaseBlockEncoder<IcfgLocation> {

	private final IcfgEdgeBuilder mEdgeBuilder;

	public Simplifier(final IcfgEdgeBuilder edgeBuilder, final IUltimateServiceProvider services,
			final BlockEncodingBacktranslator backtranslator, final ILogger logger) {
		super(logger, services, backtranslator);
		mEdgeBuilder = edgeBuilder;
	}

	@Override
	protected BasicIcfg<IcfgLocation> createResult(final BasicIcfg<IcfgLocation> icfg) {
		mLogger.info("Simplifying codeblocks");

		final Deque<IcfgEdge> edges = new ArrayDeque<>();
		final Set<IcfgEdge> closed = new HashSet<>();
		icfg.getProcedureEntryNodes().values().stream().forEach(a -> edges.addAll(a.getOutgoingEdges()));

		while (!edges.isEmpty()) {
			final IcfgEdge current = edges.removeFirst();
			if (!closed.add(current)) {
				continue;
			}
			if (current instanceof IIcfgCallTransition<?> || current instanceof IIcfgReturnTransition<?, ?>) {
				continue;
			}
			edges.addAll(current.getTarget().getOutgoingEdges());
			final IcfgEdge seqComp = mEdgeBuilder.constructSimplifiedSequentialComposition(current.getSource(),
					current.getTarget(), current);
			rememberEdgeMapping(seqComp, current);
			current.disconnectSource();
			current.disconnectTarget();
		}
		return icfg;
	}

	@Override
	public boolean isGraphStructureChanged() {
		return false;
	}
}
