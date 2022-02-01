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
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;
import java.util.function.BiPredicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.BlockEncodingBacktranslator;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class RemoveSinkStates extends BaseBlockEncoder<IcfgLocation> {

	private final BiPredicate<IIcfg<?>, IcfgLocation> mFunHasToBePreserved;

	public RemoveSinkStates(final IUltimateServiceProvider services,
			final BiPredicate<IIcfg<?>, IcfgLocation> funHasToBePreserved,
			final BlockEncodingBacktranslator backtranslator, final ILogger logger) {
		super(logger, services, backtranslator);
		mFunHasToBePreserved = funHasToBePreserved;
	}

	@Override
	protected BasicIcfg<IcfgLocation> createResult(final BasicIcfg<IcfgLocation> icfg) {
		final List<IcfgLocation> sinks = collectInitialSinks(icfg);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Collected " + sinks.size() + " initial sink states:");
			sinks.stream().forEach(mLogger::debug);
		}
		disconnectSinks(icfg, sinks);
		removeDisconnectedLocations(icfg);
		mLogger.info(
				"Removed " + mRemovedEdges + " edges and " + mRemovedLocations + " locations by removing sink states");
		return icfg;
	}

	private List<IcfgLocation> collectInitialSinks(final IIcfg<?> icfg) {
		final IcfgLocationIterator<?> iter = new IcfgLocationIterator<>(icfg);
		return iter.asStream().filter(a -> isSink(icfg, a)).collect(Collectors.toList());
	}

	private void disconnectSinks(final IIcfg<?> icfg, final List<IcfgLocation> initialSinks) {
		final Deque<IcfgLocation> sinks = new ArrayDeque<>();
		sinks.addAll(initialSinks);
		while (!sinks.isEmpty()) {
			final IcfgLocation current = sinks.removeFirst();
			assert isSink(icfg, current);
			sinks.addAll(disconnectSink(icfg, current));
		}
	}

	private List<IcfgLocation> disconnectSink(final IIcfg<?> icfg, final IcfgLocation current) {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Removing sink " + current);
		}
		final List<IcfgEdge> incoming = new ArrayList<>(current.getIncomingEdges());
		final List<IcfgLocation> sinkCanidates = new ArrayList<>();
		for (final IcfgEdge edge : incoming) {
			final IcfgLocation sinkCandidate = edge.getSource();
			edge.disconnectSource();
			edge.disconnectTarget();
			mRemovedEdges++;
			if (isSink(icfg, sinkCandidate)) {
				sinkCanidates.add(sinkCandidate);
			}
		}
		return sinkCanidates;
	}

	private boolean isSink(final IIcfg<?> icfg, final IcfgLocation current) {
		return current.getOutgoingEdges().isEmpty() && !mFunHasToBePreserved.test(icfg, current);
	}

	@Override
	public boolean isGraphStructureChanged() {
		return mRemovedEdges > 0 || mRemovedLocations > 0;
	}
}
