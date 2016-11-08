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
import java.util.Deque;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.Activator;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;

public abstract class BaseProductOptimizer {
	protected final IUltimateServiceProvider mServices;
	protected final ILogger mLogger;

	protected int mRemovedEdges;
	protected int mRemovedLocations;
	protected final CodeBlockFactory mCbf;
	private BoogieIcfgContainer mResult;

	public BaseProductOptimizer(final BoogieIcfgContainer product, final IUltimateServiceProvider services,
			final IToolchainStorage storage) {
		assert services != null;
		assert product != null;
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mCbf = CodeBlockFactory.getFactory(storage);
		mRemovedEdges = 0;
		mRemovedLocations = 0;
	}

	public abstract boolean isGraphChanged();

	public BoogieIcfgContainer getResult(final BoogieIcfgContainer product) {
		if (mResult == null) {
			mResult = createResult(product);
			assert mResult != null;
		}
		return mResult;
	}

	protected abstract BoogieIcfgContainer createResult(BoogieIcfgContainer product);

	protected List<BoogieIcfgLocation> getSuccessors(final BoogieIcfgLocation point) {
		final List<BoogieIcfgLocation> rtr = new ArrayList<>();
		for (final IcfgEdge edge : point.getOutgoingEdges()) {
			rtr.add((BoogieIcfgLocation) edge.getTarget());
		}
		return rtr;
	}

	protected void removeDisconnectedLocations(final BoogieIcfgContainer root) {
		final Deque<BoogieIcfgLocation> toRemove = new ArrayDeque<>();

		for (final Entry<String, Map<String, BoogieIcfgLocation>> procPair : root.getProgramPoints()
				.entrySet()) {
			for (final Entry<String, BoogieIcfgLocation> pointPair : procPair.getValue().entrySet()) {
				if (pointPair.getValue().getIncomingEdges().isEmpty()) {
					toRemove.add(pointPair.getValue());
				}
			}
		}

		while (!toRemove.isEmpty()) {
			final BoogieIcfgLocation current = toRemove.removeFirst();
			final List<IcfgEdge> outEdges = new ArrayList<>(current.getOutgoingEdges());
			for (final IcfgEdge out : outEdges) {
				final BoogieIcfgLocation target = (BoogieIcfgLocation) out.getTarget();
				if (target.getIncomingEdges().size() == 1) {
					toRemove.addLast(target);
				}
				out.disconnectSource();
				out.disconnectTarget();
				mRemovedEdges++;
			}
			removeDisconnectedLocation(root, current);
		}
	}

	protected void removeDisconnectedLocation(final BoogieIcfgContainer root, final BoogieIcfgLocation toRemove) {
		final BoogieIcfgContainer rootAnnot = root;
		final String procName = toRemove.getProcedure();
		final String locName = toRemove.getDebugIdentifier();
		final BoogieIcfgLocation removed = rootAnnot.getProgramPoints().get(procName).remove(locName);
		assert toRemove.equals(removed);
		mRemovedLocations++;
	}
}
