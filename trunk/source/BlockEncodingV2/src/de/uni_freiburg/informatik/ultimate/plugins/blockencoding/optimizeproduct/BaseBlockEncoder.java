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
package de.uni_freiburg.informatik.ultimate.plugins.blockencoding.optimizeproduct;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public abstract class BaseBlockEncoder implements IEncoder {
	protected final IUltimateServiceProvider mServices;
	protected final ILogger mLogger;

	protected int mRemovedEdges;
	protected int mRemovedLocations;
	protected final CodeBlockFactory mCbf;
	private RootNode mResult;

	public BaseBlockEncoder(final RootNode product, final IUltimateServiceProvider services,
			final IToolchainStorage storage) {
		assert services != null;
		assert product != null;
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mCbf = CodeBlockFactory.getFactory(storage);
		mRemovedEdges = 0;
		mRemovedLocations = 0;
	}

	@Override
	public abstract boolean isGraphChanged();

	@Override
	public RootNode getResult(final RootNode product) {
		if (mResult == null) {
			mResult = createResult(product);
			assert mResult != null;
		}
		return mResult;
	}

	protected abstract RootNode createResult(RootNode product);

	protected List<IcfgLocation> getSuccessors(final IcfgLocation point) {
		final List<IcfgLocation> rtr = new ArrayList<>();
		for (final IcfgEdge edge : point.getOutgoingEdges()) {
			rtr.add(edge.getTarget());
		}
		return rtr;
	}

	protected void removeDisconnectedLocations(final RootNode root) {
		final Deque<IcfgLocation> toRemove = new ArrayDeque<>();

		for (final Entry<String, Map<String, BoogieIcfgLocation>> procPair : root.getRootAnnot().getProgramPoints()
				.entrySet()) {
			for (final Entry<String, BoogieIcfgLocation> pointPair : procPair.getValue().entrySet()) {
				if (pointPair.getValue().getIncomingEdges().isEmpty()) {
					toRemove.add(pointPair.getValue());
				}
			}
		}

		while (!toRemove.isEmpty()) {
			final IcfgLocation current = toRemove.removeFirst();
			final List<IcfgEdge> outEdges = new ArrayList<>(current.getOutgoingEdges());
			for (final IcfgEdge out : outEdges) {
				final IcfgLocation target = out.getTarget();
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

	protected void removeDisconnectedLocation(final RootNode root, final IcfgLocation toRemove) {
		final RootAnnot rootAnnot = root.getRootAnnot();
		final String procName = toRemove.getProcedure();
		final String debugIdentifier = toRemove.getDebugIdentifier();
		// TODO: This seems wrong!
		final IcfgLocation removed = rootAnnot.getProgramPoints().get(procName).remove(debugIdentifier);
		assert toRemove.equals(removed);
		mRemovedLocations++;
	}
}
