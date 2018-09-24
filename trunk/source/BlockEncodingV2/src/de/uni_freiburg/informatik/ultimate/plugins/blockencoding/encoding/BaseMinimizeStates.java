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
import java.util.Collection;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.function.BiPredicate;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.BlockEncodingBacktranslator;

/**
 * Base class for encoder that try to minimize the nodes/states/locations of an RCFG.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class BaseMinimizeStates extends BaseBlockEncoder<IcfgLocation> {

	private final boolean mIgnoreBlowup;
	private final BiPredicate<IIcfg<?>, IcfgLocation> mFunHasToBePreserved;
	private final IcfgEdgeBuilder mEdgeBuilder;

	public BaseMinimizeStates(final IcfgEdgeBuilder edgeBuilder, final IUltimateServiceProvider services,
			final BlockEncodingBacktranslator backtranslator,
			final BiPredicate<IIcfg<?>, IcfgLocation> funHasToBePreserved, final ILogger logger,
			final boolean ignoreBlowup) {
		super(logger, services, backtranslator);
		mIgnoreBlowup = ignoreBlowup;
		mFunHasToBePreserved = funHasToBePreserved;
		mEdgeBuilder = edgeBuilder;
	}

	@Override
	public boolean isGraphStructureChanged() {
		return mRemovedLocations > 0 || mRemovedEdges > 0;
	}

	@Override
	protected final BasicIcfg<IcfgLocation> createResult(final BasicIcfg<IcfgLocation> icfg) {
		final Deque<IcfgLocation> nodes = new ArrayDeque<>();
		final Set<IcfgLocation> closed = new HashSet<>();

		nodes.addAll(icfg.getInitialNodes());

		while (!nodes.isEmpty()) {
			checkForTimeoutOrCancellation();

			final IcfgLocation current = nodes.removeFirst();
			if (closed.contains(current)) {
				continue;
			}
			closed.add(current);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("Processing node " + current + " [" + current.hashCode() + "]");
			}
			nodes.addAll(processCandidate(icfg, current, closed));
		}
		if (mRemovedEdges > 0) {
			removeDisconnectedLocations(icfg);
		}
		mLogger.info(
				"Removed " + mRemovedEdges + " edges and " + mRemovedLocations + " locations by large block encoding");
		return icfg;
	}

	/**
	 * Process the state "target" and return a set of nodes that should be processed next. Processing means adding and
	 * removing edges. The caller will take care that this method is called only once per target node.
	 *
	 * @param icfg
	 *            The current ICFG.
	 * @param target
	 *            The node that should be processed.
	 * @param closed
	 *            A set of already processed nodes. You may add additional nodes here if you know that you do not need
	 *            to process them. You may also remove some nodes if you want to re-process them.
	 * @return A set of nodes that should be processed. May not be null. Nodes already in the closed set will not be
	 *         processed again.
	 */
	protected abstract Collection<? extends IcfgLocation> processCandidate(IIcfg<?> icfg, IcfgLocation target,
			Set<IcfgLocation> closed);

	protected boolean isAllCombinableEdgePair(final List<IcfgEdge> predEdges, final List<IcfgEdge> succEdges) {
		if (!mIgnoreBlowup && isLarge(predEdges, succEdges)) {
			// we would introduce more edges than we remove, we do not want
			// that
			return false;
		}

		return predEdges.stream().map(pred -> (Predicate<IcfgEdge>) a -> isCombinableEdgePair(pred, a))
				.allMatch(a -> succEdges.stream().allMatch(a));
	}

	protected boolean isCombinableEdgePair(final IcfgEdge predEdge, final IcfgEdge succEdge) {

		if (predEdge instanceof IIcfgCallTransition<?> && succEdge instanceof IIcfgReturnTransition<?, ?>) {
			// this is allowed, continue
		} else if (predEdge instanceof IIcfgReturnTransition<?, ?> || predEdge instanceof IIcfgCallTransition<?>
				|| succEdge instanceof IIcfgReturnTransition<?, ?> || succEdge instanceof IIcfgCallTransition<?>) {
			// we can only compose (Call,Return), no other combination
			// of Call /
			// Return.
			return false;
		}

		// if one of the edges is a self loop, we cannot use it
		return !Objects.equals(predEdge.getTarget(), predEdge.getSource())
				&& !Objects.equals(succEdge.getTarget(), succEdge.getSource());
	}

	protected boolean isAllNecessary(final IIcfg<?> icfg, final List<IcfgLocation> nodes) {
		return nodes.stream().allMatch(a -> mFunHasToBePreserved.test(icfg, a));
	}

	protected boolean isNecessary(final IIcfg<?> icfg, final IcfgLocation target) {
		return mFunHasToBePreserved.test(icfg, target);
	}

	protected boolean isNotNecessary(final IIcfg<?> icfg, final IcfgLocation target) {
		return mFunHasToBePreserved.negate().test(icfg, target);
	}

	protected boolean isAnyNecessary(final IIcfg<?> icfg, final IcfgLocation pred, final IcfgLocation succ) {
		return mFunHasToBePreserved.test(icfg, pred) || mFunHasToBePreserved.test(icfg, succ);
	}

	protected IcfgEdgeBuilder getEdgeBuilder() {
		return mEdgeBuilder;
	}

	private void checkForTimeoutOrCancellation() {
		if (!mServices.getProgressMonitorService().continueProcessing()) {
			mLogger.info("Stopping block encoding due to timeout after removing " + mRemovedEdges + " edges and "
					+ mRemovedLocations + " locations (locations are removed at the end)");
			throw new ToolchainCanceledException(getClass());
		}
	}

	/**
	 * @return true iff the cross-product is larger than the sum of elements.
	 */
	private static boolean isLarge(final List<IcfgEdge> predEdges, final List<IcfgEdge> succEdges) {
		final int predEdgesSize = predEdges.size();
		final int succEdgesSize = succEdges.size();
		return predEdgesSize + succEdgesSize < predEdgesSize * succEdgesSize;
	}

}
