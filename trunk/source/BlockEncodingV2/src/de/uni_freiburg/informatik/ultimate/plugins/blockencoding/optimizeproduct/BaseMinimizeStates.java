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
import java.util.Collection;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.BlockEncodingBacktranslator;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;

/**
 * Base class for encoder that try to minimize the nodes/states/locations of an RCFG.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class BaseMinimizeStates extends BaseBlockEncoder {
	
	private final boolean mIgnoreBlowup;
	private final Predicate<IcfgLocation> mFunHasToBePreserved;
	private final RcfgEdgeBuilder mTransFormulaBuilder;
	private final BlockEncodingBacktranslator mBacktranslator;
	
	public BaseMinimizeStates(final BoogieIcfgContainer icfg, final IUltimateServiceProvider services,
			final BlockEncodingBacktranslator backtranslator, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final Predicate<IcfgLocation> funHasToBePreserved) {
		super(icfg, services);
		mIgnoreBlowup = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(PreferenceInitializer.OPTIMIZE_MINIMIZE_STATES_IGNORE_BLOWUP);
		mFunHasToBePreserved = funHasToBePreserved;
		mBacktranslator = backtranslator;
		mTransFormulaBuilder = new RcfgEdgeBuilder(icfg, services, simplificationTechnique, xnfConversionTechnique);
	}
	
	@Override
	protected final BoogieIcfgContainer createResult(final BoogieIcfgContainer icfg) {
		final Deque<IcfgLocation> nodes = new ArrayDeque<>();
		final Set<IcfgLocation> closed = new HashSet<>();
		
		nodes.addAll(icfg.getEntryNodes().values());
		
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
			if (current.getIncomingEdges().size() == 1 && current.getIncomingEdges().get(0) instanceof RootEdge) {
				nodes.addAll(current.getOutgoingNodes());
			} else {
				nodes.addAll(processCandidate(icfg, current, closed));
			}
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
	protected abstract Collection<? extends IcfgLocation> processCandidate(BoogieIcfgContainer icfg,
			IcfgLocation target, Set<IcfgLocation> closed);
	
	protected boolean areCombinableEdgePairs(final List<IcfgEdge> predEdges, final List<IcfgEdge> succEdges) {
		if (!mIgnoreBlowup && isLarge(predEdges, succEdges)) {
			// we would introduce more edges than we remove, we do not want
			// that
			return false;
		}
		
		final boolean rtr = predEdges.stream().map(pred -> (Predicate<IcfgEdge>) a -> isCombinableEdgePair(pred, a))
				.allMatch(a -> succEdges.stream().allMatch(a));
		assert rtr == neverTrustMyLambda(predEdges,
				succEdges) : "I am not sure that this does what it should, so I build this assert";
		return rtr;
	}
	
	/**
	 * @return true iff the cross-product is larger than the sum of elements.
	 */
	private static boolean isLarge(final List<IcfgEdge> predEdges, final List<IcfgEdge> succEdges) {
		final int predEdgesSize = predEdges.size();
		final int succEdgesSize = succEdges.size();
		return predEdgesSize + succEdgesSize < predEdgesSize * succEdgesSize;
	}
	
	private boolean neverTrustMyLambda(final List<IcfgEdge> predEdges, final List<IcfgEdge> succEdges) {
		for (final IcfgEdge predEdge : predEdges) {
			final Predicate<IcfgEdge> predicate = a -> isCombinableEdgePair(predEdge, a);
			if (!succEdges.stream().allMatch(predicate)) {
				return false;
			}
		}
		return true;
	}
	
	protected boolean isCombinableEdgePair(final IcfgEdge predEdge, final IcfgEdge succEdge) {
		if (!(predEdge instanceof CodeBlock) || !(succEdge instanceof CodeBlock)) {
			// if one of the edges is no codeblock, it is a root edge,
			// and we cannot apply the rule
			return false;
		}
		
		if (predEdge instanceof Call && succEdge instanceof Return) {
			// this is allowed, continue
		} else if (predEdge instanceof Return || predEdge instanceof Call || succEdge instanceof Return
				|| succEdge instanceof Call) {
			// we can only compose (Call,Return), no other combination
			// of Call /
			// Return.
			return false;
		}
		
		// if one of the edges is a self loop, we cannot use it
		return predEdge.getTarget() != predEdge.getSource() && succEdge.getTarget() != succEdge.getSource();
	}
	
	protected boolean areAllNecessary(final List<IcfgLocation> nodes) {
		return nodes.stream().allMatch(mFunHasToBePreserved);
	}
	
	protected boolean isNecessary(final IcfgLocation target) {
		return mFunHasToBePreserved.test(target);
	}
	
	protected boolean isNotNecessary(final IcfgLocation target) {
		return mFunHasToBePreserved.negate().test(target);
	}
	
	protected boolean isOneNecessary(final IcfgLocation pred, final IcfgLocation succ) {
		return mFunHasToBePreserved.test(pred) || mFunHasToBePreserved.test(succ);
	}
	
	protected RcfgEdgeBuilder getEdgeBuilder() {
		return mTransFormulaBuilder;
	}
	
	protected BlockEncodingBacktranslator getBacktranslator() {
		return mBacktranslator;
	}
	
	private void checkForTimeoutOrCancellation() {
		if (!mServices.getProgressMonitorService().continueProcessing()) {
			throw new ToolchainCanceledException(getClass());
		}
	}
	
	@Override
	public boolean isGraphChanged() {
		return mRemovedLocations > 0 || mRemovedEdges > 0;
	}
}
