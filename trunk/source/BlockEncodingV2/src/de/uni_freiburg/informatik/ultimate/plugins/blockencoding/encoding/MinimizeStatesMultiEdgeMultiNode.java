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

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.BlockEncodingBacktranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Most aggressive minimization. Tries to remove states no matter what.
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class MinimizeStatesMultiEdgeMultiNode extends BaseMinimizeStates {
	
	public MinimizeStatesMultiEdgeMultiNode(final IcfgEdgeBuilder edgeBuilder, final IUltimateServiceProvider services,
			final BlockEncodingBacktranslator backtranslator, final Predicate<IcfgLocation> funIsAccepting) {
		super(edgeBuilder, services, backtranslator, funIsAccepting);
	}
	
	@Override
	protected Collection<? extends IcfgLocation> processCandidate(final IIcfg<?> icfg, final IcfgLocation target,
			final Set<IcfgLocation> closed) {
		// we have the incoming edges
		// ei = (qi,sti,q) in EI
		// and the outgoing edges
		// ej = (q,stj,qj) in EO
		// and we will try to replace them by |EI| * |EO| edges
		
		if (isNecessary(target)) {
			// do not remove necessary nodes
			return target.getOutgoingNodes();
		}
		
		final List<IcfgLocation> incomingNodes = target.getIncomingNodes();
		final List<IcfgLocation> outgoingNodes = target.getOutgoingNodes();
		
		if (incomingNodes.isEmpty() || outgoingNodes.isEmpty()) {
			// do not remove nodes which are disconnected or sinks (not necessary)
			return target.getOutgoingNodes();
		}
		
		if (!areCombinableEdgePairs(target.getIncomingEdges(), target.getOutgoingEdges())) {
			// do not remove anything if blowup is too large or call/return combination prohibits the removal
			return target.getOutgoingNodes();
		}
		
		// we will not change the acceptance conditions, so we can start
		// with creating new edges
		// for each ei from EI, for each ej from EO
		// we add a new edge (qi,sti;stj,qj)
		
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("    will try to remove " + target.getDebugIdentifier());
		}
		
		final List<Pair<CodeBlock, CodeBlock>> pairs = getEdgePairs(target);
		if (pairs.isEmpty()) {
			// nothing to do here
			return target.getOutgoingNodes();
		}
		
		final Set<IcfgEdge> toRemove = new HashSet<>();
		final Set<IcfgLocation> openLocations = new HashSet<>();
		final Set<EdgeConstructor> constructors = new HashSet<>();
		int addE = 0;
		for (final Pair<CodeBlock, CodeBlock> pair : pairs) {
			final CodeBlock first = pair.getFirst();
			final CodeBlock second = pair.getSecond();
			toRemove.add(first);
			toRemove.add(second);
			if (first.getTransitionFormula().isInfeasible() == Infeasibility.INFEASIBLE
					|| second.getTransitionFormula().isInfeasible() == Infeasibility.INFEASIBLE) {
				// we will remove these edges but we wont add a new one
				continue;
			}
			constructors.add(new EdgeConstructor(first, second));
			addE++;
			// we changed the edges of the predecessor, we have to re-check
			// them. We therefore need to remove them from the closed set.
			openLocations.add(first.getSource());
			closed.remove(first.getSource());
		}
		
		constructors.stream().forEach(a -> a.constructSequentialComposition());
		
		final int removeE = disconnectEdges(toRemove);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("    removed " + removeE + ", added " + addE + " edges");
		}
		mRemovedEdges += removeE;
		
		// we also need to add all remaining targets of the current node
		openLocations.addAll(target.getOutgoingNodes());
		
		return openLocations;
	}
	
	private static List<Pair<CodeBlock, CodeBlock>> getEdgePairs(final IcfgLocation target) {
		final List<Pair<CodeBlock, CodeBlock>> rtr = new ArrayList<>();
		for (final IcfgEdge inEdge : target.getIncomingEdges()) {
			if (inEdge instanceof Summary) {
				// skip combinations with summary edges
				continue;
			}
			for (final IcfgEdge outEdge : target.getOutgoingEdges()) {
				if (outEdge instanceof Summary) {
					// skip combinations with summary edges
					continue;
				}
				rtr.add(new Pair<>((CodeBlock) inEdge, (CodeBlock) outEdge));
			}
		}
		return rtr;
	}
	
	private static int disconnectEdges(final Collection<IcfgEdge> edges) {
		int removedEdges = 0;
		for (final IcfgEdge succEdge : edges) {
			succEdge.disconnectSource();
			succEdge.disconnectTarget();
			removedEdges++;
		}
		return removedEdges;
	}
	
	private final class EdgeConstructor {
		private final BoogieIcfgLocation mSource;
		private final BoogieIcfgLocation mTarget;
		private final CodeBlock mFirst;
		private final CodeBlock mSecond;
		
		private EdgeConstructor(final CodeBlock first, final CodeBlock second) {
			mSource = (BoogieIcfgLocation) first.getSource();
			mTarget = (BoogieIcfgLocation) second.getTarget();
			mFirst = first;
			mSecond = second;
		}
		
		private SequentialComposition constructSequentialComposition() {
			final SequentialComposition newEdge =
					getEdgeBuilder().constructSequentialComposition(mSource, mTarget, mFirst, mSecond);
			rememberEdgeMapping(newEdge, mFirst);
			rememberEdgeMapping(newEdge, mSecond);
			return newEdge;
		}
	}
}
