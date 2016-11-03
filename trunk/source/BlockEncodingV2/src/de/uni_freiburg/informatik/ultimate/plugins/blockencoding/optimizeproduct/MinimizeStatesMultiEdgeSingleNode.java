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

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.BlockEncodingBacktranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

/**
 * Moderately aggressive minimization. Tries to remove states that have exactly one predecessor and one successor state
 * (but possibly more edges).
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class MinimizeStatesMultiEdgeSingleNode extends BaseMinimizeStates {

	public MinimizeStatesMultiEdgeSingleNode(final RootNode product, final IUltimateServiceProvider services,
			final IToolchainStorage storage, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final BlockEncodingBacktranslator backtranslator,
			final Predicate<RCFGNode> funIsAccepting) {
		super(product, services, storage, backtranslator, simplificationTechnique, xnfConversionTechnique,
				funIsAccepting);
	}

	@Override
	protected Collection<? extends RCFGNode> processCandidate(final RootNode root, final ProgramPoint target,
			final Set<RCFGNode> closed) {

		if (new HashSet<>(target.getIncomingNodes()).size() != 1
				|| new HashSet<>(target.getOutgoingNodes()).size() != 1) {
			return target.getOutgoingNodes();
		}

		// this node has exactly one predecessor and one successor, but may have
		// more edges
		// so we have the incoming edges
		// ei = (q1,sti,q2) in Ei
		// and the outoging edges
		// eo = (q2,sto,q3) in Eo
		// and we will try to replace them by |Ei| * |Eo| edges

		// a precondition is that there is only one predecessor and one
		// successor, so this is enough to get it
		final ProgramPoint pred = (ProgramPoint) target.getIncomingEdges().get(0).getSource();
		final ProgramPoint succ = (ProgramPoint) target.getOutgoingEdges().get(0).getTarget();

		if (!isNotNecessary(target) && !isOneNecessary(pred, succ)) {
			// the nodes do not fulfill the conditions, return
			return target.getOutgoingNodes();
		}

		if (!areCombinableEdgePairs(target.getIncomingEdges(), target.getOutgoingEdges())) {
			// the edges do not fulfill the conditions, return
			return target.getOutgoingNodes();
		}

		// all conditions are met so we can start with creating new edges
		// for each ei from Ei and for each eo from Eo we add a new edge
		// (q1,st1;st2,q3)

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("    will remove " + target.getPosition());
		}

		final List<RCFGEdge> predEdges = new ArrayList<>(target.getIncomingEdges());
		final List<RCFGEdge> succEdges = new ArrayList<>(target.getOutgoingEdges());

		for (final RCFGEdge predEdge : predEdges) {
			predEdge.disconnectSource();
			predEdge.disconnectTarget();
		}

		for (final RCFGEdge succEdge : succEdges) {
			succEdge.disconnectSource();
			succEdge.disconnectTarget();
		}

		int newEdges = 0;
		for (final RCFGEdge predEdge : predEdges) {
			final CodeBlock predCB = (CodeBlock) predEdge;
			if (predCB.getTransitionFormula().isInfeasible() == Infeasibility.INFEASIBLE) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("    already infeasible: " + predCB);
				}
				continue;
			}
			for (final RCFGEdge succEdge : succEdges) {
				final CodeBlock succCB = (CodeBlock) succEdge;

				if (succCB.getTransitionFormula().isInfeasible() == Infeasibility.INFEASIBLE) {
					if (mLogger.isDebugEnabled()) {
						mLogger.debug("    already infeasible: " + succCB);
					}
					continue;
				}
				getEdgeBuilder().constructSequentialComposition(pred, succ, predCB, succCB);
				newEdges++;
			}
		}

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("    removed " + (predEdges.size() + succEdges.size()) + ", added " + newEdges + " edges");
		}

		mRemovedEdges += predEdges.size() + succEdges.size();
		// we added new edges to pred, we have to recheck them now
		return pred.getOutgoingNodes();
	}

}
