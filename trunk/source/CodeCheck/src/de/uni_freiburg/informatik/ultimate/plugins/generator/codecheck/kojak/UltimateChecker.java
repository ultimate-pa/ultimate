/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Mostafa Mahmoud Amin
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CodeCheck plug-in.
 *
 * The ULTIMATE CodeCheck plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CodeCheck plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CodeCheck plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CodeCheck plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CodeCheck plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.kojak;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AnnotatedProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppHyperEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.DummyCodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.ImpRootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.CodeCheckSettings;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.CodeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.GraphWriter;

/**
 * UltimateChecker class, implements the model checker Ultimate.
 *
 * @author Mostafa Mahmoud
 *
 */
public class UltimateChecker extends CodeChecker {

	public UltimateChecker(final CfgSmtToolkit cfgSmtToolkit, final IIcfg<IcfgLocation> originalRoot,
			final ImpRootNode graphRoot, final GraphWriter graphWriter, final IHoareTripleChecker edgeChecker,
			final IPredicateUnifier predicateUnifier, final ILogger logger, final CodeCheckSettings globalSettings) {
		super(cfgSmtToolkit, originalRoot, graphRoot, graphWriter, edgeChecker, predicateUnifier, logger,
				globalSettings);
	}

	/**
	 * Given an error trace with the corresponding interpolants, then it modifies the graph accordingly.
	 */
	@Override
	public boolean codeCheck(final NestedRun<IIcfgTransition<?>, AnnotatedProgramPoint> errorRun,
			final IPredicate[] interpolants, final AnnotatedProgramPoint procedureRoot) {

		// Debug The Error Trace and the corresponding list of interpolants.
		final AnnotatedProgramPoint[] nodes = errorRun.getStateSequence().toArray(new AnnotatedProgramPoint[0]);
		final List<AnnotatedProgramPoint> errorTraceDBG = new ArrayList<>();
		Collections.addAll(errorTraceDBG, nodes);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(String.format("Error: %s%n", errorTraceDBG));
		}

		final List<IPredicate> interpolantsDBG = new ArrayList<>();
		Collections.addAll(interpolantsDBG, interpolants);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(String.format("Inters: %s%n", interpolantsDBG));
		}

		for (int i = 0; i < interpolants.length; i++) {
			splitNode(nodes[i + 1], interpolants[i]);
		}

		mEdgeChecker.releaseLock();
		return true;
	}

	private void splitNode(final AnnotatedProgramPoint oldNode, final IPredicate predicate) {
		// make two new nodes
		final AnnotatedProgramPoint newNode1 =
				new AnnotatedProgramPoint(oldNode, conjugatePredicates(oldNode.getPredicate(), predicate));
		final AnnotatedProgramPoint newNode2 = new AnnotatedProgramPoint(oldNode,
				conjugatePredicates(oldNode.getPredicate(), negatePredicate(predicate)));

		// connect predecessors of old node to new nodes, disconnect them from
		// old node
		final AppEdge[] oldInEdges = oldNode.getIncomingEdges().toArray(new AppEdge[] {});
		for (final AppEdge oldInEdge : oldInEdges) {
			final AnnotatedProgramPoint source = oldInEdge.getSource();
			final IIcfgTransition<?> statement = oldInEdge.getStatement();

			// deal with self loops elsewhere
			if (source.equals(oldNode)) {
				continue;
			}

			if (oldInEdge instanceof AppHyperEdge) {
				final AnnotatedProgramPoint hier = ((AppHyperEdge) oldInEdge).getHier();
				connectOutgoingReturnIfSat(source, hier, (IIcfgReturnTransition<?, ?>) statement, newNode1);
				connectOutgoingReturnIfSat(source, hier, (IIcfgReturnTransition<?, ?>) statement, newNode2);
			} else {
				connectOutgoingIfSat(source, statement, newNode1);
				connectOutgoingIfSat(source, statement, newNode2);
			}

			oldInEdge.disconnect();
		}

		// connect successors of old node to new nodes, disconnect them from old
		// node
		final AppEdge[] oldOutEdges = oldNode.getOutgoingEdges().toArray(new AppEdge[] {});
		for (final AppEdge oldOutEdge : oldOutEdges) {
			final AnnotatedProgramPoint target = oldOutEdge.getTarget();
			final IIcfgTransition<?> statement = oldOutEdge.getStatement();

			// deal with self loops elsewhere
			if (target.equals(oldNode)) {
				continue;
			}

			if (oldOutEdge instanceof AppHyperEdge) {
				final AnnotatedProgramPoint hier = ((AppHyperEdge) oldOutEdge).getHier();
				connectOutgoingReturnIfSat(newNode1, hier, (IIcfgReturnTransition<?, ?>) statement, target);
				connectOutgoingReturnIfSat(newNode2, hier, (IIcfgReturnTransition<?, ?>) statement, target);
			} else {
				connectOutgoingIfSat(newNode1, statement, target);
				connectOutgoingIfSat(newNode2, statement, target);
			}

			oldOutEdge.disconnect();
		}

		// deal with self loops
		for (final AppEdge oldOutEdge : oldOutEdges) {
			final AnnotatedProgramPoint target = oldOutEdge.getTarget();
			final IIcfgTransition<?> statement = oldOutEdge.getStatement();

			// already dealt with non self loops and disconnected those edges
			if (target == null) {
				continue;
			}

			if (oldOutEdge instanceof AppHyperEdge) {
				final AnnotatedProgramPoint hier = ((AppHyperEdge) oldOutEdge).getHier();
				connectOutgoingReturnIfSat(newNode1, hier, (IIcfgReturnTransition<?, ?>) statement, newNode1);
				connectOutgoingReturnIfSat(newNode1, hier, (IIcfgReturnTransition<?, ?>) statement, newNode2);
				connectOutgoingReturnIfSat(newNode2, hier, (IIcfgReturnTransition<?, ?>) statement, newNode1);
				connectOutgoingReturnIfSat(newNode2, hier, (IIcfgReturnTransition<?, ?>) statement, newNode2);
			} else {
				connectOutgoingIfSat(newNode1, statement, newNode1);
				connectOutgoingIfSat(newNode1, statement, newNode2);
				connectOutgoingIfSat(newNode2, statement, newNode1);
				connectOutgoingIfSat(newNode2, statement, newNode2);
			}

			oldOutEdge.disconnect();
		}

		// duplicate outgoing hyperedges
		final AppHyperEdge[] oldOutHypEdges = oldNode.getOutgoingHyperEdges().toArray(new AppHyperEdge[] {});
		for (final AppHyperEdge oldOutHypEdge : oldOutHypEdges) {
			final AnnotatedProgramPoint source = oldOutHypEdge.getSource();
			final AnnotatedProgramPoint target = oldOutHypEdge.getTarget();
			final IIcfgReturnTransition<?, ?> statement = (IIcfgReturnTransition<?, ?>) oldOutHypEdge.getStatement();

			connectOutgoingReturnIfSat(source, newNode1, statement, target);
			connectOutgoingReturnIfSat(source, newNode2, statement, target);

			oldOutHypEdge.disconnect();
		}
	}

	protected boolean connectOutgoingIfSat(final AnnotatedProgramPoint source, final IIcfgTransition<?> statement,
			final AnnotatedProgramPoint target) {
		if (isSatEdge(source.getPredicate(), statement, target.getPredicate())) {
			source.connectOutgoing(statement, target);
			return true;
		}
		return false;
	}

	protected boolean connectOutgoingReturnIfSat(final AnnotatedProgramPoint source, final AnnotatedProgramPoint hier,
			final IIcfgReturnTransition<?, ?> statement, final AnnotatedProgramPoint target) {
		if (isSatRetEdge(source.getPredicate(), hier.getPredicate(), statement, target.getPredicate())) {
			source.connectOutgoingReturn(hier, statement, target);
			return true;
		}
		return false;
	}

	/**
	 * Check if an edge between two AnnotatedProgramPoints is satisfiable or not, works with the cases if the edge is a
	 * normal edge or a call edge.
	 *
	 * @param preCondition
	 * @param statement
	 * @param postCondition
	 * @return
	 */
	protected boolean isSatEdge(final IPredicate preCondition, final IIcfgTransition<?> statement,
			final IPredicate postCondition) {
		if (statement instanceof DummyCodeBlock) {
			return false;
		}

		final boolean result;
		if (statement instanceof IIcfgCallTransition<?>) {
			// result is true if pre /\ stm /\ post is sat or unknown, false if unsat
			result = mEdgeChecker.checkCall(preCondition, (ICallAction) statement,
					negatePredicate(postCondition)) != Validity.VALID;
		} else {
			result = mEdgeChecker.checkInternal(preCondition, (IInternalAction) statement,
					negatePredicate(postCondition)) != Validity.VALID;
		}

		return result;
	}

	/**
	 * Check if a return edge between two AnnotatedProgramPoints is satisfiable or not.
	 *
	 * @param preCondition
	 * @param statement
	 * @param destinationNode
	 * @param hier
	 * @return
	 */
	protected boolean isSatRetEdge(final IPredicate preCondition, final IPredicate hier,
			final IIcfgReturnTransition<?, ?> statement, final IPredicate postCondition) {
		return mEdgeChecker.checkReturn(preCondition, hier, statement,
				negatePredicate(postCondition)) != Validity.VALID;
	}

}
