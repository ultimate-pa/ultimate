/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.impulse;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.RedirectionStrategy;

public class ImpulseChecker extends CodeChecker {

	private final RedirectionFinder mCloneFinder;
	private int mNodeId;

	public ImpulseChecker(final CfgSmtToolkit cfgSmtToolkit, final IIcfg<IcfgLocation> originalRoot,
			final ImpRootNode graphRoot, final GraphWriter graphWriter, final IHoareTripleChecker edgeChecker,
			final IPredicateUnifier predicateUnifier, final ILogger logger, final CodeCheckSettings globSettings) {
		super(cfgSmtToolkit, originalRoot, graphRoot, graphWriter, edgeChecker, predicateUnifier, logger, globSettings);
		mCloneFinder = new RedirectionFinder(this);
		mNodeId = 0;
	}

	public void replaceEdge(final AppEdge edge, final AnnotatedProgramPoint newTarget) {
		if (edge instanceof AppHyperEdge) {
			edge.getSource().connectOutgoingReturn(((AppHyperEdge) edge).getHier(),
					(IIcfgReturnTransition<?, ?>) edge.getStatement(), newTarget);
		} else {
			edge.getSource().connectOutgoing(edge.getStatement(), newTarget);
		}

		edge.disconnect();
	}

	public boolean defaultRedirecting(final AnnotatedProgramPoint[] nodes, final AnnotatedProgramPoint[] clones) {

		boolean errorReached = false;
		for (int i = 0; i + 1 < nodes.length; ++i) {
			if (nodes[i + 1].isErrorLocation()) {
				clones[i].getEdge(nodes[i + 1]).disconnect();
				errorReached = true;
			} else {
				if (getGlobalSettings().isDefaultRedirection()) {
					if (getGlobalSettings().isCheckSatisfiability()) {
						redirectIfValid(clones[i].getEdge(nodes[i + 1]), clones[i + 1]);
					} else {
						replaceEdge(clones[i].getEdge(nodes[i + 1]), clones[i + 1]);
					}
				} else {
					AnnotatedProgramPoint clone = clones[i + 1];
					final AppEdge prevEdge = clones[i].getEdge(nodes[i + 1]);
					if (getGlobalSettings().getRedirectionStrategy() != RedirectionStrategy.No_Strategy) {
						clone = mCloneFinder.getStrongestValidCopy(prevEdge);
					}

					if (clone == null) {
						continue;
					}
					redirectIfValid(prevEdge, clone);
				}
			}
		}

		return errorReached;
	}

	public boolean redirectEdges(final AnnotatedProgramPoint[] nodes, final AnnotatedProgramPoint[] clones) {

		for (int i = 0; i < nodes.length; ++i) {
			if (nodes[i].isErrorLocation()) {
				continue;
			}
			final AppEdge[] prevEdges = nodes[i].getIncomingEdges().toArray(new AppEdge[] {});
			for (final AppEdge prevEdge : prevEdges) {
				AnnotatedProgramPoint clone = clones[i];

				if (getGlobalSettings().getRedirectionStrategy() != RedirectionStrategy.No_Strategy) {
					clone = mCloneFinder.getStrongestValidCopy(prevEdge);
				}

				if (clone == null) {
					continue;
				}
				redirectIfValid(prevEdge, clone);
			}
		}
		return true;
	}

	protected void redirectIfValid(final AppEdge edge, final AnnotatedProgramPoint target) {
		if (edge.getTarget() == target) {
			return;
		}
		if (isValidRedirection(edge, target)) {
			if (edge instanceof AppHyperEdge) {

				if (!getGlobalSettings().isCheckSatisfiability()
						|| mEdgeChecker.checkReturn(edge.getSource().getPredicate(),
								((AppHyperEdge) edge).getHier().getPredicate(), (IReturnAction) edge.getStatement(),
								edge.getTarget().getPredicate()) != Validity.VALID) {
					edge.getSource().connectOutgoingReturn(((AppHyperEdge) edge).getHier(),
							(IIcfgReturnTransition<?, ?>) edge.getStatement(), target);
				}
			} else {

				boolean result = !getGlobalSettings().isCheckSatisfiability();
				if (!result) {
					if (edge.getStatement() instanceof IIcfgCallTransition<?>) {
						result = mEdgeChecker.checkCall(edge.getSource().getPredicate(),
								(ICallAction) edge.getStatement(), edge.getTarget().getPredicate()) != Validity.VALID;
					} else {
						result = mEdgeChecker.checkInternal(edge.getSource().getPredicate(),
								(IInternalAction) edge.getStatement(),
								edge.getTarget().getPredicate()) != Validity.VALID;
					}
				}

				if (result) {
					edge.getSource().connectOutgoing(edge.getStatement(), target);
				}

			}

			edge.disconnect();
		}
	}

	public boolean isValidRedirection(final AppEdge edge, final AnnotatedProgramPoint target) {
		if (edge instanceof AppHyperEdge) {
			return isValidReturnEdge(edge.getSource(), edge.getStatement(), target, ((AppHyperEdge) edge).getHier());
		}
		return isValidEdge(edge.getSource(), edge.getStatement(), target);
	}

	@Override
	public boolean codeCheck(final NestedRun<IIcfgTransition<?>, AnnotatedProgramPoint> errorRun,
			final IPredicate[] interpolants, final AnnotatedProgramPoint procedureRoot) {

		final AnnotatedProgramPoint[] nodes = errorRun.getStateSequence().toArray(new AnnotatedProgramPoint[0]);
		final AnnotatedProgramPoint[] clones = new AnnotatedProgramPoint[nodes.length];

		final AnnotatedProgramPoint newRoot =
				new AnnotatedProgramPoint(nodes[0], nodes[0].getPredicate(), true, ++mNodeId);

		clones[0] = nodes[0];
		nodes[0] = newRoot;

		for (int i = 0; i < interpolants.length; ++i) {
			clones[i + 1] = new AnnotatedProgramPoint(nodes[i + 1],
					conjugatePredicates(nodes[i + 1].getPredicate(), interpolants[i]), true, ++mNodeId);
		}

		if (!defaultRedirecting(nodes, clones)) {
			throw new AssertionError("The error location hasn't been reached.");
		}
		redirectEdges(nodes, clones);

		if (getGlobalSettings().isRemoveFalseNodes()) {
			removeFalseNodes(nodes, clones);
		}

		return true;
	}

	public boolean removeFalseNodes(final AnnotatedProgramPoint[] nodes, final AnnotatedProgramPoint[] clones) {
		for (int i = 0; i < nodes.length; ++i) {
			if (nodes[i].isErrorLocation()) {
				continue;
			}
			// TODO: Handle the false predicate properly.
			final IPredicate annotation = clones[i].getPredicate();
			if (mPredicateUnifier.getOrConstructPredicate(annotation.getFormula())
					.equals(mPredicateUnifier.getFalsePredicate())) {
				clones[i].isolateNode();
			}
		}
		return true;
	}

	public boolean improveAnnotations(final AnnotatedProgramPoint root) {
		final HashSet<AnnotatedProgramPoint> seen = new HashSet<>();

		final HashSet<AnnotatedProgramPoint> pushed = new HashSet<>();
		final Queue<AnnotatedProgramPoint> queue = new LinkedList<>();

		queue.add(root);
		pushed.add(root);

		while (!queue.isEmpty()) {
			final AnnotatedProgramPoint peak = queue.poll();
			final AnnotatedProgramPoint[] prevNodes = peak.getIncomingNodes().toArray(new AnnotatedProgramPoint[] {});
			if (prevNodes.length == 1) {
				// TODO: Modify the new predicate.
				final AnnotatedProgramPoint prevNode = prevNodes[0];
				if (seen.contains(prevNode)) {
					// peak.predicate &= prevNode.predicate o edge.formula
				}
			} else {
				// TODO: To handle this case later
				for (final AnnotatedProgramPoint prevNode : prevNodes) {
					if (seen.contains(prevNode)) {
						// Formula |= prevNode.predicate o edge.formula
					}
				}
			}

			final AnnotatedProgramPoint[] nextNodes = peak.getOutgoingNodes().toArray(new AnnotatedProgramPoint[] {});
			for (final AnnotatedProgramPoint nextNode : nextNodes) {
				if (!pushed.contains(nextNode)) {
					pushed.add(nextNode);
					queue.add(nextNode);
				}
			}
			seen.add(peak);
		}

		return true;
	}

	public boolean isValidEdge(final AnnotatedProgramPoint sourceNode, final IIcfgTransition<?> edgeLabel,
			final AnnotatedProgramPoint destinationNode) {
		if (edgeLabel instanceof DummyCodeBlock) {
			return false;
		}

		boolean result = true;
		if (edgeLabel instanceof IIcfgCallTransition<?>) {
			result = mEdgeChecker.checkCall(sourceNode.getPredicate(), (ICallAction) edgeLabel,
					destinationNode.getPredicate()) == Validity.VALID;
		} else {
			result = mEdgeChecker.checkInternal(sourceNode.getPredicate(), (IInternalAction) edgeLabel,
					destinationNode.getPredicate()) == Validity.VALID;
		}
		return result;
	}

	public boolean isValidReturnEdge(final AnnotatedProgramPoint sourceNode, final IIcfgTransition<?> edgeLabel,
			final AnnotatedProgramPoint destinationNode, final AnnotatedProgramPoint callNode) {
		final boolean result = mEdgeChecker.checkReturn(sourceNode.getPredicate(), callNode.getPredicate(),
				(IReturnAction) edgeLabel, destinationNode.getPredicate()) == Validity.VALID;
		return result;
	}

	protected boolean connectOutgoingIfValid(final AnnotatedProgramPoint source, final IIcfgTransition<?> statement,
			final AnnotatedProgramPoint target) {
		if (isValidEdge(source, statement, target)) {
			source.connectOutgoing(statement, target);
			return true;
		}
		return false;
	}

	protected boolean connectOutgoingReturnIfValid(final AnnotatedProgramPoint source, final AnnotatedProgramPoint hier,
			final IIcfgReturnTransition<?, ?> statement, final AnnotatedProgramPoint target) {
		if (isValidReturnEdge(source, statement, target, hier)) {
			source.connectOutgoingReturn(hier, statement, target);
			return true;
		}
		return false;
	}

	boolean isStrongerPredicate(final AnnotatedProgramPoint node1, final AnnotatedProgramPoint node2) {
		boolean result = mPredicateUnifier.getCoverageRelation().isCovered(node1.getPredicate(),
				node2.getPredicate()) == Validity.VALID;
		if (result) {
			final boolean converse = mPredicateUnifier.getCoverageRelation().isCovered(node2.getPredicate(),
					node1.getPredicate()) == Validity.VALID;
			result &= !converse || node1.getNodeId() > node2.getNodeId();
		}
		return result;
	}
}
