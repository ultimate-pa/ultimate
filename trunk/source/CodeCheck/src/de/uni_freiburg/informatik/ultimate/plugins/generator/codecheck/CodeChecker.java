/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Mostafa Mahmoud Amin
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AnnotatedProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.ImpRootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.IsContained;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap4;

public abstract class CodeChecker {

	protected BoogieIcfgContainer mOriginalRoot;
	protected CfgSmtToolkit mCfgToolkit;
	protected ImpRootNode mGraphRoot;

	protected IHoareTripleChecker mEdgeChecker;
	protected PredicateUnifier mPredicateUnifier;

	/*
	 * Maps for storing edge check results. Not that in case of ImpulseChecker these really are valid, not sat, triples.
	 * TODO: either change name, make duplicates for ImpulseChecker, or modify ImpulseChecker such that those are really
	 * sat triples.
	 */
	protected NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> mSatTriples;
	protected NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> mUnsatTriples;
	protected NestedMap4<IPredicate, IPredicate, CodeBlock, IPredicate, IsContained> mSatQuadruples;
	protected NestedMap4<IPredicate, IPredicate, CodeBlock, IPredicate, IsContained> mUnsatQuadruples;

	// stats
	protected int mMemoizationHitsSat = 0;
	protected int mMemoizationHitsUnsat = 0;
	protected int mMemoizationReturnHitsSat = 0;
	protected int mMemoizationReturnHitsUnsat = 0;

	protected GraphWriter mGraphWriter;

	/**
	 * Debugs all the nodes in a graph.
	 */
	private final HashSet<AnnotatedProgramPoint> mVisited = new HashSet<>();
	protected final ILogger mLogger;

	public CodeChecker(final IElement root, final CfgSmtToolkit csToolkit, final BoogieIcfgContainer originalRoot,
			final ImpRootNode graphRoot, final GraphWriter graphWriter, final IHoareTripleChecker edgeChecker,
			final PredicateUnifier predicateUnifier, final ILogger logger) {
		mLogger = logger;
		mCfgToolkit = csToolkit;
		mOriginalRoot = originalRoot;
		mGraphRoot = graphRoot;

		mEdgeChecker = edgeChecker;
		mPredicateUnifier = predicateUnifier;

		mGraphWriter = graphWriter;
	}

	public abstract boolean codeCheck(NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun, IPredicate[] interpolants,
			AnnotatedProgramPoint procedureRoot);

	public abstract boolean codeCheck(NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun, IPredicate[] interpolants,
			AnnotatedProgramPoint procedureRoot, NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> satTriples,
			NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> unsatTriples);

	public abstract boolean codeCheck(NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun, IPredicate[] interpolants,
			AnnotatedProgramPoint procedureRoot, NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> satTriples,
			NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> unsatTriples,
			NestedMap4<IPredicate, IPredicate, CodeBlock, IPredicate, IsContained> satQuadruples,
			NestedMap4<IPredicate, IPredicate, CodeBlock, IPredicate, IsContained> unsatQuadruples);

	/**
	 * Given 2 predicates, return a predicate which is the conjunction of both.
	 *
	 * @param a
	 *            : The first Predicate.
	 * @param b
	 *            : The second Predicate.
	 */
	protected IPredicate conjugatePredicates(final IPredicate a, final IPredicate b) {
		final Term tvp = mPredicateUnifier.getPredicateFactory().and(a, b);
		return mPredicateUnifier.getOrConstructPredicate(tvp);
	}

	/**
	 * Given a predicate, return a predicate which is the negation of it.
	 *
	 * @param a
	 *            : The Predicate.
	 */
	protected IPredicate negatePredicate(final IPredicate a) {
		final Term tvp = mPredicateUnifier.getPredicateFactory().not(a);
		return mPredicateUnifier.getOrConstructPredicate(tvp);
	}

	/**
	 * Given a predicate, return a predicate which is the negation of it, not showing it to the PredicateUnifier
	 *
	 * @param a
	 *            : The Predicate.
	 */
	protected IPredicate negatePredicateNoPU(final IPredicate a) {
		final Term negation = mPredicateUnifier.getPredicateFactory().not(a);
		return mPredicateUnifier.getPredicateFactory().newPredicate(negation);
	}

	public static String objectReference(final Object o) {
		return Integer.toHexString(System.identityHashCode(o));
	}

	public void debug() {
		mVisited.clear();
		dfs(mGraphRoot);
	}

	protected boolean debugNode(final AnnotatedProgramPoint node) {
		return debugNode(node, "");
	}

	/**
	 * A method used for debugging, it prints all the connections of a given node. A message can be added to the printed
	 * information.
	 *
	 * @param node
	 * @param message
	 * @return
	 */
	protected boolean debugNode(final AnnotatedProgramPoint node, final String message) {
		String display = "";
		/*
		 * display += String.format("connected To: %s\n", node.getOutgoingNodes()); display += String.format(
		 * "connected Fr: %s\n", node.getIncomingNodes());
		 */
		// if (node.moutgoingReturnCallPreds != null &&
		// node.moutgoingReturnCallPreds.size() > 0) {
		// display += String.format("outGoing: %s\n",
		// node.moutgoingReturnCallPreds);
		// }
		// if (node.mnodesThatThisIsReturnCallPredOf != null &&
		// node.mnodesThatThisIsReturnCallPredOf.size() > 0) {
		// display += String.format("inHyperEdges: %s\n",
		// node.mnodesThatThisIsReturnCallPredOf);
		// }
		if (display.length() > 0) {
			display = String.format("%s\nNode %s:%n", message, node) + display;
			mLogger.debug(display);
		}
		return false;
	}

	/**
	 * Depth First Search algorithm that debugs all the nodes in a graph.
	 *
	 * @param node
	 *            : The current Node being explored in the DFS.
	 * @return
	 */
	private boolean dfs(final AnnotatedProgramPoint node) {
		if (!mVisited.contains(node)) {
			mVisited.add(node);
			debugNode(node);
			final AnnotatedProgramPoint[] adj = node.getOutgoingNodes().toArray(new AnnotatedProgramPoint[] {});
			for (final AnnotatedProgramPoint child : adj) {
				dfs(child);
			}
		}
		return false;
	}
}
