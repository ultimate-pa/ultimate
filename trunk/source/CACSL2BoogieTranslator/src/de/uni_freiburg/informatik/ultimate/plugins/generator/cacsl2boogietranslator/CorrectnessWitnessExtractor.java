/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import org.apache.log4j.Logger;
import org.eclipse.cdt.core.dom.ast.ASTGenericVisitor;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNodeAnnotation;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class CorrectnessWitnessExtractor {

	private final IUltimateServiceProvider mServices;
	private final Logger mLogger;
	private WitnessNode mWitnessNode;
	private IASTTranslationUnit mTranslationUnit;
	private Pair<Map<IASTNode, String>, Map<IASTNode, String>> mAST2Invariant;

	public CorrectnessWitnessExtractor(final IUltimateServiceProvider service) {
		mServices = service;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	public void setWitness(final WitnessNode wnode) {
		mWitnessNode = wnode;
	}

	public void setAST(final IASTTranslationUnit inputTU) {
		mTranslationUnit = inputTU;
	}

	public boolean isReady() {
		return mWitnessNode != null && mTranslationUnit != null;
	}

	public void clear() {
		mWitnessNode = null;
		mTranslationUnit = null;
	}

	/**
	 * @return a map from {@link IASTNode} to a String that represents a witness invariant which has to hold before
	 *         whatever is represented by this node.
	 */
	public Map<IASTNode, String> getBeforeAST2Invariants() {
		if (mAST2Invariant == null) {
			mAST2Invariant = extract();
		}
		return mAST2Invariant.getFirst();
	}

	/**
	 * @return a map from {@link IASTNode} to a String that represents a witness invariant which has to hold after
	 *         whatever is represented by this node.
	 */
	public Map<IASTNode, String> getAfterAST2Invariants() {
		if (mAST2Invariant == null) {
			mAST2Invariant = extract();
		}
		return mAST2Invariant.getSecond();
	}

	private Pair<Map<IASTNode, String>, Map<IASTNode, String>> extract() {
		if (!isReady()) {
			mLogger.warn("Cannot extract witness if there is no witness");
			return null;
		}
		final Pair<Map<IASTNode, String>, Map<IASTNode, String>> rtr = new Pair<Map<IASTNode, String>, Map<IASTNode, String>>(
				new HashMap<>(), new HashMap<>());

		final Deque<WitnessNode> worklist = new ArrayDeque<>();
		final Set<WitnessNode> closed = new HashSet<>();
		worklist.add(mWitnessNode);
		int successCounter = 0;
		int failCounter = 0;
		while (!worklist.isEmpty()) {
			final WitnessNode current = worklist.remove();
			if (!closed.add(current)) {
				continue;
			}
			worklist.addAll(current.getOutgoingNodes());
			switch (extractNode(current, rtr)) {
			case EXTRACTED:
				++successCounter;
				break;
			case NOT_EXTRACTED:
				++failCounter;
				break;
			default:
				break;
			}
		}

		mLogger.info("Processed " + closed.size() + " nodes");
		mLogger.info("Extracted " + successCounter + " invariants");
		if (failCounter > 0) {
			mLogger.info("Could not extract " + failCounter + " invariants");
		} else {
			mLogger.info("Extracted all invariants");
		}
		printResults(rtr);

		return rtr;
	}

	private void printResults(final Pair<Map<IASTNode, String>, Map<IASTNode, String>> rtr) {
		final Map<IASTNode, String> before = rtr.getFirst();
		final Map<IASTNode, String> after = rtr.getSecond();
		if (before.isEmpty() && after.isEmpty()) {
			mLogger.info("Witness did not contain any usable invariants.");
			return;
		}
		mLogger.info("Found the following invariants in the witness:");
		for (final Entry<IASTNode, String> entry : before.entrySet()) {
			mLogger.info(toLogStringCNode("Before", entry.getKey(), entry.getValue()));
		}
		for (final Entry<IASTNode, String> entry : after.entrySet()) {
			mLogger.info(toLogStringCNode("After", entry.getKey(), entry.getValue()));
		}
	}

	/**
	 * @return true iff an invariant was extracted, false otherwise.
	 */
	private ExtractionResult extractNode(final WitnessNode current,
			final Pair<Map<IASTNode, String>, Map<IASTNode, String>> rtr) {
		final WitnessNodeAnnotation annot = WitnessNodeAnnotation.getAnnotation(current);
		if (annot == null) {
			return ExtractionResult.NOT_RELEVANT;
		}
		final String invariant = annot.getInvariant();
		if (invariant == null || invariant.equalsIgnoreCase("true")) {
			return ExtractionResult.NOT_RELEVANT;
		}
		final Pair<List<IASTNode>, List<IASTNode>> nodes = matchASTNodes(current);
		if (nodes == null || (nodes.getFirst().isEmpty() && nodes.getSecond().isEmpty())) {
			mLogger.error("Could not match witness node to AST node: " + current);
			return ExtractionResult.NOT_EXTRACTED;
		}

		for (final IASTNode node : nodes.getFirst()) {
			addInvariants(rtr.getFirst(), invariant, node, current);
		}
		for (final IASTNode node : nodes.getSecond()) {
			addInvariants(rtr.getSecond(), invariant, node, current);
		}
		return ExtractionResult.EXTRACTED;
	}

	private void addInvariants(final Map<IASTNode, String> rtr, final String invariant, final IASTNode node,
			final WitnessNode current) {
		final String oldInvariant = rtr.put(node, invariant);
		if (oldInvariant != null) {
			final String newInvariant = "(" + invariant + ") || (" + oldInvariant + ")";
			mLogger.warn("Already matched invariant to C node [" + node.getFileLocation().getStartingLineNumber() + "] "
					+ node.getRawSignature());
			mLogger.warn("  Witness node label is " + current);
			mLogger.warn("  Replacing invariant " + oldInvariant + " with invariant " + newInvariant);
			rtr.put(node, newInvariant);
		}
	}

	private Pair<List<IASTNode>, List<IASTNode>> matchASTNodes(final WitnessNode wnode) {
		final Set<Integer> afterLines = wnode.getIncomingEdges().stream().map(a -> a.getLocation().getEndLine())
				.collect(Collectors.toSet());
		final Set<Integer> beforeLines = wnode.getOutgoingEdges().stream().map(a -> a.getLocation().getStartLine())
				.collect(Collectors.toSet());

		// remove the line number that is used for "no line number"
		afterLines.remove(-1);
		beforeLines.remove(-1);

		if (afterLines.size() == 0 && beforeLines.size() == 0) {
			mLogger.error("No line numbers found for " + wnode);
			return null;
		}

		final LineMatchingVisitor matcher = new LineMatchingVisitor(beforeLines, afterLines);
		matcher.run(mTranslationUnit);

		final Pair<List<IASTNode>, List<IASTNode>> matchedNodes = matcher.getMatchedNodes();

		// filter matches s.t. edges that cross procedure boundaries are eliminated
		filterBeforeMatches(wnode, matchedNodes);

		boolean printlabel = false;
		if (matchedNodes.getFirst().isEmpty() && !beforeLines.isEmpty()) {
			mLogger.warn(
					"Could not match AST node to invariant before witness lines " + toStringCollection(beforeLines));
			printlabel = true;
		}
		if (matchedNodes.getSecond().isEmpty() && !afterLines.isEmpty()) {
			mLogger.warn("Could not match AST node to invariant after witness lines " + toStringCollection(afterLines));
			printlabel = true;
		}
		if (printlabel) {
			mLogger.warn("  Witness node label is " + wnode.getLabel());
		}

		return matchedNodes;
	}

	private void filterBeforeMatches(final WitnessNode wnode, final Pair<List<IASTNode>, List<IASTNode>> matchedNodes) {
		final Iterator<IASTNode> beforeIter = matchedNodes.getFirst().iterator();
		while (beforeIter.hasNext()) {
			final IASTNode beforeCurrent = beforeIter.next();
			final IASTDeclaration beforeScope = determineScope(beforeCurrent);
			 if (beforeScope == null) {
			 // its the global scope
			 continue;
			 }
			for (final IASTNode afterCurrent : matchedNodes.getSecond()) {
				final IASTDeclaration afterScope = determineScope(afterCurrent);
				if (afterScope == null) {
					// its the global scope
					continue;
				}
				if (beforeScope != afterScope) {
					mLogger.warn("Removing invariant match "
							+ toLogStringCNode("Before", beforeCurrent,
									WitnessNodeAnnotation.getAnnotation(wnode).getInvariant())
							+ " because scopes differ: " + toLogString(beforeScope, afterScope));
					beforeIter.remove();
					break;
				}
			}
		}
	}

	private String toLogString(IASTNode bScope, IASTNode aScope) {
		String bScopeId = bScope == null ? "Global" : "L" + bScope.getFileLocation().getStartingLineNumber();
		String aScopeId = aScope == null ? "Global" : "L" + aScope.getFileLocation().getStartingLineNumber();
		return "B=" + bScopeId + ", A=" + aScopeId;
	}

	private IASTDeclaration determineScope(final IASTNode current) {
		IASTNode parent = current.getParent();
		while (parent != null) {
			if (parent instanceof IASTFunctionDefinition) {
				return (IASTDeclaration) parent;
			}
			if (parent instanceof IASTTranslationUnit) {
				return null;
			}
			parent = parent.getParent();
		}

		return null;
	}

	private String toStringCollection(final Collection<?> lines) {
		return String.join(", ", lines.stream().map(a -> String.valueOf(a)).collect(Collectors.toList()));
	}

	private String toLogStringCNode(final String prefix, final IASTNode node, final String invariant) {
		return prefix + " [L" + node.getFileLocation().getStartingLineNumber() + "] " + node.getRawSignature()
				+ " invariant is " + invariant;
	}

	private final static class LineMatchingVisitor extends ASTGenericVisitor {

		private final Set<Integer> mBeforeLines;
		private final Set<Integer> mAfterLines;
		private final Pair<List<IASTNode>, List<IASTNode>> mMatchedNodes;

		public LineMatchingVisitor(final Set<Integer> beforeLines, final Set<Integer> afterLines) {
			super(true);
			mBeforeLines = beforeLines;
			mAfterLines = afterLines;
			mMatchedNodes = new Pair<List<IASTNode>, List<IASTNode>>(new ArrayList<>(), new ArrayList<>());
		}

		public void run(IASTTranslationUnit translationUnit) {
			translationUnit.accept(this);
			removeSubtreeMatches(mMatchedNodes.getFirst());
			removeSubtreeMatches(mMatchedNodes.getSecond());
		}

		private Pair<List<IASTNode>, List<IASTNode>> getMatchedNodes() {
			return mMatchedNodes;
		}

		@Override
		protected int genericVisit(IASTNode node) {
			if (match(node)) {
				return PROCESS_SKIP;
			}
			return PROCESS_CONTINUE;
		}

		private boolean match(IASTNode node) {
			final IASTFileLocation loc = node.getFileLocation();
			if (loc == null) {
				return false;
			}
			final int startLine = loc.getStartingLineNumber();
			final int endLine = loc.getEndingLineNumber();

			boolean matched = false;
			if (mBeforeLines.contains(startLine)) {
				mMatchedNodes.getFirst().add(node);
				matched = true;
			}
			if (mAfterLines.contains(endLine)) {
				mMatchedNodes.getSecond().add(node);
				matched = true;
			}
			return matched;
		}

		/**
		 * Remove all nodes from a list of {@link IASTNode}s where the parent of a node is also in the list.
		 */
		private void removeSubtreeMatches(final List<IASTNode> list) {
			final Iterator<IASTNode> iter = list.iterator();
			while (iter.hasNext()) {
				final IASTNode current = iter.next();
				if (list.stream().filter(a -> a != current).anyMatch(a -> isContainedInSubtree(current, a))) {
					iter.remove();
				}
			}
		}

		private boolean isContainedInSubtree(final IASTNode candidate, final IASTNode possibleParent) {
			final SubtreeChecker sc = new SubtreeChecker(candidate);
			possibleParent.accept(sc);
			return sc.isContainedInSubtree();
		}

		private final static class SubtreeChecker extends ASTGenericVisitor {

			private final IASTNode mCandidate;
			private boolean mIsContainedInSubtree;

			public SubtreeChecker(final IASTNode candidate) {
				super(true);
				mCandidate = candidate;
				mIsContainedInSubtree = false;
			}

			public boolean isContainedInSubtree() {
				return mIsContainedInSubtree;
			}

			@Override
			protected int genericVisit(IASTNode child) {
				if (mIsContainedInSubtree) {
					return PROCESS_SKIP;
				}
				if (child == mCandidate) {
					mIsContainedInSubtree = true;
					return PROCESS_SKIP;
				}
				return PROCESS_CONTINUE;
			}
		}
	}

	private enum ExtractionResult {
		/**
		 * The invariant was true and is therefore not relevant.
		 */
		NOT_RELEVANT,
		/**
		 * We could extract a relevant invariant.
		 */
		EXTRACTED,
		/**
		 * We could not extract a relevant invariant.
		 */
		NOT_EXTRACTED

	}
}
