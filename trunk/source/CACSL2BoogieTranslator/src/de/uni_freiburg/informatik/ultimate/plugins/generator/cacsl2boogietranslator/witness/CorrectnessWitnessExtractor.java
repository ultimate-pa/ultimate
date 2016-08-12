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

package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import org.eclipse.cdt.core.dom.ast.ASTGenericVisitor;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTGotoStatement;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Activator;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdgeAnnotation;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNodeAnnotation;
import de.uni_freiburg.informatik.ultimate.witnessparser.preferences.WitnessParserPreferences;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class CorrectnessWitnessExtractor {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final boolean mCheckOnlyLoopInvariants;

	private WitnessNode mWitnessNode;
	private IASTTranslationUnit mTranslationUnit;
	private Map<IASTNode, ExtractedWitnessInvariant> mAST2Invariant;

	public CorrectnessWitnessExtractor(final IUltimateServiceProvider service) {
		mServices = service;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mCheckOnlyLoopInvariants = WitnessParserPreferences.getPrefs(service)
				.getBoolean(WitnessParserPreferences.LABEL_CW_USE_ONLY_LOOPINVARIANTS);
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
	 * @return a map from {@link IASTNode} to an {@link ExtractedWitnessInvariant}. The
	 *         {@link ExtractedWitnessInvariant} represents a witness invariant which has to hold before, at, or after
	 *         the {@link IASTNode}.
	 */
	public Map<IASTNode, ExtractedWitnessInvariant> getCorrectnessWitnessInvariants() {
		if (mAST2Invariant == null) {
			mAST2Invariant = extract();
		}
		return mAST2Invariant;
	}

	private Map<IASTNode, ExtractedWitnessInvariant> extract() {
		if (!isReady()) {
			mLogger.warn("Cannot extract witness if there is no witness");
			return null;
		}
		if (mCheckOnlyLoopInvariants) {
			mLogger.info("Only extracting loop invariants from correctness witness");
		} else {
			mLogger.info("Extracting all invariants from correctness witness");
		}

		Map<IASTNode, ExtractedWitnessInvariant> rtr = new HashMap<>();

		final ExtractionStatistics stats = new ExtractionStatistics();
		final Deque<WitnessNode> worklist = new ArrayDeque<>();
		final Set<WitnessNode> closed = new HashSet<>();
		worklist.add(mWitnessNode);
		while (!worklist.isEmpty()) {
			final WitnessNode current = worklist.remove();
			if (!closed.add(current)) {
				continue;
			}
			worklist.addAll(current.getOutgoingNodes());
			final Map<IASTNode, ExtractedWitnessInvariant> match = matchWitnessToAstNode(current, stats);
			rtr = mergeMatchesIfNecessary(rtr, match);
		}

		mLogger.info("Processed " + closed.size() + " nodes");
		mLogger.info("WitnessExtracted=" + stats.getSuccess());
		mLogger.info("WitnessTotal=" + stats.getTotal());
		if (stats.getFailure() > 0) {
			mLogger.info("Could not extract " + stats.getFailure() + " invariants");
		} else {
			mLogger.info("Extracted all invariants");
		}
		printResults(rtr);

		return rtr;
	}

	private void printResults(final Map<IASTNode, ExtractedWitnessInvariant> result) {
		if (result.isEmpty()) {
			mLogger.info("Witness did not contain any usable invariants.");
			return;
		}
		mLogger.info("Found the following invariants in the witness:");
		for (final Entry<IASTNode, ExtractedWitnessInvariant> entry : result.entrySet()) {
			assert entry.getKey() == entry.getValue().getRelatedAstNode();
			mLogger.info(entry.getValue().toStringWithCNode());
		}
	}

	private Map<IASTNode, ExtractedWitnessInvariant> matchWitnessToAstNode(final WitnessNode current,
			final ExtractionStatistics stats) {
		final WitnessNodeAnnotation annot = WitnessNodeAnnotation.getAnnotation(current);
		if (annot == null) {
			return Collections.emptyMap();
		}
		final String invariant = annot.getInvariant();
		if (invariant == null || invariant.equalsIgnoreCase("true")) {
			return Collections.emptyMap();
		}
		final Map<IASTNode, ExtractedWitnessInvariant> ast2invariant = matchWitnessToAstNode(current);
		if (ast2invariant == null || ast2invariant.isEmpty()) {
			mLogger.error("Could not match witness node to AST node: " + current);
			stats.fail();
			return Collections.emptyMap();
		}
		stats.success();
		return ast2invariant;
	}

	private Map<IASTNode, ExtractedWitnessInvariant> matchWitnessToAstNode(final WitnessNode wnode) {
		final Set<Integer> afterLines = collectLineNumbers(wnode.getIncomingEdges(), a -> a.getEndLine());
		final Set<Integer> beforeLines = collectLineNumbers(wnode.getOutgoingEdges(), a -> a.getStartLine());

		if (afterLines.isEmpty() && beforeLines.isEmpty()) {
			mLogger.error("No line numbers found for " + wnode);
			return null;
		}

		final Set<IASTNode> beforeNodes = matchLines(beforeLines, a -> a.getStartingLineNumber());
		final Set<IASTNode> afterNodes = matchLines(afterLines, a -> a.getEndingLineNumber());

		// filter matches s.t. edges that cross procedure boundaries are eliminated
		filterScopeChanges(wnode, beforeNodes, afterNodes);

		boolean printlabel = false;
		if (beforeNodes.isEmpty() && !beforeLines.isEmpty()) {
			mLogger.warn(
					"Could not match AST node to invariant before witness lines " + toStringCollection(beforeLines));
			printlabel = true;
		}
		if (afterNodes.isEmpty() && !afterLines.isEmpty()) {
			mLogger.warn("Could not match AST node to invariant after witness lines " + toStringCollection(afterLines));
			printlabel = true;
		}
		if (printlabel) {
			mLogger.warn("  Witness node label is " + wnode.getLabel());
		}
		final Map<IASTNode, ExtractedWitnessInvariant> possibleMatches =
				extractInvariants(wnode, beforeNodes, afterNodes);
		return possibleMatches;
	}

	private Map<IASTNode, ExtractedWitnessInvariant> extractInvariants(final WitnessNode wnode,
			final Set<IASTNode> beforeNodes, final Set<IASTNode> afterNodes) {
		final String invariant = WitnessNodeAnnotation.getAnnotation(wnode).getInvariant();
		// new WitnessInvariant(invariant, wnode.getLabel(), match, isBefore, isAfter, isAt)
		final Set<IASTNode> beforeMatches =
				beforeNodes.stream().filter(a -> !afterNodes.contains(a)).collect(Collectors.toSet());
		final Set<IASTNode> atMatches = beforeNodes.stream().filter(afterNodes::contains).collect(Collectors.toSet());
		final Set<IASTNode> afterMatches =
				afterNodes.stream().filter(a -> !beforeNodes.contains(a)).collect(Collectors.toSet());
		final Map<IASTNode, ExtractedWitnessInvariant> rtr = new HashMap<>();
		if (mCheckOnlyLoopInvariants) {
			if (!beforeMatches.isEmpty() || !afterMatches.isEmpty()) {
				// if there is some match in the difference, we did not match a loop invariant with 100% certainty.
				// we know that we should match loop heads, so we can search for goto-statements and match directly to
				// them (somewhat hacky)

				final Set<IASTNode> gotos = new HashSet<>();
				for (final IASTNode node : beforeMatches) {
					gotos.addAll(new GotoExtractor().run(node));
				}
				for (final IASTNode node : afterMatches) {
					gotos.addAll(new GotoExtractor().run(node));
				}
				if (!gotos.isEmpty()) {
					// we found some gotos, hooray
					return extractInvariants(wnode, gotos, gotos);
				}

				mLogger.warn("Ignoring possible match because exact match is not possible ");
				mLogger.warn("Before-Matches:");
				beforeMatches
						.stream().map(a -> new ExtractedWitnessInvariant(invariant,
								Collections.singletonList(wnode.getName()), a, true, false, false))
						.forEach(a -> mLogger.warn(a.toStringWithCNode()));
				mLogger.warn("After-Matches:");
				afterMatches
						.stream().map(a -> new ExtractedWitnessInvariant(invariant,
								Collections.singletonList(wnode.getName()), a, true, false, false))
						.forEach(a -> mLogger.warn(a.toStringWithCNode()));
				return rtr;
			}
		} else {
			beforeMatches
					.stream().map(a -> new ExtractedWitnessInvariant(invariant,
							Collections.singletonList(wnode.getName()), a, true, false, false))
					.forEach(a -> rtr.put(a.getRelatedAstNode(), a));
			afterMatches
					.stream().map(a -> new ExtractedWitnessInvariant(invariant,
							Collections.singletonList(wnode.getName()), a, false, false, true))
					.forEach(a -> rtr.put(a.getRelatedAstNode(), a));
		}
		atMatches.stream().map(a -> new ExtractedWitnessInvariant(invariant, Collections.singletonList(wnode.getName()),
				a, true, true, true)).forEach(a -> rtr.put(a.getRelatedAstNode(), a));
		return rtr;
	}

	private Map<IASTNode, ExtractedWitnessInvariant> mergeMatchesIfNecessary(
			final Map<IASTNode, ExtractedWitnessInvariant> mapA, final Map<IASTNode, ExtractedWitnessInvariant> mapB) {
		if (mapA == null || mapA.isEmpty()) {
			return mapB;
		}
		if (mapB == null || mapB.isEmpty()) {
			return mapA;
		}
		if (mapA.size() < mapB.size()) {
			return mergeMatchesIfNecessary(mapB, mapA);
		}

		final Map<IASTNode, ExtractedWitnessInvariant> rtr = new HashMap<>(mapA.size());
		for (final Entry<IASTNode, ExtractedWitnessInvariant> entryB : mapB.entrySet()) {
			final ExtractedWitnessInvariant aWitnessInvariant = mapA.get(entryB.getKey());
			if (aWitnessInvariant == null) {
				rtr.put(entryB.getKey(), entryB.getValue());
			} else {
				final ExtractedWitnessInvariant bWitnessInvariant = entryB.getValue();
				final ExtractedWitnessInvariant newInvariant = bWitnessInvariant.merge(aWitnessInvariant);
				mLogger.warn("Merging invariants");
				mLogger.warn("  Invariant A is " + aWitnessInvariant.toString());
				mLogger.warn("  Invariant B is " + bWitnessInvariant.toString());
				mLogger.warn("  New match: " + newInvariant.toStringWithCNode());
				rtr.put(entryB.getKey(), newInvariant);
			}
		}
		return rtr;
	}

	private Set<IASTNode> matchLines(final Set<Integer> lines, final Function<IASTFileLocation, Integer> funGetLine) {
		final LineMatchingVisitor matcher = new LineMatchingVisitor(lines, funGetLine);
		matcher.run(mTranslationUnit);
		return matcher.getMatchedNodes();
	}

	private Set<Integer> collectLineNumbers(final List<WitnessEdge> edges,
			final Function<ILocation, Integer> loc2linenumber) {
		final Set<Integer> lines;
		if (mCheckOnlyLoopInvariants) {
			// consider only edges that enter a loop head
			lines = edges.stream().filter(a -> WitnessEdgeAnnotation.getAnnotation(a).getEnterLoopHead())
					.map(a -> loc2linenumber.apply(a.getLocation())).collect(Collectors.toSet());
		} else {
			lines = edges.stream().map(a -> loc2linenumber.apply(a.getLocation())).collect(Collectors.toSet());
		}
		// remove the line number that is used to mark "no line number"
		lines.remove(-1);
		return lines;
	}

	/**
	 * Remove all {@link IASTNode}s from the <code>before</code> list if there is a node in the <code>after</code> list
	 * that has a different scope, except if the "before" node is in the global scope.
	 */
	private void filterScopeChanges(final WitnessNode wnode, final Collection<IASTNode> before,
			final Collection<IASTNode> after) {
		// collect all scopes from the after list
		final Set<IASTDeclaration> afterScopes =
				after.stream().map(a -> determineScope(a)).filter(a -> a != null).collect(Collectors.toSet());

		// iterate over before list and remove all matches that would lead to a scope change
		final Iterator<IASTNode> beforeIter = before.iterator();
		while (beforeIter.hasNext()) {
			final IASTNode beforeCurrent = beforeIter.next();
			final IASTDeclaration beforeScope = determineScope(beforeCurrent);
			if (beforeScope == null) {
				// its the global scope
				continue;
			}
			final Optional<IASTDeclaration> scopeChange = afterScopes.stream().filter(a -> a != beforeScope).findAny();
			if (scopeChange.isPresent()) {
				mLogger.warn("Removing invariant match " + wnode.getLabel() + ": "
						+ WitnessNodeAnnotation.getAnnotation(wnode).getInvariant() + " because scopes differ: "
						+ toLogString(beforeScope, scopeChange.get()));
				beforeIter.remove();
			}
		}
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

	private String toLogString(final IASTNode bScope, final IASTNode aScope) {
		final String bScopeId = bScope == null ? "Global" : ("L" + bScope.getFileLocation().getStartingLineNumber());
		final String aScopeId = aScope == null ? "Global" : ("L" + aScope.getFileLocation().getStartingLineNumber());
		return "B=" + bScopeId + ", A=" + aScopeId;
	}

	private String toStringCollection(final Collection<?> lines) {
		return String.join(", ", lines.stream().map(a -> String.valueOf(a)).collect(Collectors.toList()));
	}

	private static final class GotoExtractor extends ASTGenericVisitor {
		private Set<IASTGotoStatement> mGotoStatements;

		public GotoExtractor() {
			super(true);
		}

		public Set<IASTGotoStatement> run(final IASTNode subtreeRoot) {
			mGotoStatements = new HashSet<>();
			subtreeRoot.accept(this);
			return mGotoStatements;
		}

		@Override
		public int visit(final IASTStatement statement) {
			if (statement instanceof IASTGotoStatement) {
				mGotoStatements.add((IASTGotoStatement) statement);
				return PROCESS_SKIP;
			}
			return PROCESS_CONTINUE;
		}
	}

	private static final class LineMatchingVisitor extends ASTGenericVisitor {

		private final Set<Integer> mBeforeLines;
		private final Set<IASTNode> mMatchedNodes;
		private final Function<IASTFileLocation, Integer> mFunGetLine;

		public LineMatchingVisitor(final Set<Integer> lines, final Function<IASTFileLocation, Integer> funGetLine) {
			super(true);
			mBeforeLines = lines;
			mMatchedNodes = new HashSet<>();
			mFunGetLine = funGetLine;
		}

		public void run(final IASTTranslationUnit translationUnit) {
			translationUnit.accept(this);
			removeSubtreeMatches(mMatchedNodes);
		}

		private Set<IASTNode> getMatchedNodes() {
			return mMatchedNodes;
		}

		@Override
		protected int genericVisit(final IASTNode node) {
			if (match(node)) {
				// skip the subtree if a match occurred, but continue with siblings.
				return PROCESS_SKIP;
			}
			return PROCESS_CONTINUE;
		}

		private boolean match(final IASTNode node) {
			final IASTFileLocation loc = node.getFileLocation();
			if (loc == null) {
				return false;
			}
			final int line = mFunGetLine.apply(loc);
			if (mBeforeLines.contains(line)) {
				mMatchedNodes.add(node);
				return true;
			}
			return false;
		}

		/**
		 * Remove all nodes from a list of {@link IASTNode}s where the parent of a node is also in the list.
		 */
		private void removeSubtreeMatches(final Collection<IASTNode> list) {
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
	}

	private static final class SubtreeChecker extends ASTGenericVisitor {

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
		protected int genericVisit(final IASTNode child) {
			if (mIsContainedInSubtree) {
				return PROCESS_ABORT;
			}
			if (child == mCandidate) {
				mIsContainedInSubtree = true;
				return PROCESS_ABORT;
			}
			return PROCESS_CONTINUE;
		}
	}

	private static final class ExtractionStatistics {
		private int mSuccess;
		private int mFailure;

		private ExtractionStatistics() {
			mSuccess = 0;
			mFailure = 0;
		}

		private void success() {
			mSuccess++;
		}

		private void fail() {
			mFailure++;
		}

		public int getSuccess() {
			return mSuccess;
		}

		public int getFailure() {
			return mFailure;
		}

		public int getTotal() {
			return mSuccess + mFailure;
		}
	}
}
