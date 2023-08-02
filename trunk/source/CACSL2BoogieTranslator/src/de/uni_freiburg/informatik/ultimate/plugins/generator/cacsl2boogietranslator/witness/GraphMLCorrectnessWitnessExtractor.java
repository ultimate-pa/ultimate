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
import java.util.Arrays;
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
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.eclipse.cdt.core.dom.ast.ASTGenericVisitor;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDoStatement;
import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTGotoStatement;
import org.eclipse.cdt.core.dom.ast.IASTIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IASTWhileStatement;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.CdtASTUtils;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdgeAnnotation;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNodeAnnotation;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class GraphMLCorrectnessWitnessExtractor extends CorrectnessWitnessExtractor {
	private WitnessNode mWitnessNode;
	private final Collection<Class<?>> mLoopTypes;
	private final Collection<Class<?>> mConditionalTypes;

	public GraphMLCorrectnessWitnessExtractor(final IUltimateServiceProvider service) {
		super(service);
		mLoopTypes = Arrays.asList(new Class[] { IASTGotoStatement.class, IASTDoStatement.class,
				IASTWhileStatement.class, IASTForStatement.class });
		mConditionalTypes = Arrays.asList(new Class[] { IASTDoStatement.class, IASTWhileStatement.class,
				IASTForStatement.class, IASTIfStatement.class });
	}

	public void setWitness(final WitnessNode wnode) {
		mWitnessNode = wnode;
	}

	@Override
	public boolean isReady() {
		return mWitnessNode != null && mTranslationUnit != null;
	}

	@Override
	protected HashRelation<IASTNode, ExtractedWitnessInvariant> extract() {
		Map<IASTNode, ExtractedWitnessInvariant> map = new HashMap<>();

		final Deque<WitnessNode> worklist = new ArrayDeque<>();
		final Set<WitnessNode> closed = new HashSet<>();
		worklist.add(mWitnessNode);
		while (!worklist.isEmpty()) {
			final WitnessNode current = worklist.remove();
			if (!closed.add(current)) {
				continue;
			}
			worklist.addAll(current.getOutgoingNodes());
			final Map<IASTNode, ExtractedWitnessInvariant> match = matchWitnessToAstNode(current, mStats);
			map = mergeMatchesIfNecessary(map, match);
		}
		final HashRelation<IASTNode, ExtractedWitnessInvariant> rtr = new HashRelation<>();
		map.forEach(rtr::addPair);
		mLogger.info("Processed " + closed.size() + " nodes");
		return rtr;
	}

	protected Map<IASTNode, ExtractedWitnessInvariant> mergeMatchesIfNecessary(
			final Map<IASTNode, ExtractedWitnessInvariant> mapA, final Map<IASTNode, ExtractedWitnessInvariant> mapB) {
		if (mapA == null || mapA.isEmpty()) {
			return mapB;
		}
		if (mapB == null || mapB.isEmpty()) {
			return mapA;
		}

		final Map<IASTNode, ExtractedWitnessInvariant> rtr = new HashMap<>(mapA.size());
		for (final Entry<IASTNode, ExtractedWitnessInvariant> entryB : mapB.entrySet()) {
			final ExtractedWitnessInvariant aWitnessInvariant = mapA.get(entryB.getKey());
			if (aWitnessInvariant == null) {
				rtr.put(entryB.getKey(), entryB.getValue());
			} else {
				rtr.put(entryB.getKey(), mergeAndWarn(aWitnessInvariant, entryB.getValue()));
			}
		}
		for (final Entry<IASTNode, ExtractedWitnessInvariant> entryA : mapA.entrySet()) {
			final ExtractedWitnessInvariant aWitnessInvariant = mapB.get(entryA.getKey());
			if (aWitnessInvariant == null) {
				rtr.put(entryA.getKey(), entryA.getValue());
			} else {
				// we already merged in the earlier pass
			}
		}
		return rtr;
	}

	private ExtractedWitnessInvariant mergeAndWarn(final ExtractedWitnessInvariant invA,
			final ExtractedWitnessInvariant invB) {
		final ExtractedWitnessInvariant newInvariant = mergeInvariants(invA, invB);
		mLogger.warn("Merging invariants");
		mLogger.warn("  Invariant A is " + invA.toString());
		mLogger.warn("  Invariant B is " + invB.toString());
		mLogger.warn("  New match: " + newInvariant.toString());
		return newInvariant;
	}

	private static ExtractedWitnessInvariant mergeInvariants(final ExtractedWitnessInvariant ewi1,
			final ExtractedWitnessInvariant ewi2) {
		if (ewi2 == null) {
			return ewi1;
		}
		if (ewi1.getRelatedAstNode() != ewi2.getRelatedAstNode()) {
			throw new IllegalArgumentException("Cannot merge WitnessInvariants that are matched to different nodes");
		}
		final String invariant1 = ewi1.getInvariant();
		final String invariant2 = ewi2.getInvariant();
		String newInvariant;
		if (invariant1.equals(invariant2)) {
			newInvariant = invariant1;
		} else {
			final StringBuilder builder = new StringBuilder();
			builder.append('(');
			builder.append(invariant1);
			builder.append(')');
			builder.append("||");
			builder.append('(');
			builder.append(invariant2);
			builder.append(')');
			newInvariant = builder.toString();
		}

		final Set<String> newNodeLabels = DataStructureUtils.union(ewi1.getNodeLabels(), ewi2.getNodeLabels());

		return new ExtractedWitnessInvariant(newInvariant, newNodeLabels, ewi1.getRelatedAstNode(), ewi1.isBefore(),
				ewi1.isAfter(), ewi1.isAt());
	}

	private Map<IASTNode, ExtractedWitnessInvariant> matchWitnessToAstNode(final WitnessNode current,
			final ExtractionStatistics stats) {
		final WitnessNodeAnnotation annot = WitnessNodeAnnotation.getAnnotation(current);
		if (annot == null) {
			return Collections.emptyMap();
		}
		final String invariant = annot.getInvariant();
		if (invariant == null || "true".equalsIgnoreCase(invariant)) {
			return Collections.emptyMap();
		}
		final Map<IASTNode, ExtractedWitnessInvariant> ast2invariant = matchWitnessToAstNode(current);
		if (ast2invariant == null || ast2invariant.isEmpty()) {
			mLogger.error("Could not match witness node to any AST node: " + current);
			stats.fail();
			return Collections.emptyMap();
		}
		stats.success();
		return ast2invariant;
	}

	private Map<IASTNode, ExtractedWitnessInvariant> matchWitnessToAstNode(final WitnessNode wnode) {
		final Set<DecoratedWitnessEdge> edges = new HashSet<>();
		edges.addAll(convertAndFilterEdges(wnode.getIncomingEdges(), true));
		edges.addAll(convertAndFilterEdges(wnode.getOutgoingEdges(), false));

		if (edges.isEmpty()) {
			mLogger.error("No line numbers found for " + wnode);
			return null;
		}
		final DecoratedWitnessNode dwnode = new DecoratedWitnessNode(wnode);
		final Set<MatchedASTNode> candidateNodes = matchLines(edges);

		boolean printlabel = false;
		if (!mCheckOnlyLoopInvariants) {
			// While trying to match loop invariants, we should ignore incoming edges
			// because if the incoming edge comes from a preceding loop, we will match the
			// the invariant to the wrong loop.
			final Set<DecoratedWitnessEdge> incomingEdges = getIncomingSet(edges);
			if (candidateNodes.stream().allMatch(a -> !a.isIncoming()) && !incomingEdges.isEmpty()) {
				mLogger.warn("Could not match AST node to invariant before witness lines "
						+ toStringCollection(incomingEdges));
				printlabel = true;
			}
		}

		final Set<DecoratedWitnessEdge> outgoingEdges = getOutgoingSet(edges);
		if (candidateNodes.stream().allMatch(a -> a.isIncoming()) && !outgoingEdges.isEmpty()) {
			mLogger.warn(
					"Could not match AST node to invariant after witness lines " + toStringCollection(outgoingEdges));
			printlabel = true;
		}
		if (printlabel) {
			mLogger.warn("  Witness node label is " + dwnode);
		}
		final Map<IASTNode, ExtractedWitnessInvariant> possibleMatches = extractInvariants(dwnode, candidateNodes);
		return possibleMatches;
	}

	private Map<IASTNode, ExtractedWitnessInvariant> extractInvariants(final DecoratedWitnessNode dwnode,
			final Set<MatchedASTNode> candidateNodes) {

		// filter matches s.t. edges that cross procedure boundaries are eliminated
		filterScopeChanges(dwnode, candidateNodes);

		Map<IASTNode, ExtractedWitnessInvariant> rtr = new HashMap<>();
		rtr = mergeMatchesIfNecessary(rtr, extractLoopInvariants(dwnode, candidateNodes));

		if (mCheckOnlyLoopInvariants) {
			// we already extracted all the loop invariants
			mLogger.warn("The following possible matches for " + dwnode
					+ " were ignored because we could not match them to a loop:");
			candidateNodes.stream().forEach(a -> mLogger.warn("  " + a.toStringSimple()));
			return rtr;
		}
		rtr = mergeMatchesIfNecessary(rtr, extractStatementInvariants(dwnode, candidateNodes));
		return rtr;
	}

	private Map<IASTNode, ExtractedWitnessInvariant> extractLoopInvariants(final DecoratedWitnessNode dwnode,
			final Set<MatchedASTNode> candidateNodes) {
		final Set<MatchedASTNode> loopHeads;
		if (mCheckOnlyLoopInvariants) {
			loopHeads = new HashSet<>(candidateNodes);
		} else {
			// TODO 20221126 Matthias: This filter excludes all outgoing edges of a loop
			// head which makes it more difficult to find a match.
			loopHeads = candidateNodes.stream().filter(a -> a.isLoopHead()).collect(Collectors.toSet());
		}
		candidateNodes.removeAll(loopHeads);

		final Map<IASTNode, ExtractedWitnessInvariant> down = tryMatchLoopInvariantsDownwards(dwnode, loopHeads);
		if (loopHeads.isEmpty()) {
			// downward matching matched everything, nothing more to do.
			return down;
		}
		if (!down.isEmpty()) {
			// if downward matched something, we take this as it is most likely the correct loop -- we only use upward
			// matching if downward matching failed completely.
			mLogger.warn("Downward matching could not match all canidates");
			return down;
		}
		mLogger.warn("Downward matching could not match anything");

		// try to match the remaining loop heads upwards
		final Map<IASTNode, ExtractedWitnessInvariant> up = tryMatchLoopInvariantsUpwards(dwnode, loopHeads);
		if (!loopHeads.isEmpty()) {
			mLogger.warn("Could not match the following loop heads:");
			loopHeads.stream().forEach(a -> mLogger.warn("  " + a.toStringSimple()));
			candidateNodes.addAll(loopHeads);
		}
		return mergeMatchesIfNecessary(down, up);
	}

	private Map<IASTNode, ExtractedWitnessInvariant> tryMatchLoopInvariantsDownwards(final DecoratedWitnessNode dwnode,
			final Set<MatchedASTNode> loopHeads) {

		final Map<IASTNode, ExtractedWitnessInvariant> rtr = new HashMap<>();
		final Iterator<MatchedASTNode> iter = loopHeads.iterator();
		while (iter.hasNext()) {
			final MatchedASTNode loopHead = iter.next();
			final Set<IASTStatement> loopStatements = CdtASTUtils.findDesiredType(loopHead.getNode(), mLoopTypes);
			if (loopStatements.isEmpty()) {
				continue;
			}
			mLogger.info("Matched downward: " + loopHead.toStringSimple());
			loopStatements.stream()
					.map(a -> new ExtractedWitnessInvariant(dwnode.getInvariant(),
							Collections.singletonList(dwnode.getName()), a, false, false, true))
					.forEach(a -> rtr.put(a.getRelatedAstNode(), a));
			iter.remove();
		}
		return rtr;
	}

	private Map<IASTNode, ExtractedWitnessInvariant> tryMatchLoopInvariantsUpwards(final DecoratedWitnessNode dwnode,
			final Set<MatchedASTNode> loopHeads) {
		final Map<IASTNode, ExtractedWitnessInvariant> rtr = new HashMap<>();
		final IASTNode commonParent = findCommonParentStatement(loopHeads);
		if (commonParent == null) {
			// if there is no common parent, we cannot match upwards
			return rtr;
		}
		mLogger.info("Matched remaining loop heads upward to common parent of type "
				+ commonParent.getClass().getSimpleName());

		// check if the common parent or a parent of the common parent is a loop
		IASTNode currentParent = commonParent;
		Set<IASTStatement> loopStatements = Collections.emptySet();
		while (currentParent != null && currentParent instanceof IASTStatement) {
			loopStatements = CdtASTUtils.findDesiredType(currentParent, mLoopTypes);
			if (!loopStatements.isEmpty()) {
				break;
			}
			currentParent = currentParent.getParent();
		}
		if (loopStatements.isEmpty()) {
			return rtr;
		}
		loopStatements.stream()
				.map(a -> new ExtractedWitnessInvariant(dwnode.getInvariant(),
						Collections.singletonList(dwnode.getName()), a, false, false, true))
				.forEach(a -> rtr.put(a.getRelatedAstNode(), a));
		loopHeads.clear();
		return rtr;
	}

	private static Map<IASTNode, ExtractedWitnessInvariant>
			extractStatementInvariants(final DecoratedWitnessNode dwnode, final Set<MatchedASTNode> candidateNodes) {
		final Map<IASTNode, ExtractedWitnessInvariant> rtr = new HashMap<>();
		candidateNodes.stream()
				.map(a -> new ExtractedWitnessInvariant(dwnode.getInvariant(),
						Collections.singletonList(dwnode.getName()), a.getNode(), !a.isIncoming(), a.isIncoming(),
						false))
				.forEach(a -> rtr.put(a.getRelatedAstNode(), a));
		candidateNodes.clear();
		return rtr;
	}

	private Set<MatchedASTNode> matchLines(final Set<DecoratedWitnessEdge> edges) {
		final Set<MatchedASTNode> rtr = new HashSet<>();
		for (final DecoratedWitnessEdge edge : edges) {
			final LineMatchingVisitor matcher = new LineMatchingVisitor(edge);
			matcher.run(mTranslationUnit);
			rtr.addAll(matcher.getMatchedNodes());
		}
		return rtr;
	}

	/**
	 * Remove all witness edges that have no linenumber and convert the remaining to {@link DecoratedWitnessEdge}s.
	 */
	private static Set<DecoratedWitnessEdge> convertAndFilterEdges(final List<WitnessEdge> edges,
			final boolean isIncoming) {
		return edges.stream().map(a -> new DecoratedWitnessEdge(a, isIncoming)).filter(a -> !a.hasNoLineNumber())
				.collect(Collectors.toSet());
	}

	/**
	 * Remove all {@link IASTNode}s from the <code>before</code> list if there is a node in the <code>after</code> list
	 * that has a different scope, except if the "before" node is in the global scope.
	 */
	private void filterScopeChanges(final DecoratedWitnessNode wnode, final Collection<MatchedASTNode> nodes) {

		final Set<MatchedASTNode> after = getOutgoingSet(nodes);
		final Set<MatchedASTNode> before = getIncomingSet(nodes);

		// collect all scopes from the after list
		final Set<IASTDeclaration> afterScopes = after.stream().map(a -> CdtASTUtils.findScope(a.getNode()))
				.filter(a -> a != null).collect(Collectors.toSet());

		// iterate over before list and remove all matches that would lead to a scope change
		final Iterator<MatchedASTNode> beforeIter = before.iterator();
		while (beforeIter.hasNext()) {
			final MatchedASTNode beforeCurrent = beforeIter.next();
			final IASTDeclaration beforeScope = CdtASTUtils.findScope(beforeCurrent.getNode());
			if (beforeScope == null) {
				// its the global scope
				continue;
			}
			final Optional<IASTDeclaration> scopeChange = afterScopes.stream().filter(a -> a != beforeScope).findAny();
			if (scopeChange.isPresent()) {
				mLogger.warn("Removing invariant match " + wnode + ": " + wnode.getInvariant()
						+ " because scopes differ: " + toLogString(beforeScope, scopeChange.get()));
				beforeIter.remove();
			}
		}
	}

	private static IASTNode findCommonParentStatement(final Collection<MatchedASTNode> list) {
		if (list.isEmpty()) {
			throw new IllegalArgumentException("Empty collection cannot have a parent");
		}
		if (list.size() == 1) {
			// singleton is always its parent
			return list.iterator().next().getNode();
		}

		for (final MatchedASTNode currentParent : list) {
			if (list.stream().allMatch(a -> a == currentParent
					|| CdtASTUtils.isContainedInSubtree(a.getNode(), currentParent.getNode()))) {
				return currentParent.getNode();
			}
		}

		// if this is not the case, we know that one node in the path from the first element to the root has to be the
		// parent, or there is no common parent

		IASTNode possibleParent = list.iterator().next().getNode().getParent();
		while (possibleParent != null) {
			if (!(possibleParent instanceof IASTStatement)) {
				return null;
			}
			final IASTNode pParent = possibleParent;
			if (list.stream()
					.allMatch(a -> a.getNode() == pParent || CdtASTUtils.isContainedInSubtree(a.getNode(), pParent))) {
				return pParent;
			}
			possibleParent = possibleParent.getParent();
		}
		return null;
	}

	private static <T extends IHasIncoming> Stream<T> getIncomingStream(final Collection<T> edges) {
		return edges.stream().filter(a -> a.isIncoming());
	}

	private static <T extends IHasIncoming> Set<T> getIncomingSet(final Collection<T> edges) {
		return getIncomingStream(edges).collect(Collectors.toSet());
	}

	private static <T extends IHasIncoming> Stream<T> getOutgoingStream(final Collection<T> edges) {
		return edges.stream().filter(a -> !a.isIncoming());
	}

	private static <T extends IHasIncoming> Set<T> getOutgoingSet(final Collection<T> edges) {
		return getOutgoingStream(edges).collect(Collectors.toSet());
	}

	private static String toLogString(final IASTNode bScope, final IASTNode aScope) {
		final String bScopeId = bScope == null ? "Global" : ("L" + bScope.getFileLocation().getStartingLineNumber());
		final String aScopeId = aScope == null ? "Global" : ("L" + aScope.getFileLocation().getStartingLineNumber());
		return "B=" + bScopeId + ", A=" + aScopeId;
	}

	private static String toStringCollection(final Collection<?> stream) {
		return toStringCollection(stream.stream());
	}

	private static String toStringCollection(final Stream<?> stream) {
		return String.join(", ", stream.map(a -> String.valueOf(a)).collect(Collectors.toList()));
	}

	private final class LineMatchingVisitor extends ASTGenericVisitor {

		private final DecoratedWitnessEdge mEdge;
		private final Set<MatchedASTNode> mMatchedNodes;
		private final Predicate<IASTNode> mFunMatch;

		public LineMatchingVisitor(final DecoratedWitnessEdge edge) {
			super(true);
			mEdge = edge;
			mMatchedNodes = new HashSet<>();
			mFunMatch = determineMatcher(mEdge);
		}

		private Predicate<IASTNode> determineMatcher(final DecoratedWitnessEdge edge) {
			switch (edge.getConditional()) {
			case NONE:
				return this::matchNonConditional;
			case CONDITION_EVAL_FALSE:
				return a -> matchConditional(false, a);
			case CONDITION_EVAL_TRUE:
				return a -> matchConditional(true, a);
			case ARG_EVAL:
			case EXPR_EVAL:
			case FUNC_CALL:
			case PROC_CALL:
			case PROC_RETURN:
			default:
				throw new UnsupportedOperationException(
						"This conditional case was not yet considered: " + edge.getConditional());
			}
		}

		public void run(final IASTTranslationUnit translationUnit) {
			translationUnit.accept(this);
		}

		private Set<MatchedASTNode> getMatchedNodes() {
			return mMatchedNodes;
		}

		@Override
		protected int genericVisit(final IASTNode node) {
			if (mFunMatch.test(node)) {
				// skip the subtree if a match occurred, but continue with siblings.
				return PROCESS_SKIP;
			}
			return PROCESS_CONTINUE;
		}

		private boolean matchConditional(final boolean condition, final IASTNode node) {
			if (!matchLineNumber(node)) {
				return false;
			}
			final IASTStatement stmt;
			if (!(node instanceof IASTStatement)) {
				stmt = CdtASTUtils.getEnclosingStatement(node);
				if (stmt == null) {
					return false;
				}
			} else {
				stmt = (IASTStatement) node;
			}
			// we assume that node is a conditional and search for conditionals at this location
			final Set<IASTStatement> result;
			if (CdtASTUtils.isBranchingStatement(stmt)) {
				result = Collections.singleton(stmt);
			} else {
				result = CdtASTUtils.findDesiredType(node.getParent(), mConditionalTypes);
			}
			if (result.isEmpty()) {
				return false;
			}
			if (result.size() > 1) {
				mLogger.warn("Possible match is too ambiguous");
				return false;
			}

			final IASTStatement branchingSuccessor =
					CdtASTUtils.findBranchingSuccessorStatement(condition, result.iterator().next());
			if (branchingSuccessor == null) {
				return false;
			}
			mMatchedNodes.add(new MatchedASTNode(branchingSuccessor, mEdge));
			return true;
		}

		private boolean matchNonConditional(final IASTNode node) {
			if (matchLineNumber(node)) {
				mMatchedNodes.add(new MatchedASTNode(node, mEdge));
				return true;
			}
			return false;
		}

		private boolean matchLineNumber(final IASTNode node) {
			final IASTFileLocation loc = node.getFileLocation();
			if (loc == null) {
				return false;
			}

			return mEdge.getLineNumber() == loc.getEndingLineNumber() && mEdge.isIncoming()
					|| mEdge.getLineNumber() == loc.getStartingLineNumber() && !mEdge.isIncoming();
		}
	}

	private static final class DecoratedWitnessEdge implements IHasIncoming {
		private final WitnessEdge mEdge;
		private final WitnessEdgeAnnotation mAnnotation;
		private final boolean mIsIncoming;
		private final StepInfo mConditional;

		public DecoratedWitnessEdge(final WitnessEdge edge, final boolean isIncoming) {
			mIsIncoming = isIncoming;
			mEdge = edge;
			mAnnotation = WitnessEdgeAnnotation.getAnnotation(edge);
			mConditional = getConditionalFromAnnotation(mAnnotation);
		}

		private static StepInfo getConditionalFromAnnotation(final WitnessEdgeAnnotation annotation) {
			if (annotation == null || annotation.getCondition() == null) {
				return StepInfo.NONE;
			}
			if (annotation.getCondition()) {
				return StepInfo.CONDITION_EVAL_TRUE;
			}
			return StepInfo.CONDITION_EVAL_FALSE;
		}

		public StepInfo getConditional() {
			return mConditional;
		}

		public boolean hasNoLineNumber() {
			return getLineNumber() == -1;
		}

		@Override
		public boolean isIncoming() {
			return mIsIncoming;
		}

		public int getLineNumber() {
			if (mIsIncoming) {
				return mEdge.getLocation().getEndLine();
			}
			return mEdge.getLocation().getStartLine();
		}

		public boolean isEnteringLoop() {
			if (mAnnotation == null) {
				return false;
			}
			final Boolean val = mAnnotation.getEnterLoopHead();
			return val != null && val;
		}

		@Override
		public String toString() {
			return mEdge.toString() + " (inc=" + isIncoming() + ", isEnteringLoop=" + isEnteringLoop() + ")";
		}
	}

	private static final class DecoratedWitnessNode {
		private final WitnessNode mNode;
		private final WitnessNodeAnnotation mAnnotation;

		public DecoratedWitnessNode(final WitnessNode node) {
			mNode = node;
			mAnnotation = WitnessNodeAnnotation.getAnnotation(node);
		}

		public String getName() {
			return mNode.getName();
		}

		public String getInvariant() {
			return mAnnotation.getInvariant();
		}

		@Override
		public String toString() {
			return mNode.toString();
		}
	}

	private static final class MatchedASTNode implements IHasIncoming {
		private final IASTNode mNode;
		private final DecoratedWitnessEdge mEdge;

		private MatchedASTNode(final IASTNode node, final DecoratedWitnessEdge edge) {
			mNode = node;
			mEdge = edge;
		}

		private IASTNode getNode() {
			return mNode;
		}

		@Override
		public boolean isIncoming() {
			return mEdge.isIncoming();
		}

		public boolean isLoopHead() {
			return mEdge.isEnteringLoop() && isIncoming();
		}

		@Override
		public String toString() {
			return toStringSimple() + " " + mNode.getRawSignature();
		}

		public String toStringSimple() {
			return "Node: " + getLineNumberString() + " Edge: " + mEdge;
		}

		private String getLineNumberString() {
			final StringBuilder sb = new StringBuilder();
			sb.append("[L");
			sb.append(mNode.getFileLocation().getStartingLineNumber());
			if (mNode.getFileLocation().getStartingLineNumber() != mNode.getFileLocation().getEndingLineNumber()) {
				sb.append('-');
				sb.append(mNode.getFileLocation().getEndingLineNumber());
			}
			sb.append("]");
			return sb.toString();
		}
	}

	private interface IHasIncoming {
		boolean isIncoming();
	}
}
