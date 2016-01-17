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
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import org.apache.log4j.Logger;
import org.eclipse.cdt.core.dom.ast.ASTGenericVisitor;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
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
public class TrueWitnessExtractor {

	private final IUltimateServiceProvider mServices;
	private final Logger mLogger;
	private WitnessNode mWitnessNode;
	private IASTTranslationUnit mTranslationUnit;
	private Pair<Map<IASTNode, String>, Map<IASTNode, String>> mAST2Invariant;

	public TrueWitnessExtractor(final IUltimateServiceProvider service) {
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

		while (!worklist.isEmpty()) {
			final WitnessNode current = worklist.remove();
			if (!closed.add(current)) {
				continue;
			}
			worklist.addAll(current.getOutgoingNodes());
			extractNode(current, rtr);
		}

		printDebug(rtr);

		return rtr;
	}

	private void printDebug(final Pair<Map<IASTNode, String>, Map<IASTNode, String>> rtr) {
		mLogger.info("Found the following invariants in the witness");
		final Map<IASTNode, String> before = rtr.getFirst();
		final Map<IASTNode, String> after = rtr.getSecond();
		if (before.isEmpty() && after.isEmpty()) {
			mLogger.info("No invariants found except invariant=true");
			return;
		}
		for (final Entry<IASTNode, String> entry : before.entrySet()) {
			mLogger.info("Before " + entry.getKey().getRawSignature() + " invariant is " + entry.getValue());
		}
		for (final Entry<IASTNode, String> entry : after.entrySet()) {
			mLogger.info("After " + entry.getKey().getRawSignature() + " invariant is " + entry.getValue());
		}
	}

	private void extractNode(final WitnessNode current, final Pair<Map<IASTNode, String>, Map<IASTNode, String>> rtr) {
		final WitnessNodeAnnotation annot = WitnessNodeAnnotation.getAnnotation(current);
		if (annot == null) {
			return;
		}
		final String invariant = annot.getInvariant();
		if (invariant == null || invariant.equalsIgnoreCase("true")) {
			return;
		}
		final Pair<List<IASTNode>, List<IASTNode>> nodes = matchASTNodes(current);
		if (nodes == null) {
			mLogger.error("Could not match witness node to AST node: " + current);
		}
		for (final IASTNode node : nodes.getFirst()) {
			addInvariants(rtr.getFirst(), invariant, node);
		}
		for (final IASTNode node : nodes.getSecond()) {
			addInvariants(rtr.getSecond(), invariant, node);
		}
	}

	private void addInvariants(final Map<IASTNode, String> rtr, final String invariant, final IASTNode node) {
		final String oldInvariant = rtr.put(node, invariant);
		if (oldInvariant != null) {
			final String newInvariant = invariant + " || " + oldInvariant;
			mLogger.warn("Multiple witness invariants matched for the same node, merging to " + newInvariant);
			rtr.put(node, newInvariant);
		}
	}

	private Pair<List<IASTNode>, List<IASTNode>> matchASTNodes(final WitnessNode current) {
		final Set<Integer> afterLines = current.getIncomingEdges().stream().map(a -> a.getLocation().getEndLine())
				.collect(Collectors.toSet());
		final Set<Integer> beforeLines = current.getOutgoingEdges().stream().map(a -> a.getLocation().getStartLine())
				.collect(Collectors.toSet());

		// remove the line number that is used for "no line number"
		afterLines.remove(-1);
		beforeLines.remove(-1);

		if (afterLines.size() == 0 && beforeLines.size() == 0) {
			mLogger.error("No line numbers found for " + current);
			return null;
		}
		if (afterLines.size() > 1) {
			mLogger.warn("Multiple line numbers found after " + current + ": " + toStringCollection(afterLines));
		}
		if (beforeLines.size() > 1) {
			mLogger.warn("Multiple line numbers found before " + current + ": " + toStringCollection(beforeLines));
		}

		final LineMatchingVisitor matcher = new LineMatchingVisitor(beforeLines, afterLines);
		mTranslationUnit.accept(matcher);

		final Pair<List<IASTNode>, List<IASTNode>> matchedNodes = matcher.getMatchedNodes();
		if (matchedNodes.getFirst().isEmpty()) {
			mLogger.warn("Could not match AST node to invariant for witness lines " + toStringCollection(beforeLines));
		}
		if (matchedNodes.getSecond().isEmpty()) {
			mLogger.warn("Could not match AST node to invariant for witness lines " + toStringCollection(afterLines));
		}

		return matchedNodes;
	}

	private String toStringCollection(final Collection<?> lines) {
		return String.join(",", lines.stream().map(a -> String.valueOf(a)).collect(Collectors.toList()));
	}

	private final class LineMatchingVisitor extends ASTGenericVisitor {

		private final Set<Integer> mBeforeLines;
		private final Set<Integer> mAfterLines;
		private final Pair<List<IASTNode>, List<IASTNode>> mMatchedNodes;

		public LineMatchingVisitor(final Set<Integer> beforeLines, Set<Integer> afterLines) {
			super(true);
			mBeforeLines = beforeLines;
			mAfterLines = afterLines;
			mMatchedNodes = new Pair<List<IASTNode>, List<IASTNode>>(new ArrayList<>(), new ArrayList<>());
		}

		private Pair<List<IASTNode>, List<IASTNode>> getMatchedNodes() {
			return mMatchedNodes;
		}

		@Override
		public int visit(IASTDeclaration declaration) {
			match(declaration);
			return super.visit(declaration);
		}

		@Override
		public int visit(IASTStatement statement) {
			match(statement);
			return super.visit(statement);
		}

		private void match(IASTNode node) {
			final IASTFileLocation loc = node.getFileLocation();
			final int startLine = loc.getStartingLineNumber();
			final int endLine = loc.getEndingLineNumber();

			if (mBeforeLines.contains(startLine)) {
				mMatchedNodes.getFirst().add(node);
			}
			if (mAfterLines.contains(endLine)) {
				mMatchedNodes.getSecond().add(node);
			}
		}
	}

}
