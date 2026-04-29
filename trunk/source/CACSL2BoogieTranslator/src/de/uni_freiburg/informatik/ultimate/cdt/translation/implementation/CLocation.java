/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation;

import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.cdt.translation.LineDirectiveMapping;
import de.uni_freiburg.informatik.ultimate.cdt.translation.LineOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.CdtASTUtils;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.MergedLocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class CLocation extends CACSLLocation {
	private static final long serialVersionUID = -7497131349540138810L;
	private final List<IASTNode> mNodes;
	private final LineDirectiveMapping mLineDirectiveMapping;
	private final LineOffsetComputer mLineOffsetComputer;

	protected CLocation(final IASTNode node, final boolean ignoreDuringBacktranslation,
			final LineDirectiveMapping lineDirectiveMapping, final LineOffsetComputer lineOffsetComputer) {
		this(node == null ? List.of() : List.of(node), ignoreDuringBacktranslation, lineDirectiveMapping,
				lineOffsetComputer);
	}

	private CLocation(final List<IASTNode> nodes, final boolean ignoreDuringBacktranslation,
			final LineDirectiveMapping lineDirectiveMapping, final LineOffsetComputer lineOffsetComputer) {
		super(ignoreDuringBacktranslation);
		mNodes = nodes;
		mLineDirectiveMapping = lineDirectiveMapping;
		mLineOffsetComputer = lineOffsetComputer;
	}

	private Pair<Integer, String> getOriginalLocation(final int lineInTu, final String filename) {
		if (mLineDirectiveMapping == null) {
			return new Pair<>(lineInTu, filename);
		}
		return mLineDirectiveMapping.getOriginal(lineInTu, filename);
	}

	private Stream<IASTFileLocation> getValidFileLocations() {
		return mNodes.stream().map(IASTNode::getFileLocation).filter(Objects::nonNull);
	}

	private static <T> T getUniqueElementOrNull(final Stream<T> stream) {
		return stream.collect(
				Collectors.collectingAndThen(Collectors.toSet(), x -> x.size() == 1 ? x.iterator().next() : null));
	}

	@Override
	public String getFileName() {
		return getUniqueElementOrNull(getValidFileLocations()
				.map(x -> getOriginalLocation(x.getStartingLineNumber(), x.getFileName()).getSecond()));
	}

	@Override
	public int getStartLine() {
		return getValidFileLocations()
				.mapToInt(x -> getOriginalLocation(x.getStartingLineNumber(), x.getFileName()).getFirst()).min()
				.orElse(-1);
	}

	@Override
	public int getEndLine() {
		return getValidFileLocations()
				.mapToInt(x -> getOriginalLocation(x.getEndingLineNumber(), x.getFileName()).getFirst()).max()
				.orElse(-1);
	}

	@Override
	public int getStartColumn() {
		final int startLine = getStartLine();
		if (mLineOffsetComputer == null || startLine == -1
				|| startLine != getValidFileLocations().mapToInt(x -> x.getStartingLineNumber()).min().getAsInt()) {
			// If the start line differs from the "actual" start line (i.e., there is a line directive at this
			// location), we don't return a column, since columns with line directives are not reliable.
			// The same holds, if we cannot compute the column (if there is no start line or no LineOffsetComputer).
			return -1;
		}
		final int lineOffset = mLineOffsetComputer.getOffset(startLine);
		// The offset starts with 0, but the column start with 1 (as specified by the SV-COMP)
		return getValidFileLocations().mapToInt(IASTFileLocation::getNodeOffset).min().getAsInt() - lineOffset + 1;
	}

	@Override
	public int getEndColumn() {
		final int endLine = getEndLine();
		if (mLineOffsetComputer == null || endLine == -1
				|| endLine != getValidFileLocations().mapToInt(x -> x.getEndingLineNumber()).max().getAsInt()) {
			// If the end line differs from the "actual" end line (i.e., there is a line directive at this
			// location), we don't return a column, since columns with line directives are not reliable.
			// The same holds, if we cannot compute the column (if there is no end line or no LineOffsetComputer).
			return -1;
		}
		final int lineOffset = mLineOffsetComputer.getOffset(endLine);
		// The offset starts with 0, but the column start with 1 (as specified by the SV-COMP)
		final var lastLoc = getValidFileLocations().max((Comparator.comparing(IASTFileLocation::getNodeOffset))).get();
		return lastLoc.getNodeOffset() + lastLoc.getNodeLength() - lineOffset + 1;
	}

	@Deprecated
	public IASTNode getNode() {
		// For compatibility we use the old behavior here: Find the common parent of all the nodes
		// (except for the translation unit itself)
		return CdtASTUtils.findCommonParent(mNodes.stream().filter(x -> !(x instanceof IASTTranslationUnit)).toList());
	}

	public LineDirectiveMapping getLineDirectiveMapping() {
		return mLineDirectiveMapping;
	}

	public LineOffsetComputer getLineOffsetComputer() {
		return mLineOffsetComputer;
	}

	@Override
	public String toString() {
		if (mNodes.isEmpty()) {
			return "";
		}
		final StringBuilder sb = new StringBuilder();
		sb.append("C: ").append(mNodes.stream().map(IASTNode::getRawSignature).toList());
		sb.append(" [");
		if (getStartLine() == getEndLine()) {
			sb.append(getStartLine());
		} else {
			sb.append(getStartLine());
			sb.append("-");
			sb.append(getEndLine());
		}
		sb.append("]");

		return sb.toString();
	}

	@Override
	public IAnnotations merge(final IAnnotations other) {
		if (other == null || this == other) {
			return this;
		}
		if (other instanceof CLocation) {
			final CLocation otherCloc = (CLocation) other;
			final boolean ignoreDuringBacktranslation =
					ignoreDuringBacktranslation() && otherCloc.ignoreDuringBacktranslation();
			LineDirectiveMapping resultLineDirectiveMapping;
			if (mLineDirectiveMapping == null) {
				resultLineDirectiveMapping = otherCloc.getLineDirectiveMapping();
			} else {
				resultLineDirectiveMapping = mLineDirectiveMapping;
			}
			final LineOffsetComputer resultLineOffsetComputer;
			if (mLineOffsetComputer == null) {
				resultLineOffsetComputer = otherCloc.getLineOffsetComputer();
			} else {
				resultLineOffsetComputer = mLineOffsetComputer;
			}
			final List<IASTNode> resultNodes = concatNodes(mNodes, otherCloc.mNodes);
			return new CLocation(resultNodes, ignoreDuringBacktranslation, resultLineDirectiveMapping,
					resultLineOffsetComputer);
		} else if (other instanceof ILocation) {
			return MergedLocation.mergeToMergeLocation(this, (ILocation) other);
		}
		throw new UnmergeableAnnotationsException(this, other);
	}

	private static List<IASTNode> concatNodes(final List<IASTNode> nodes1, final List<IASTNode> nodes2) {
		if (nodes2.isEmpty()) {
			return nodes1;
		}
		if (nodes1.isEmpty()) {
			return nodes2;
		}
		final Set<IASTNode> nodeSet1 = new HashSet<>(nodes1);
		final Set<IASTNode> nodeSet2 = new HashSet<>(nodes2);
		// Keep those nodes that are not duplicates and don't have any parent in the other list
		return Stream.concat(nodes1.stream().filter(x -> !hasParent(x, nodeSet2)),
				nodes2.stream().filter(x -> !nodeSet1.contains(x) && !hasParent(x, nodeSet1))).toList();
	}

	private static boolean hasParent(final IASTNode node, final Set<IASTNode> otherNodes) {
		for (IASTNode current = node.getParent(); current != null; current = current.getParent()) {
			if (otherNodes.contains(current)) {
				return true;
			}
		}
		return false;
	}

	@Override
	public String getFunction() {
		return getUniqueElementOrNull(mNodes.stream().map(x -> {
			final var scope = CdtASTUtils.findScope(x);
			if (scope == null) {
				// global scope
				return null;
			}
			return scope.getDeclarator().getName().toString();
		}));
	}

	/**
	 * Returns a location for the parent node of this.
	 */
	public CLocation getParent() {
		final IASTNode uniqueParent = getUniqueElementOrNull(mNodes.stream().map(IASTNode::getParent));
		if (uniqueParent == null) {
			return null;
		}
		return new CLocation(uniqueParent, ignoreDuringBacktranslation(), mLineDirectiveMapping, mLineOffsetComputer);
	}

	public CLocation createIgnoreCopy() {
		return new CLocation(mNodes, true, mLineDirectiveMapping, mLineOffsetComputer);
	}

	public CLocation copy() {
		return new CLocation(mNodes, ignoreDuringBacktranslation(), mLineDirectiveMapping, mLineOffsetComputer);
	}
}
