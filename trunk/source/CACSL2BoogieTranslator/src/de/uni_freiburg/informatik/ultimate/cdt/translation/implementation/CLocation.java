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

import java.util.Collection;
import java.util.HashSet;

import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.cdt.translation.LineDirectiveMapping;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.CdtASTUtils;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.MergedLocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;

public class CLocation extends CACSLLocation {

	private static final long serialVersionUID = -7497131349540138810L;
	private final IASTNode mNode;
	private final LineDirectiveMapping mLineDirectiveMapping;

	protected CLocation(final IASTNode node, final Check checkedSpec, final boolean ignoreDuringBacktranslation,
			final LineDirectiveMapping lineDirectiveMapping) {
		super(checkedSpec, ignoreDuringBacktranslation);
		mNode = node;
		mLineDirectiveMapping = lineDirectiveMapping;
	}

	@Override
	public String getFileName() {
		if (mNode != null) {
			if (mLineDirectiveMapping == null) {
				return mNode.getFileLocation().getFileName();
			}
			final int currentLineNumber = mNode.getFileLocation().getStartingLineNumber();
			final String currentFilename = mNode.getFileLocation().getFileName();
			return mLineDirectiveMapping.getOriginal(currentLineNumber, currentFilename).getSecond();
		}
		return null;
	}

	@Override
	public int getStartLine() {
		if (mNode != null) {
			if (mLineDirectiveMapping == null) {
				return mNode.getFileLocation().getStartingLineNumber();
			}
			final int currentLineNumber = mNode.getFileLocation().getStartingLineNumber();
			final String currentFilename = mNode.getFileLocation().getFileName();
			return mLineDirectiveMapping.getOriginal(currentLineNumber, currentFilename).getFirst();
		}
		return -1;
	}

	@Override
	public int getEndLine() {
		if (mNode != null) {
			if (mLineDirectiveMapping == null) {
				return mNode.getFileLocation().getEndingLineNumber();
			}
			final int currentLineNumber = mNode.getFileLocation().getEndingLineNumber();
			final String currentFilename = mNode.getFileLocation().getFileName();
			return mLineDirectiveMapping.getOriginal(currentLineNumber, currentFilename).getFirst();
		}
		return -1;
	}

	@Override
	public int getStartColumn() {
		return -1;
	}

	@Override
	public int getEndColumn() {
		return -1;
	}

	public IASTNode getNode() {
		return mNode;
	}

	public LineDirectiveMapping getLineDirectiveMapping() {
		return mLineDirectiveMapping;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		if (mNode != null) {
			sb.append("C: ");
			sb.append(mNode.getRawSignature());
			sb.append(" [");
			if (getStartLine() == getEndLine()) {
				sb.append(getStartLine());
			} else {
				sb.append(getStartLine());
				sb.append("-");
				sb.append(getEndLine());
			}
			sb.append("]");
		}

		return sb.toString();
	}

	@Override
	public IAnnotations merge(final IAnnotations other) {
		if (other == null) {
			return this;
		}
		if (other instanceof CLocation) {
			final CLocation otherCloc = (CLocation) other;
			final Check mergedCheck = Check.mergeCheck(getCheck(), otherCloc.getCheck());
			final boolean ignoreDuringBacktranslation =
					ignoreDuringBacktranslation() && otherCloc.ignoreDuringBacktranslation();
			final IASTNode node = getMergedNode(otherCloc);
			LineDirectiveMapping resultLineDirectiveMapping;
			if (mLineDirectiveMapping == null) {
				resultLineDirectiveMapping = otherCloc.getLineDirectiveMapping();
			} else {
				resultLineDirectiveMapping = mLineDirectiveMapping;
			}
			return new CLocation(node, mergedCheck, ignoreDuringBacktranslation, resultLineDirectiveMapping);
		} else if (other instanceof ILocation) {
			return MergedLocation.mergeToMergeLocation(this, (ILocation) other);
		}
		throw new UnmergeableAnnotationsException(this, other);
	}

	private IASTNode getMergedNode(final CLocation otherCloc) {
		final IASTNode otherNode = otherCloc.getNode();
		final IASTNode myNode = getNode();
		if (myNode == null && otherNode == null) {
			return null;
		}
		if (myNode == null) {
			return otherNode;
		} else if (otherNode == null) {
			return myNode;
		} else {
			// we have two nodes and want to merge them; if one of both is a translation unit, we take the other
			// one. If both are not translation units, we try to find a common parent
			if (myNode instanceof IASTTranslationUnit) {
				return otherNode;
			} else if (otherNode instanceof IASTTranslationUnit) {
				return myNode;
			} else {
				final Collection<IASTNode> nodes = new HashSet<>();
				nodes.add(myNode);
				nodes.add(otherNode);
				return CdtASTUtils.findCommonParent(nodes);
			}
		}
	}

}
