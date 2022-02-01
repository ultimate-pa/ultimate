/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.cdt;

import org.eclipse.cdt.core.dom.ast.IASTComment;
import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIncludeStatement;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;

/**
 * Emulates the IASTFileLocation interface for comments to avoid calling
 * IASTComment.getFileLocation() unless necessary.
 */
class CommentHackAstFileLocation implements IASTFileLocation {
	private final int mOffset;
	private final int mLength;
	private final String mFilePath;
	private final ISourceDocument mSource;
	private final IASTComment mFallbackNode;
	
	public CommentHackAstFileLocation(final int offset, final int length, final String filePath,
			final ISourceDocument source, final IASTComment fallbackNode) {
		mOffset = offset;
		mLength = length;
		mFilePath = filePath;
		mSource = source;
		mFallbackNode = fallbackNode;
	}
	
	@Override
	public IASTFileLocation asFileLocation() {
		return this;
	}
	
	@Override
	public IASTPreprocessorIncludeStatement getContextInclusionStatement() {
		return mFallbackNode != null ? mFallbackNode.getFileLocation().getContextInclusionStatement() : null;
	}
	
	@Override
	public int getEndingLineNumber() {
		if (mSource != null) {
			return mSource.getLineNumber(mLength == 0 ? mOffset : (mOffset + mLength - 1));
		}
		return mFallbackNode != null ? mFallbackNode.getFileLocation().getEndingLineNumber() : 0;
	}
	
	@Override
	public String getFileName() {
		return mFilePath;
	}
	
	@Override
	public int getNodeLength() {
		return mLength;
	}
	
	@Override
	public int getNodeOffset() {
		return mOffset;
	}
	
	@Override
	public int getStartingLineNumber() {
		if (mSource != null) {
			return mSource.getLineNumber(mOffset);
		}
		return mFallbackNode != null ? mFallbackNode.getFileLocation().getStartingLineNumber() : 0;
	}
	
	@Override
	public String toString() {
		return getFileName() + "[" + mOffset + "," + (mOffset + mLength) + "]";
	}
}
