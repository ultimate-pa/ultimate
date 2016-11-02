package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.cdt;

import org.eclipse.cdt.core.dom.ast.IASTComment;
import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIncludeStatement;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;

/**
 * Emulates the IASTFileLocation interface for comments to avoid calling
 * IASTComment.getFileLocation() unless necessary.
 *
 */
class CommentHackASTFileLocation implements IASTFileLocation {
	private final int mOffset;
	private final int mLength;
	private final String mFilePath;
	private final ISourceDocument mSource;
	private final IASTComment mFallbackNode;

	public CommentHackASTFileLocation(final int offset, final int length, final String filePath,
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
